#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include <vector>
#include <algorithm>
#include <queue>
#include <unordered_map>
#include <cstdint>
#include <iostream>
#include "llvm/Transforms/Utils/CodeMotion.h"
using namespace llvm;

namespace {
  int adjacent_loop_same_tripcount = 0;
  int nonadjacent_loop_same_tripcount = 0;
  int sink_loop_same_tripcount = 0;
  int hoist_loop_same_tripcount = 0;
  int adjacent_loop_diff_tripcount = 0;
  int nonadjacent_loop_diff_tripcount = 0;
  int sink_loop_diff_tripcount = 0;
  int hoist_loop_diff_tripcount = 0;

  // Returns true if the instruction \p I can be hoisted to the end of the
  // preheader of \p FC0. \p SafeToHoist contains the instructions that are
  // known to be safe to hoist. The instructions encountered that cannot be
  // hoisted are in \p NotHoisting.
  // TODO: Move functionality into CodeMoverUtils
  bool canHoistInst(Instruction &I,
                    const SmallVector<Instruction *, 4> &SafeToHoist,
                    const SmallVector<Instruction *, 4> &NotHoisting,
                    const Loop &Aloop,
                    const SmallVector<Instruction *, 16> &AMemReads,
                    const SmallVector<Instruction *, 16> &AMemWrites,
                    DependenceInfo &DI, DominatorTree &DT){
    const BasicBlock *AloopPreheader = Aloop.getLoopPreheader()->getSingleSuccessor();
    assert(AloopPreheader &&
           "Expected single successor for loop preheader.");
 
    for (Use &Op : I.operands()) {
      if (auto *OpInst = dyn_cast<Instruction>(Op)) {
        bool OpHoisted = is_contained(SafeToHoist, OpInst);
        // Check if we have already decided to hoist this operand. In this
        // case, it does not dominate FC0 *yet*, but will after we hoist it.
        if (!(OpHoisted || DT.dominates(OpInst, AloopPreheader))) {
          return false;
        }
      }
    }
 
    // PHIs in FC1's header only have FC0 blocks as predecessors. PHIs
    // cannot be hoisted and should be sunk to the exit of the fused loop.
    if (isa<PHINode>(I))
      return false;
 
    // If this isn't a memory inst, hoisting is safe
    if (!I.mayReadOrWriteMemory())
      return true;
 
    // outs() << "Checking if this mem inst can be hoisted.\n";
    for (Instruction *NotHoistedInst : NotHoisting) {
      if (auto D = DI.depends(&I, NotHoistedInst, true)) {
        // Dependency is not read-before-write, write-before-read or
        // write-before-write
        if (D->isFlow() || D->isAnti() || D->isOutput()) {
          // outs() << "Inst depends on an instruction in FC1's "
                              //  "preheader that is not being hoisted.\n";
          return false;
        }
      }
    }
 
    for (Instruction *ReadInst : AMemReads) {
      if (auto D = DI.depends(ReadInst, &I, true)) {
        // Dependency is not read-before-write
        if (D->isAnti()) {
          // outs() << "Inst depends on a read instruction in FC0.\n";
          return false;
        }
      }
    }
 
    for (Instruction *WriteInst : AMemWrites) {
      if (auto D = DI.depends(WriteInst, &I, true)) {
        // Dependency is not write-before-read or write-before-write
        if (D->isFlow() || D->isOutput()) {
          // outs() << "Inst depends on a write instruction in FC0.\n";
          return false;
        }
      }
    }
    return true;
  }

  // Returns true if the instruction \p I can be sunk to the top of the exit
  // block of \p FC1.
  // TODO: Move functionality into CodeMoverUtils
  bool canSinkInst(Instruction &I, const Loop &Bloop,
  const SmallVector<Instruction *, 16> &BMemReads,
  const SmallVector<Instruction *, 16> &BMemWrites,
  DependenceInfo &DI) {
    for (User *U : I.users()) {
      if (auto *UI{dyn_cast<Instruction>(U)}) {
        // Cannot sink if user in loop
        // If FC1 has phi users of this value, we cannot sink it into FC1.
        if (Bloop.contains(UI)) {
          // Cannot hoist or sink this instruction. No hoisting/sinking
          // should take place, loops should not fuse
          return false;
        }
      }
    }
 
    // If this isn't a memory inst, sinking is safe
    if (!I.mayReadOrWriteMemory())
      return true;
 
    for (Instruction *ReadInst : BMemReads) {
      if (auto D = DI.depends(&I, ReadInst, true)) {
        // Dependency is not write-before-read
        if (D->isFlow()) {
          // outs() << "Inst depends on a read instruction in FC1.\n";
          return false;
        }
      }
    }
 
    for (Instruction *WriteInst : BMemWrites) {
      if (auto D = DI.depends(&I, WriteInst, true)) {
        // Dependency is not write-before-write or read-before-write
        if (D->isOutput() || D->isAnti()) {
          // outs() << "Inst depends on a write instruction in FC1.\n";
          return false;
        }
      }
    }
 
    return true;
  }

  bool collectMovablePreheaderInsts(
    const Loop &Aloop, const Loop &Bloop,
    SmallVector<Instruction *, 4> &SafeToHoist,
    SmallVector<Instruction *, 4> &SafeToSink,
    SmallVector<Instruction *, 16> &AMemReads,
    SmallVector<Instruction *, 16> &AMemWrites,
    SmallVector<Instruction *, 16> &BMemReads,
    SmallVector<Instruction *, 16> &BMemWrites,
    DependenceInfo &DI, DominatorTree &DT){
      BasicBlock *AExitBlock = Aloop.getExitBlock();
      SmallVector<Instruction *, 4> NotHoisting;
      for(Instruction &I : *AExitBlock){
        if(&I == AExitBlock->getTerminator()){
          continue;
        }
        // If the instruction has side-effects, give up.
        // TODO: The case of mayReadFromMemory we can handle but requires
        // additional work with a dependence analysis so for now we give
        // up on memory reads.
        if (I.mayThrow() || !I.willReturn()) {
          // outs() << "Inst: " << I << " may throw or won't return.\n";
          return false;
        }
        // outs() << "Checking Inst: " << I << "\n";
        if (I.isAtomic() || I.isVolatile()) {
          // outs() << "\tInstruction is volatile or atomic. Cannot move it.\n";
          return false;
        }
        if (canHoistInst(I, SafeToHoist, NotHoisting, Aloop, AMemReads, AMemWrites, DI, DT)) {
          SafeToHoist.push_back(&I);
          // outs() << "Safe to hoist.\n";
        } else {
          // outs() << "\tCould not hoist. Trying to sink...\n";
          NotHoisting.push_back(&I);
          if (canSinkInst(I, Bloop, BMemReads, BMemWrites, DI)) {
            SafeToSink.push_back(&I);
            // outs() << "\tSafe to sink.\n";
          } else {
            // outs() << "\tCould not sink.\n";
            return false;
          }
        }
      }
      // outs() << "All preheader instructions could be sunk or hoisted!\n";
      return true;
    }

  // split the preheader
  void splitPreheader(Loop &loop, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
    BasicBlock *preheader = loop.getLoopPreheader();
    BasicBlock *header = loop.getHeader();
    BasicBlock *aftersplit;
    if(PHINode *phinode = dyn_cast<PHINode>(&(header->front()))){
      // // outs() << "Preheader: " << header->front() << "\n";
      Instruction *end = preheader->getTerminator();
      aftersplit = preheader->splitBasicBlock(end, "Preheader");
    }
    // update the dominate tree
    DT.recalculate(F);
    PDT.recalculate(F);
  }

  // merge the preheader
  void mergePreheader(Loop &loop, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
    BasicBlock *preheader = loop.getLoopPreheader();
    BasicBlock *header = loop.getHeader();
    if(preheader->size() == 1){
      BasicBlock *preheader_succ = preheader->getTerminator()->getSuccessor(0);
      if(header != preheader_succ){
        // outs() << "header != preheader_succ\n";
        return;
      }
      BasicBlock *preheader_pred = preheader->getUniquePredecessor();
      if(!preheader_pred){
        return;
      }
      Instruction *pred_term = preheader_pred->getTerminator();
      int pred_term_index = -1;
      for(int i=0; i<pred_term->getNumSuccessors(); i++){
        if(pred_term->getSuccessor(i) == preheader){
          pred_term_index = i;
          break;
        }
      }
      if(pred_term_index < 0){
        return;
      }
      pred_term->setSuccessor(pred_term_index, preheader_succ);
      header->replacePhiUsesWith(preheader, preheader_pred);
      preheader->eraseFromParent();
    }
    DT.recalculate(F);
    PDT.recalculate(F);
    return;
  }

  void splitExitBlock(Loop &loop, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
    BasicBlock *exitblock = loop.getExitBlock();
    BasicBlock *header = loop.getHeader();
    BasicBlock *aftersplit;
    Instruction *begin = &(exitblock->front());
    aftersplit = exitblock->splitBasicBlock(begin, "ExitBlock");
    // update the dominate tree
    DT.recalculate(F);
    PDT.recalculate(F);
  }

  /// Rewrite all additive recurrences in a SCEV to use a new loop.
  class AddRecLoopReplacer : public SCEVRewriteVisitor<AddRecLoopReplacer> {
  public:
    AddRecLoopReplacer(ScalarEvolution &SE, const Loop &OldL, const Loop &NewL,
                       bool UseMax = true)
        : SCEVRewriteVisitor(SE), Valid(true), UseMax(UseMax), OldL(OldL),
          NewL(NewL) {}

    const SCEV *visitAddRecExpr(const SCEVAddRecExpr *Expr) {
      const Loop *ExprL = Expr->getLoop();
      SmallVector<const SCEV *, 2> Operands;
      if (ExprL == &OldL) {
        append_range(Operands, Expr->operands());
        return SE.getAddRecExpr(Operands, &NewL, Expr->getNoWrapFlags());
      }

      if (OldL.contains(ExprL)) {
        bool Pos = SE.isKnownPositive(Expr->getStepRecurrence(SE));
        if (!UseMax || !Pos || !Expr->isAffine()) {
          Valid = false;
          return Expr;
        }
        return visit(Expr->getStart());
      }

      for (const SCEV *Op : Expr->operands())
        Operands.push_back(visit(Op));
      return SE.getAddRecExpr(Operands, ExprL, Expr->getNoWrapFlags());
    }

    bool wasValidSCEV() const { return Valid; }

  private:
    bool Valid, UseMax;
    const Loop &OldL, &NewL;
  };

  /// Return false if the access functions of \p I0 and \p I1 could cause
  /// a negative dependence.
  bool accessDiffIsPositive(const Loop &Aloop, const Loop &Bloop, Instruction &I0, Instruction &I1,
    bool EqualIsInvalid, ScalarEvolution &SE, DominatorTree &DT) {
      // // outs() << "accessDiffIsPositive\n";
      Value *Ptr0 = getLoadStorePointerOperand(&I0);
      Value *Ptr1 = getLoadStorePointerOperand(&I1);
      if (!Ptr0 || !Ptr1)
        return false;

      const SCEV *SCEVPtr0 = SE.getSCEVAtScope(Ptr0, &Aloop);
      const SCEV *SCEVPtr1 = SE.getSCEVAtScope(Ptr1, &Bloop);

      AddRecLoopReplacer Rewriter(SE, Aloop, Bloop);
      SCEVPtr0 = Rewriter.visit(SCEVPtr0);

      if (!Rewriter.wasValidSCEV())
        return false;

      // TODO: isKnownPredicate doesnt work well when one SCEV is loop carried (by
      //       L0) and the other is not. We could check if it is monotone and test
      //       the beginning and end value instead.

      BasicBlock *L0Header = Aloop.getHeader();
      auto HasNonLinearDominanceRelation = [&](const SCEV *S) {
        const SCEVAddRecExpr *AddRec = dyn_cast<SCEVAddRecExpr>(S);
        if (!AddRec)
          return false;
        return !DT.dominates(L0Header, AddRec->getLoop()->getHeader()) &&
              !DT.dominates(AddRec->getLoop()->getHeader(), L0Header);
      };
      if (SCEVExprContains(SCEVPtr1, HasNonLinearDominanceRelation))
        return false;

      ICmpInst::Predicate Pred =
          EqualIsInvalid ? ICmpInst::ICMP_SGT : ICmpInst::ICMP_SGE;
      bool IsAlwaysGE = SE.isKnownPredicate(Pred, SCEVPtr0, SCEVPtr1);
    // // outs() << "accessDiffIsPositive: " << IsAlwaysGE << "\n";
    return IsAlwaysGE;
  }
  // DepChoice = 0 : FUSION_DEPENDENCE_ANALYSIS_SCEV
  // DepChoice = 1 : FUSION_DEPENDENCE_ANALYSIS_DA
  // DepChoice = 2 : FUSION_DEPENDENCE_ANALYSIS_ALL
  bool dependencesAllowFusion(const Loop &Aloop, const Loop &Bloop, Instruction &I0, Instruction &I1,
    bool AnyDep, int DepChoice, DependenceInfo &DI,
    SmallVector<Instruction *, 16> ALoopMemReads, SmallVector<Instruction *, 16> ALoopMemWrites,
    SmallVector<Instruction *, 16> BLoopMemReads, SmallVector<Instruction *, 16> BLoopMemWrites,
    ScalarEvolution &SE, DominatorTree &DT){
    // // outs() << "DepChoice = " << DepChoice << "\n";
    switch (DepChoice) {
      case 0:
        return accessDiffIsPositive(Aloop, Bloop, I0, I1, AnyDep, SE, DT);
      case 1:
        {
          auto DepResult = DI.depends(&I0, &I1, true);
          if (!DepResult){
            // // outs() << "There is no data dependence\n";
            return true;
          }
          // // outs() << "There exist data dependence\n";
          return false;
        }
      case 2:
        return dependencesAllowFusion(Aloop, Bloop, I0, I1, AnyDep, 0, DI,
          ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT) ||
             dependencesAllowFusion(Aloop, Bloop, I0, I1, AnyDep, 1, DI,
             ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT);
      default:
        return dependencesAllowFusion(Aloop, Bloop, I0, I1, AnyDep, 0, DI,
          ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT) ||
             dependencesAllowFusion(Aloop, Bloop, I0, I1, AnyDep, 1, DI,
             ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT) ;
    }
  }
  /// Perform a dependence check and return if @p FC0 and @p FC1 can be fused.
  bool dependencesAllowFusion(const Loop &Aloop, const Loop &Bloop, DependenceInfo &DI,
    SmallVector<Instruction *, 16> ALoopMemReads, SmallVector<Instruction *, 16> ALoopMemWrites,
    SmallVector<Instruction *, 16> BLoopMemReads, SmallVector<Instruction *, 16> BLoopMemWrites,
    ScalarEvolution &SE, DominatorTree &DT){
    // // outs() << "Check if " << Aloop << " can be fused with " << Bloop << "\n";
    // outs() << *(Aloop.getHeader());
    // outs() << *(Bloop.getHeader());
    assert(Aloop.getLoopDepth() == Bloop.getLoopDepth());
    // assert(DT.dominates(Aloop.getEntryBlock(), Bloop.getEntryBlock()));
    int FusionDependenceAnalysis = 2;
    for (Instruction *WriteL0 : ALoopMemWrites) {
      for (Instruction *WriteL1 : BLoopMemWrites)
        if (!dependencesAllowFusion(Aloop, Bloop, *WriteL0, *WriteL1,
          /* AnyDep */ false, FusionDependenceAnalysis, DI, 
          ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT)) {
          // // outs() << "In Aloopwrite :write !dependencesAllowFusion\n";
          // // outs() << "Aloopwrite: "<< *WriteL0 << "\n" << "Bloopwrite: " << *WriteL1 << "\n";
          return false;
        }
      for (Instruction *ReadL1 : BLoopMemReads)
        if (!dependencesAllowFusion(Aloop, Bloop, *WriteL0, *ReadL1,
          /* AnyDep */ false, FusionDependenceAnalysis, DI,
          ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT)) {
          // // outs() << "In Aloopwrite :read !dependencesAllowFusion\n";
          return false;
        }
    }

    for (Instruction *WriteL1 : BLoopMemWrites) {
      for (Instruction *WriteL0 : ALoopMemWrites)
        if (!dependencesAllowFusion(Aloop, Bloop, *WriteL0, *WriteL1,
          /* AnyDep */ false, FusionDependenceAnalysis, DI,
          ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT)) {
          // // outs() << "In Bloopwrite :write !dependencesAllowFusion\n";
          return false;
        }
      for (Instruction *ReadL0 : ALoopMemReads)
        if (!dependencesAllowFusion(Aloop, Bloop, *ReadL0, *WriteL1,
          /* AnyDep */ false, FusionDependenceAnalysis, DI,
          ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT)) {
          // // outs() << "In Bloopwrite :read !dependencesAllowFusion\n";
          return false;
        }
    }

    // // Walk through all uses in FC1. For each use, find the reaching def. If the
    // // def is located in FC0 then it is is not safe to fuse.
    for (BasicBlock *BB : Bloop.blocks())
      for (Instruction &I : *BB)
        for (auto &Op : I.operands())
          if (Instruction *Def = dyn_cast<Instruction>(Op))
            if (Aloop.contains(Def->getParent())) {
              // outs() << "InvalidDependencies\n";
              return false;
            }

    return true;
  }

  bool isValidLoop(Loop *L){
    BasicBlock *Latch = L->getLoopLatch();
    BasicBlock *ExitBlock = L->getExitBlock();
    if(!Latch || !ExitBlock){
      return false;
    }
    for(BasicBlock *BB : L->blocks()){
      if(BB -> hasAddressTaken()){
        return false;
      }
      for(Instruction &I : *BB){
        if(I.mayThrow()){
          return false;;
        }
        if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
          if (SI->isVolatile()) {
            return false;
          }
        }
        if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
          if (LI->isVolatile()) {
            return false;
          }
        }
      }
    }
    return true;
  }

  bool canMoveUp(Instruction &I,
    const SmallVector<Instruction *, 4> &SafeToMoveUp,
    const Loop &loop,
    const SmallVector<Instruction *, 16> &MemReads,
    const SmallVector<Instruction *, 16> &MemWrites,
    SmallVector<BasicBlock*, 16> &Move_Up_BB,
    DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT,
    SmallVector<BasicBlock*, 16> All_Check_BB){
      const BasicBlock *Preheader = loop.getLoopPreheader()->getSingleSuccessor();
      // for(BasicBlock *BB : All_Check_BB){
      //   outs() << *BB;
      // }
      assert(Preheader && "Expected single successor for loop preheader.");
      for (Use &Op : I.operands()) {
        // // outs() << "oeprands: " << *Op << "\n";
        if (auto *OpInst = dyn_cast<Instruction>(Op)) {
          bool OpHoisted = is_contained(SafeToMoveUp, OpInst);
          if (!(OpHoisted || DT.dominates(OpInst, Preheader) || is_contained(All_Check_BB, OpInst->getParent()))) {

            // outs() << "CHECK: " << I << "\n";
            // outs() << "CHECK OpInst: " << *OpInst << "\ncannot be move up" << "\n";
              return false;
            // outs() << "pass the CHECK " << *OpInst  << "\n";
            // return false;
          }
        }
      }
      if (isa<PHINode>(I)) {
        PHINode* phinode = dyn_cast<PHINode>(&I);
        // // outs() << "check phinode: " << *phinode << "\n";
        for (int i=0; i<phinode->getNumIncomingValues(); i++) {
          if(!is_contained(All_Check_BB, phinode->getIncomingBlock(i))){
            return false;
          }
        }
        // // outs() << "passed\n";
      }


      // If this isn't a memory inst, hoisting is safe
      if (!I.mayReadOrWriteMemory()){
        return true;
      }

      for (Instruction *ReadInst : MemReads) {
        if (auto D = DI.depends(ReadInst, &I, true)) {
          // Dependency is not read-before-write
          if (D->isAnti()) {
            // outs() << "Inst depends on a read instruction in FC0, cannot move up\n";
            return false;
          }
        }
      }
 
      for (Instruction *WriteInst : MemWrites) {
        if (auto D = DI.depends(WriteInst, &I, true)) {
          // Dependency is not write-before-read or write-before-write
          if (D->isFlow() || D->isOutput()) {
            // outs() << "Inst depends on a write instruction in FC0, cannot move up\n";
            return false;
          }
        }
      }
      return true;
  }

  bool BB_dependent_on_firstloop(BasicBlock* current_BB, const Loop &loop,
    SmallVector<Instruction *, 16> &MemReads,
    SmallVector<Instruction *, 16> &MemWrites,
    SmallVector<BasicBlock*, 16> &Move_Up_BB,
    SmallVector<Instruction *, 4> &SafeToMoveUp,
    DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT,
    SmallVector<BasicBlock*, 16> All_Check_BB){
      for(Instruction &I : *current_BB){
        if(&I == current_BB->getTerminator()){
          continue;
        }
        if (I.mayThrow() || !I.willReturn()) {
          // outs() << "Inst: " << I << " may throw or won't return.\n";
          return true;
        }
        if (I.isAtomic() || I.isVolatile()) {
          // outs() << "\tInstruction is volatile or atomic. Cannot move it.\n";
          return true;
        }
        if (canMoveUp(I, SafeToMoveUp, loop, MemReads, MemWrites, Move_Up_BB, DI, DT, PDT, All_Check_BB)) {
          SafeToMoveUp.push_back(&I);
          // // outs() << "push_back " << I << "\n";
        }
        else{
          return true;
        }
      }
      // outs() << *current_BB << "save to move up\n";
      return false;
  }

  bool canMoveDown(Instruction &I,
    const SmallVector<Instruction *, 4> &SafeToMoveDown,
    const Loop &loop,
    const SmallVector<Instruction *, 16> &MemReads,
    const SmallVector<Instruction *, 16> &MemWrites,
    SmallVector<BasicBlock*, 16> &Move_Down_BB,
    DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT){
      // // outs() << "CHECK: " << I << "\n";
      for (User *U : I.users()) {
        if (auto *UI{dyn_cast<Instruction>(U)}) {
          if (loop.contains(UI)) {
            // outs() << "loop conatins " << *UI << "\n";
            return false;
          }
        }
      }
  
      // If this isn't a memory inst, sinking is safe
      if (!I.mayReadOrWriteMemory())
        return true;
  
      for (Instruction *ReadInst : MemReads) {
        if (auto D = DI.depends(&I, ReadInst, true)) {
          // Dependency is not write-before-read
          if (D->isFlow()) {
            // outs() << "Inst depends on a read instruction in FC1, cannot move down\n";
            return false;
          }
        }
      }
  
      for (Instruction *WriteInst : MemWrites) {
        if (auto D = DI.depends(&I, WriteInst, true)) {
          // Dependency is not write-before-write or read-before-write
          if (D->isOutput() || D->isAnti()) {
            // outs() << "Inst depends on a write instruction in FC1, cannot move down\n";
            return false;
          }
        }
      }
      return true;
  }

  bool BB_dependent_on_secondloop(BasicBlock* current_BB, const Loop &loop,
    SmallVector<Instruction *, 16> &MemReads,
    SmallVector<Instruction *, 16> &MemWrites,
    SmallVector<BasicBlock*, 16> &Move_Down_BB,
    SmallVector<Instruction *, 4> &SafeToMoveDown,
    DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT){
      for(Instruction &I : *current_BB){
        if(&I == current_BB->getTerminator()){
          continue;
        }
        if (I.mayThrow() || !I.willReturn()) {
          // outs() << "Inst: " << I << " may throw or won't return.\n";
          return true;
        }
        if (I.isAtomic() || I.isVolatile()) {
          // outs() << "\tInstruction is volatile or atomic. Cannot move it.\n";
          return true;
        }
        if (canMoveDown(I, SafeToMoveDown, loop, MemReads, MemWrites, Move_Down_BB, DI, DT, PDT)) {
          SafeToMoveDown.push_back(&I);
          // // outs() << "push_back " << I << "\n";
        }
        else{
          return true;
        }
      }
      // // outs() << *current_BB << "save to move down\n";
      return false;
  }

  void move_intervening_code_up(const Loop &Aloop, const Loop &Bloop, SmallVector<BasicBlock*, 16> &Move_Up_BB, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
    // move the intervening code up to the end of preheader of first loop
    // outs() << "Can move up\n";

    BasicBlock *AHeader = Aloop.getHeader();
    BasicBlock *APreheader = Aloop.getLoopPreheader();
    BasicBlock *AExitBlock = Aloop.getExitBlock();
    BasicBlock *BPreheader = Bloop.getLoopPreheader();
    Instruction *AHeaderterm = AHeader->getTerminator();
    Instruction *Last_Move_BB = BPreheader->getUniquePredecessor()->getTerminator();
    for(int i=0; i<AHeaderterm->getNumSuccessors(); i++){
      if(AHeaderterm->getSuccessor(i) == AExitBlock){
        AHeaderterm->setSuccessor(i, BPreheader);
        break;
      }
    }
    for(int i=0; i<Move_Up_BB.size(); i++){
      Move_Up_BB[i]->moveBefore(AHeader);
    }
    Instruction *APreheaderterm = APreheader->getTerminator();
    for(int i=0; i<Last_Move_BB->getNumSuccessors(); i++){
      if(Last_Move_BB->getSuccessor(i) == BPreheader){
        Last_Move_BB->setSuccessor(i, AHeader);
        break;
      }
    }
    APreheader->replaceSuccessorsPhiUsesWith(Last_Move_BB->getParent());
    // Move_Up_BB[0] is AExitBlock
    APreheaderterm->setSuccessor(0, AExitBlock);
    DT.recalculate(F);
    PDT.recalculate(F);
  }

  void move_intervening_code_down(const Loop &Aloop, const Loop &Bloop, SmallVector<BasicBlock*, 16> &Move_Down_BB, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
    // move the intervening code down to the start of exit block of second loop
    // outs() << "Can move down\n";
    BasicBlock *AHeader = Aloop.getHeader();
    BasicBlock *AExitBlock = Aloop.getExitBlock();
    BasicBlock *BPreheader = Bloop.getLoopPreheader();
    BasicBlock *BHeader = Bloop.getHeader();
    BasicBlock *BExitBlock = Bloop.getExitBlock();
    Instruction *AHeaderterm = AHeader->getTerminator();
    Instruction *Last_Move_BB = BPreheader->getUniquePredecessor()->getTerminator();
    // outs() << *Last_Move_BB << "\n";
    for(int i=0; i<AHeaderterm->getNumSuccessors(); i++){
      if(AHeaderterm->getSuccessor(i) == AExitBlock){
        AHeaderterm->setSuccessor(i, BPreheader);
        break;
      }
    }
    Instruction *BHeaderterm = BHeader->getTerminator();
    // outs() << Move_Down_BB[0] << " : " << AExitBlock << "\n";
    for(int i=0; i<BHeaderterm->getNumSuccessors(); i++){
      if(BHeaderterm->getSuccessor(i) == BExitBlock){
        // BHeaderterm->setSuccessor(i, Move_Down_BB[0]);
        BHeaderterm->setSuccessor(i, AExitBlock);
        break;
      }
    }

    for(int i=0; i<Move_Down_BB.size(); i++){
      Move_Down_BB[i]->moveBefore(BExitBlock);
    }
    // Instruction *Last_Move_BB = Move_Down_BB[Move_Down_BB.size()-1]->getTerminator();
    // outs() << *Last_Move_BB << "\n";

    for(int i=0; i<Last_Move_BB->getNumSuccessors(); i++){
      if(Last_Move_BB->getSuccessor(i) == BPreheader){
        // outs() << *(Last_Move_BB->getSuccessor(i)) << "\n";
        Last_Move_BB->setSuccessor(0, BExitBlock);
        break;
      }
    }
    // Last_Move_BB->setSuccessor(0, BExitBlock);
    DT.recalculate(F);
    PDT.recalculate(F);
  }

  bool moveMoreInterveningCode(const Loop &Aloop, const Loop &Bloop,
    SmallVector<Instruction *, 16> &AMemReads,
    SmallVector<Instruction *, 16> &AMemWrites,
    SmallVector<Instruction *, 16> &BMemReads,
    SmallVector<Instruction *, 16> &BMemWrites,
    DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
      std::queue<BasicBlock*> intervening_BB;
      std::unordered_map<uintptr_t, bool> visited_BB;
      SmallVector<BasicBlock*, 16> Move_Up_BB;
      SmallVector<BasicBlock*, 16> Move_Down_BB;
      SmallVector<BasicBlock*, 16> All_Check_BB;
      BasicBlock *Aheader = Aloop.getHeader();
      BasicBlock *Bheader = Bloop.getHeader();
      BasicBlock *AExitBlock = Aloop.getExitBlock();
      BasicBlock *BPreheader = Bloop.getLoopPreheader();
      intervening_BB.push(AExitBlock);
      All_Check_BB.push_back(AExitBlock);
      visited_BB[reinterpret_cast<uintptr_t>(AExitBlock)] = true;
      /*
        Find all intervening code basic blocks, guarantee that loops in intervening code will also be checked when hoist intervening code. 
      */
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && terminator->getSuccessor(i) != BPreheader){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            All_Check_BB.push_back(terminator->getSuccessor(i));
          }
        }
      }
      visited_BB.clear();
      /*
        Check if intervening code can be moved
      */
      intervening_BB.push(AExitBlock);
      visited_BB[reinterpret_cast<uintptr_t>(AExitBlock)] = true;
      int Num_BB = 0;
      SmallVector<Instruction *, 4> SafeToMoveUp;
      SmallVector<Instruction *, 4> SafeToMoveDown;
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Num_BB++;
        bool movable = false;
        if (!BB_dependent_on_firstloop(current_BB, Aloop, AMemReads, AMemWrites, Move_Up_BB, SafeToMoveUp, DI, DT, PDT, All_Check_BB)) {
          // Not dependent on first loop, potentially move up
          Move_Up_BB.push_back(current_BB);
          movable = true;
        }
        if (!BB_dependent_on_secondloop(current_BB, Bloop, BMemReads, BMemWrites, Move_Down_BB, SafeToMoveDown, DI, DT, PDT)) {
          // Not dependent on second loop, potentially move down
          Move_Down_BB.push_back(current_BB);
          movable = true;
        }
        if (!movable) {
          // Dependent on both loops, can't be fused
          // outs() << "cannot move up\n";
          return false;
        }
        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && terminator->getSuccessor(i) != BPreheader){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            // outs() << "push " << *(terminator->getSuccessor(i)) << "to queue\n";
          }
        }
      }
      if(Num_BB == Move_Down_BB.size()){
        // outs() << "can be movedown\n";
        move_intervening_code_down(Aloop, Bloop, Move_Down_BB, DT, PDT, F);
        return true;
      }
      else if(Num_BB == Move_Up_BB.size()){
        // outs() << "can be moveup\n";
        move_intervening_code_up(Aloop, Bloop, Move_Up_BB, DT, PDT, F);
        return true;
      }
      // if(Num_BB == Move_Up_BB.size()){
      //   // outs() << "can be moveup\n";
      //   move_intervening_code_up(Aloop, Bloop, Move_Up_BB, DT, PDT, F);
      //   return true;
      // }
      // else if(Num_BB == Move_Down_BB.size()){
      //   // outs() << "can be movedown\n";
      //   move_intervening_code_down(Aloop, Bloop, Move_Down_BB, DT, PDT, F);
      //   return true;
      // }
      return false;
  }

  void restoreSinkNonCFEInterveningCode(Instruction *PreentryTermInst,
    BasicBlock *Restore_PreentryTermInst, Instruction *Last_PostDominate_BB_Term,
    int Last_PostDominate_BB_Term_Index, BasicBlock* Restore_Last_PostDominate_BB_Term,
    Instruction *AHeaderTermInst, int AExitBlock_Term_Index,
    BasicBlock *Restore_AHeaderTermInst, BasicBlock *APreheader, 
    BasicBlock *AExitBlock, const Loop &Aloop, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
      // outs() << "restoreSinkNonCFEInterveningCode\n";
      PreentryTermInst->setSuccessor(0, Restore_PreentryTermInst);
      Last_PostDominate_BB_Term->setSuccessor(Last_PostDominate_BB_Term_Index, Restore_Last_PostDominate_BB_Term);
      AHeaderTermInst->setSuccessor(AExitBlock_Term_Index, Restore_AHeaderTermInst);
      APreheader->moveBefore(AExitBlock);
      for(BasicBlock *BB : Aloop.blocks()){
        BB->moveBefore(AExitBlock);
      }
      DT.recalculate(F);
      PDT.recalculate(F);
      return;
  }

  bool checkSinkNonCFEInterveningCode(const Loop &Aloop, const Loop &Bloop,
    SmallVector<Instruction *, 16> &AMemReads,
    SmallVector<Instruction *, 16> &AMemWrites,
    SmallVector<Instruction *, 16> &BMemReads,
    SmallVector<Instruction *, 16> &BMemWrites,
    SmallVector<BasicBlock*, 16> &Last_PostDominate_BB_Succ,
    BasicBlock* Last_PostDominate_BB, DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
    /*
    The "moveNonCFEInterveningCodetoBranch" is moved here since we need to record the original basicblocks for restoring if there is a data dependence.
    */
      // outs() << "checkSinkNonCFEInterveningCode\n";
    /*
    *
    *
    * 
    * The moveNonCFEInterveningCodetoBranch function starts
    * 
    * 
    * 
    */
      BasicBlock *APreheader = Aloop.getLoopPreheader();
      BasicBlock *AHeader = Aloop.getHeader();
      BasicBlock *AExitBlock = Aloop.getExitBlock();
      BasicBlock *BHeader = Bloop.getHeader();
      BasicBlock *Dominate_Bloop_BB;
      bool Dominate_Bloop_BB_is_null = true;
      Instruction *Last_PostDominate_BB_Term = Last_PostDominate_BB->getTerminator();
      int Last_PostDominate_BB_Term_Index = -1;
      for(int i=0; i<Last_PostDominate_BB_Term->getNumSuccessors(); i++){
        if(DT.dominates(Last_PostDominate_BB_Term->getSuccessor(i), BHeader) &&
          PDT.dominates(BHeader, Last_PostDominate_BB_Term->getSuccessor(i))){
          Dominate_Bloop_BB = Last_PostDominate_BB_Term->getSuccessor(i);
          Last_PostDominate_BB_Term_Index = i;
          Dominate_Bloop_BB_is_null = false;
          break;
        }
      }
      int AExitBlock_Term_Index = -1;
      Instruction *AHeaderTermInst = AHeader->getTerminator();
      BranchInst *AHeaderTermInst_Br = dyn_cast<BranchInst>(AHeaderTermInst);
      for(int i=0; i<AHeaderTermInst->getNumSuccessors(); i++){
        if(AHeaderTermInst->getSuccessor(i) == AExitBlock){
          AExitBlock_Term_Index = i;
          break;
        }
      }
      if(AExitBlock_Term_Index <0 || Last_PostDominate_BB_Term_Index <0 ||
        Dominate_Bloop_BB_is_null){
          // outs() << "moveNonCFEInterveningCodetoBranch: BB is NULL\n";
          return false;
        }
      // // outs() << "moveNonCFEInterveningCodetoBranch" << *Dominate_Bloop_BB;
      // assert(AExitBlock_Term_Index >= 0 && Last_PostDominate_BB_Term_Index >= 0 && Dominate_Bloop_BB && "moveNonCFEInterveningCodetoBranch: BB is NULL\n");
      BasicBlock *Preentry = APreheader->getUniquePredecessor();
      if(!Preentry){
        // outs() << "Preentry is NULL\n";
        return false;
      }
      // assert(Preentry && "Preentry is NULL\n");
      APreheader->moveBefore(Dominate_Bloop_BB);
      for(BasicBlock *BB : Aloop.blocks()){
        // // outs() << *BB;
        BB->moveBefore(Dominate_Bloop_BB);
      }

      Instruction *PreentryTermInst = Preentry->getTerminator();
      BranchInst *PreentryTermInst_Br = dyn_cast<BranchInst>(PreentryTermInst);
      if(PreentryTermInst_Br->isConditional()){
        // outs() << "preentry branch is conditional branch\n";
        return false;
      }
      // assert(!PreentryTermInst_Br->isConditional() && "preentry branch is conditional branch\n");
      if(!AHeaderTermInst_Br->isConditional()){
        // outs() << "header branch is not conditional branch\n";
        return false;
      }
      // assert(AHeaderTermInst_Br->isConditional() && "header branch is not conditional branch\n");
      BasicBlock *Restore_PreentryTermInst = PreentryTermInst->getSuccessor(0);
      BasicBlock *Restore_Last_PostDominate_BB_Term = Last_PostDominate_BB_Term->getSuccessor(Last_PostDominate_BB_Term_Index);
      BasicBlock *Restore_AHeaderTermInst = AHeaderTermInst->getSuccessor(AExitBlock_Term_Index);

      PreentryTermInst->setSuccessor(0, AExitBlock);
      Last_PostDominate_BB_Term->setSuccessor(Last_PostDominate_BB_Term_Index, APreheader);
      AHeaderTermInst->setSuccessor(AExitBlock_Term_Index, Dominate_Bloop_BB);
      // // outs() << *Restore_PreentryTermInst << *Restore_Last_PostDominate_BB_Term << *Restore_AHeaderTermInst;
      DT.recalculate(F);
      PDT.recalculate(F);
    /*
    *
    *
    * 
    * The moveNonCFEInterveningCodetoBranch function ends
    * 
    * 
    * 
    */

      BasicBlock *BPreheader = Bloop.getLoopPreheader();
      BasicBlock *First_Dominate_BB;
      bool First_Dominate_BB_is_null = true;
      for(BasicBlock *BB : Last_PostDominate_BB_Succ){
        if(DT.dominates(BB, BHeader) && PDT.dominates(BHeader, BB)){
          First_Dominate_BB = BB;
          First_Dominate_BB_is_null = false;
          break;
        }
      }
      if(First_Dominate_BB_is_null){
        // Restore Code
        restoreSinkNonCFEInterveningCode(PreentryTermInst, Restore_PreentryTermInst,
            Last_PostDominate_BB_Term, Last_PostDominate_BB_Term_Index,
            Restore_Last_PostDominate_BB_Term, AHeaderTermInst, AExitBlock_Term_Index, Restore_AHeaderTermInst,
            APreheader, AExitBlock, Aloop, DT, PDT, F);
        // outs() << "Basic Block is Null, restore Non CFE Intervening Code.\n";
        return false;
      }
      std::queue<BasicBlock*> intervening_BB;
      std::unordered_map<uintptr_t, bool> visited_BB;
      SmallVector<BasicBlock*, 16> Move_Up_BB;
      SmallVector<BasicBlock*, 16> Move_Down_BB;
      SmallVector<BasicBlock*, 16> All_Check_BB;
      intervening_BB.push(First_Dominate_BB);
      All_Check_BB.push_back(First_Dominate_BB);
      visited_BB[reinterpret_cast<uintptr_t>(First_Dominate_BB)] = true;
      /*
        Find all intervening code basic blocks, guarantee that loops in intervening code will also be checked when hoist intervening code. 
      */
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && terminator->getSuccessor(i) != BPreheader){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            All_Check_BB.push_back(terminator->getSuccessor(i));
          }
        }
      }
      visited_BB.clear();
      /*
        Check if intervening code can be moved
      */

      intervening_BB.push(First_Dominate_BB);
      visited_BB[reinterpret_cast<uintptr_t>(First_Dominate_BB)] = true;
      int Num_BB = 0;
      SmallVector<Instruction *, 4> SafeToMoveUp;
      SmallVector<Instruction *, 4> SafeToMoveDown;
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Num_BB++;
        bool movable = false;
        if (!BB_dependent_on_firstloop(current_BB, Aloop, AMemReads, AMemWrites, Move_Up_BB, SafeToMoveUp, DI, DT, PDT, All_Check_BB)) {
          // Not dependent on first loop, potentially move up
          Move_Up_BB.push_back(current_BB);
          movable = true;
        }
        if (!BB_dependent_on_secondloop(current_BB, Bloop, BMemReads, BMemWrites, Move_Down_BB, SafeToMoveDown, DI, DT, PDT)) {
          // Not dependent on second loop, potentially move down
          Move_Down_BB.push_back(current_BB);
          movable = true;
        }
        if (!movable) {
          // Dependent on both loops, can't be fused
          // Restore Code
          restoreSinkNonCFEInterveningCode(PreentryTermInst, Restore_PreentryTermInst,
            Last_PostDominate_BB_Term, Last_PostDominate_BB_Term_Index,
            Restore_Last_PostDominate_BB_Term, AHeaderTermInst, AExitBlock_Term_Index, Restore_AHeaderTermInst,
            APreheader, AExitBlock, Aloop, DT, PDT, F);
          // outs() << "!movable, restore Non CFE Intervening Code.\n";
          return false;
        }
        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && terminator->getSuccessor(i) != BPreheader){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            // // outs() << "push " << *(terminator->getSuccessor(i)) << "to queue\n";
          }
        }
      }
      if(Num_BB == Move_Down_BB.size()){
        // outs() << "NonCFEInterveningCode can be move down\n";
        move_intervening_code_down(Aloop, Bloop, Move_Down_BB, DT, PDT, F);
        return true;
      }
      else if(Num_BB == Move_Up_BB.size()){
        // outs() << "NonCFEInterveningCode can be move up\n";
        move_intervening_code_up(Aloop, Bloop, Move_Up_BB, DT, PDT, F);
        return true;
      }
      // Restore Code
      restoreSinkNonCFEInterveningCode(PreentryTermInst, Restore_PreentryTermInst,
            Last_PostDominate_BB_Term, Last_PostDominate_BB_Term_Index,
            Restore_Last_PostDominate_BB_Term, AHeaderTermInst, AExitBlock_Term_Index, Restore_AHeaderTermInst,
            APreheader, AExitBlock, Aloop, DT, PDT, F);
      // outs() << "Restore Non CFE Intervening Code.\n";
      return false;
  }

  void cloneSinkLoopToOtherBranch(Loop &Aloop, Loop &Bloop, BasicBlock* Last_PostDominate_BB,
    LoopInfo &LI, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
      ValueToValueMapTy VMap;
      BasicBlock *APreheader = Aloop.getLoopPreheader();
      BasicBlock *AHeader = Aloop.getHeader();
      BasicBlock *ALatch= Aloop.getLoopLatch();
      BasicBlock *AExitBlock = Aloop.getExitBlock();
      BasicBlock *BHeader = Bloop.getHeader();
      // Determine to clone loop to which basicblock
      Instruction *Last_PostDominate_BB_Term = Last_PostDominate_BB->getTerminator();
      assert(Last_PostDominate_BB_Term->getNumSuccessors() == 2 && "Last_PostDominate_BB_Term->getNumSuccessors() != 2\n");
      BasicBlock *Loop_in_this_BB;
      BasicBlock *Cloned_loop_to_this_BB;
      int Loop_in_this_BB_index = -1;
      int Cloned_loop_to_this_BB_index = -1;
      for(int i=0; i<Last_PostDominate_BB_Term->getNumSuccessors(); i++){
        if(DT.dominates(Last_PostDominate_BB_Term->getSuccessor(i), AHeader) && PDT.dominates(AHeader, Last_PostDominate_BB_Term->getSuccessor(i))){
          Loop_in_this_BB = Last_PostDominate_BB_Term->getSuccessor(i);
          Loop_in_this_BB_index = i;
        }
        else{
          Cloned_loop_to_this_BB = Last_PostDominate_BB_Term->getSuccessor(i);
          Cloned_loop_to_this_BB_index = i;
        }
      }
      // // outs() << *Loop_in_this_BB << *Cloned_loop_to_this_BB;
      assert(Loop_in_this_BB && Cloned_loop_to_this_BB && "cloneSinkLoopToOtherBranch error\n");
      assert(Loop_in_this_BB_index >= 0 && Cloned_loop_to_this_BB_index >= 0 && "cloneSinkLoopToOtherBranch error\n");

      SmallVector<BasicBlock *, 16> Blocks;
      Loop *ClonedLoop = cloneLoopWithPreheader(APreheader, APreheader, &Aloop, VMap, "", &LI, &DT, Blocks);
      VMap[AExitBlock] = APreheader; // chain: cloned loop -> original loop
      remapInstructionsInBlocks(Blocks, VMap);
      BasicBlock *ClonedPreheader = ClonedLoop->getLoopPreheader();
      BasicBlock *ClonedHeader = ClonedLoop->getHeader();
      BasicBlock *ClonedLatch= ClonedLoop->getLoopLatch();
      BasicBlock *ClonedExitBlock = ClonedLoop->getExitBlock();
      // move the preheader before Cloned_loop_to_this_BB
      ClonedPreheader->moveBefore(Cloned_loop_to_this_BB);
      // move all the blocks before Cloned_loop_to_this_BB
      for(BasicBlock *BB : ClonedLoop->blocks()){
        BB->moveBefore(Cloned_loop_to_this_BB);
      }
      // setSuccessor()
      Last_PostDominate_BB_Term->setSuccessor(Cloned_loop_to_this_BB_index, ClonedPreheader);
      Instruction *ClonedHeader_TermInst = ClonedHeader->getTerminator();
      BranchInst *ClonedHeaderBr = dyn_cast<BranchInst>(ClonedHeader_TermInst);
      assert(ClonedHeaderBr->isConditional() && "cloned header is not conditional branch\n");
      int ClonedHeader_to_ExitBlock_index = -1;
      for(int i=0; i<ClonedHeader_TermInst->getNumSuccessors(); i++){
        if(ClonedHeader_TermInst->getSuccessor(i) == ClonedExitBlock){
          ClonedHeader_to_ExitBlock_index = i;
        }
      }
      assert(ClonedHeader_to_ExitBlock_index >= 0 && "ClonedHeader_to_ExitBlock_index < 0");
      ClonedHeader_TermInst->setSuccessor(ClonedHeader_to_ExitBlock_index, Cloned_loop_to_this_BB);
      Cloned_loop_to_this_BB->replacePhiUsesWith(Last_PostDominate_BB, ClonedHeader);
      DT.recalculate(F);
      PDT.recalculate(F);
      return;
  }

  bool sinkNonCFELoop(Loop &Aloop, Loop &Bloop,
    SmallVector<Instruction *, 16> &AMemReads,
    SmallVector<Instruction *, 16> &AMemWrites,
    SmallVector<Instruction *, 16> &BMemReads,
    SmallVector<Instruction *, 16> &BMemWrites,
    LoopInfo &LI, DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
      // outs() << "sinkNonCFELoop\n";
      // Find predecessors of Bheader until reaching Aheader
      std::queue<BasicBlock*> intervening_BB;
      std::unordered_map<uintptr_t, bool> visited_BB;
      SmallVector<BasicBlock*, 16> Move_Up_BB;
      BasicBlock *Aheader = Aloop.getHeader();
      BasicBlock *Bheader = Bloop.getHeader();
      BasicBlock *AExitBlock = Aloop.getExitBlock();
      BasicBlock *BPreheader = Bloop.getLoopPreheader();
      SmallVector<Instruction *, 4> SafeToMoveUp;
      intervening_BB.push(BPreheader);
      visited_BB[reinterpret_cast<uintptr_t>(BPreheader)] = true;
      int Num_BB = 0;
      // // outs() << "push " << *BPreheader << "to queue\n";

      // Find predecessors of BPreheader until reaching the first BB which is CFE with AExitBlock. 
      BasicBlock *Last_PostDominate_BB;
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        if(PDT.dominates(current_BB, Aheader)){
          Last_PostDominate_BB = current_BB;
          // // outs() << "Find the BB which dual-dominates the first loop\n";
          // // outs() << *Last_PostDominate_BB;
          break;
        }
        else{
          for(BasicBlock *Pred : predecessors(current_BB)){
            if(visited_BB[reinterpret_cast<uintptr_t>(Pred)] == false){
              intervening_BB.push(Pred);
              visited_BB[reinterpret_cast<uintptr_t>(Pred)] = true;
              // // outs() << "push " << *Pred << "to queue\n";
            }
          }
        }
      }
      // clear visited_BB and intervening_BB
      visited_BB.clear();
      while(!intervening_BB.empty()){
        intervening_BB.pop();
      }
      // BBs before Last_PostDominate_BB post-dominate the first loop.
      // BBs after Last_PostDominate_BB does not post-dominate the first loop.
      SmallVector<BasicBlock*, 16> Last_PostDominate_BB_Succ;
      if(succ_size(Last_PostDominate_BB) != 2){
        // outs() << "Last_PostDominate_BB->getNumSuccessors() != 2\n";
        return false;
      }
      for(BasicBlock *Succ : successors(Last_PostDominate_BB)){
        Last_PostDominate_BB_Succ.push_back(Succ);
        // // outs() << "Succ"<< *Succ;
      }
      /*
        Find all intervening code basic blocks, guarantee that loops in intervening code will also be checked when hoist intervening code. 
      */
      SmallVector<BasicBlock*, 16> All_Check_BB;
      intervening_BB.push(AExitBlock);
      All_Check_BB.push_back(AExitBlock);
      visited_BB[reinterpret_cast<uintptr_t>(AExitBlock)] = true;
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && !is_contained(Last_PostDominate_BB_Succ, terminator->getSuccessor(i))){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            All_Check_BB.push_back(terminator->getSuccessor(i));
          }
        }
      }
      visited_BB.clear();
      /*
        Check if intervening code can be moved
      */
      intervening_BB.push(AExitBlock);
      visited_BB[reinterpret_cast<uintptr_t>(AExitBlock)] = true;
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Num_BB++;
        bool movable = false;
        if(!BB_dependent_on_firstloop(current_BB, Aloop, AMemReads, AMemWrites, Move_Up_BB, SafeToMoveUp, DI, DT, PDT, All_Check_BB)){
          Move_Up_BB.push_back(current_BB);
          movable = true;
        }

        if (!movable) {
          // Dependent on both loops, can't be fused
          // outs() << *current_BB << "!movable\n";
          return false;
        }

        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && !is_contained(Last_PostDominate_BB_Succ, terminator->getSuccessor(i))){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            // // outs() << "push " << *(terminator->getSuccessor(i)) << "to queue\n";
          }
        }
      }

      if(Num_BB == Move_Up_BB.size()){
        // now check data dependency in the branch
        Move_Up_BB.clear();
        SafeToMoveUp.clear();
        // move code to the NonCFE basic block(the branch basic block)
        // In checkSinkNonCFEInterveningCode, it moves code and restores code if return false;
        if(!checkSinkNonCFEInterveningCode(Aloop, Bloop,
          AMemReads, AMemWrites, BMemReads, BMemWrites, Last_PostDominate_BB_Succ, Last_PostDominate_BB, DI, DT, PDT, F)){  
          return false;
        }
        // TODO: clone sink loop to the other branch
        cloneSinkLoopToOtherBranch(Aloop, Bloop, Last_PostDominate_BB, LI, DT, PDT, F);
        return true;
      }
      // outs() << "false\n";
      return false;
  }

  void restoreHoistNonCFEInterveningCode(BasicBlock *BPreheader, BasicBlock *BExitBlock,
    Instruction *PreentryTermInst, BasicBlock *Restore_PreentryTermInst, 
    Instruction *PostDominate_Aloop_BB_Term, BasicBlock *Restore_PostDominate_Aloop_BB_Term,
    Instruction *BHeaderTermInst, int BExitBlock_Term_Index,
    BasicBlock *Restore_BHeaderTermInst, const Loop &Bloop,
    DominatorTree &DT, PostDominatorTree &PDT, Function &F){
    // outs() << "restoreHoistNonCFEInterveningCode\n";
    BPreheader->moveBefore(BExitBlock);
      for(BasicBlock *BB : Bloop.blocks()){
        // // outs() << *BB;
        BB->moveBefore(BExitBlock);
      }
      PreentryTermInst->setSuccessor(0, Restore_PreentryTermInst);
      PostDominate_Aloop_BB_Term->setSuccessor(0, Restore_PostDominate_Aloop_BB_Term);
      BHeaderTermInst->setSuccessor(BExitBlock_Term_Index, Restore_BHeaderTermInst);
      DT.recalculate(F);
      PDT.recalculate(F);
    return;
  }

  bool checkHoistNonCFEInterveningCode(const Loop &Aloop, const Loop &Bloop,
    SmallVector<Instruction *, 16> &AMemReads,
    SmallVector<Instruction *, 16> &AMemWrites,
    SmallVector<Instruction *, 16> &BMemReads,
    SmallVector<Instruction *, 16> &BMemWrites,
    SmallVector<BasicBlock*, 16> &First_Dominate_BB_Pred,
    BasicBlock* First_Dominate_BB, DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
    /*
    The "moveNonCFEInterveningCodetoBranch" is moved here since we need to record the original basicblocks for restoring if there is a data dependence.
    */
      // outs() << "checkHoistNonCFEInterveningCode\n";
    /*
    *
    *
    * 
    * The moveNonCFEInterveningCodetoBranch function starts
    * 
    * 
    * 
    */
      BasicBlock *APreheader = Aloop.getLoopPreheader();
      BasicBlock *AHeader = Aloop.getHeader();
      BasicBlock *BPreheader = Bloop.getLoopPreheader();
      BasicBlock *BHeader = Bloop.getHeader();
      BasicBlock *BExitBlock = Bloop.getExitBlock();
      BasicBlock *PostDominate_Aloop_BB;
      bool PostDominate_Aloop_BB_is_null = true;
      if(First_Dominate_BB_Pred.size() != 2){
        // outs() << "First_Dominate_BB_Pred.size() != 2\n";
        return false;
      }
      for(BasicBlock *Pred : First_Dominate_BB_Pred){
        if(DT.dominates(AHeader, Pred) && PDT.dominates(Pred, AHeader)){
          PostDominate_Aloop_BB = Pred;
          PostDominate_Aloop_BB_is_null = false;
          break;
        }
      }
      // assert(!PostDominate_Aloop_BB_is_null && "PostDominate_Aloop_BB is NULL\n");
      if(PostDominate_Aloop_BB_is_null){
        // outs() << "PostDominate_Aloop_BB is NULL\n";
        return false;
      }
      // outs() << "NULL\n";
      Instruction* PostDominate_Aloop_BB_Term = PostDominate_Aloop_BB->getTerminator();
      if(PostDominate_Aloop_BB_Term->getNumSuccessors() != 1){
        // outs() << "PostDominate_Aloop_BB_Term is conditional\n";
        return false;
      }

      int BExitBlock_Term_Index = -1;
      Instruction *BHeaderTermInst = BHeader->getTerminator();
      BranchInst *BHeaderTermInst_Br = dyn_cast<BranchInst>(BHeaderTermInst);
      for(int i=0; i<BHeaderTermInst->getNumSuccessors(); i++){
        if(BHeaderTermInst->getSuccessor(i) == BExitBlock){
          BExitBlock_Term_Index = i;
          break;
        }
      }
      if(BExitBlock_Term_Index < 0){
        // outs() << "BExitBlock_Term_Index < 0\n";
        return false;
      }
      // // outs() << "moveNonCFEInterveningCodetoBranch" << *PostDominate_Aloop_BB;

      BasicBlock *Preentry = BPreheader->getUniquePredecessor();
      if(!Preentry){
        // outs() << "Preentry is NULL\n";
        return false;
      }

      Instruction *PreentryTermInst = Preentry->getTerminator();
      BranchInst *PreentryTermInst_Br = dyn_cast<BranchInst>(PreentryTermInst);
      if(PreentryTermInst_Br->isConditional()){
        // outs() << "preentry branch is conditional branch\n";
        return false;
      }

      if(!BHeaderTermInst_Br->isConditional()){
        // outs() << "header branch is not conditional branch\n";
        return false;
      }

      for(BasicBlock *BB : reverse(Bloop.blocks())){
        // // outs() << *BB;
        BB->moveAfter(PostDominate_Aloop_BB);
      }
      BPreheader->moveAfter(PostDominate_Aloop_BB);
      BasicBlock *Restore_PreentryTermInst = PreentryTermInst->getSuccessor(0);
      BasicBlock *Restore_PostDominate_Aloop_BB_Term = PostDominate_Aloop_BB_Term->getSuccessor(0);
      BasicBlock *Restore_BHeaderTermInst = BHeaderTermInst->getSuccessor(BExitBlock_Term_Index);
      // // outs() << *Restore_PreentryTermInst << *Restore_PostDominate_Aloop_BB_Term << *Restore_BHeaderTermInst;
      
      PreentryTermInst->setSuccessor(0, BExitBlock);
      PostDominate_Aloop_BB_Term->setSuccessor(0, BPreheader);
      BHeaderTermInst->setSuccessor(BExitBlock_Term_Index, First_Dominate_BB);
      DT.recalculate(F);
      PDT.recalculate(F);
    /*
    *
    *
    * 
    * The moveNonCFEInterveningCodetoBranch function ends
    * 
    * 
    * 
    */
      BasicBlock *AExitBlock = Aloop.getExitBlock();
      std::queue<BasicBlock*> intervening_BB;
      std::unordered_map<uintptr_t, bool> visited_BB;
      SmallVector<BasicBlock*, 16> Move_Up_BB;
      SmallVector<BasicBlock*, 16> Move_Down_BB;
      SmallVector<BasicBlock*, 16> All_Check_BB;
      intervening_BB.push(AExitBlock);
      All_Check_BB.push_back(AExitBlock);
      visited_BB[reinterpret_cast<uintptr_t>(AExitBlock)] = true;
      /*
        Find all intervening code basic blocks, guarantee that loops in intervening code will also be checked when hoist intervening code. 
      */
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && terminator->getSuccessor(i) != BPreheader){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            All_Check_BB.push_back(terminator->getSuccessor(i));
          }
        }
      }
      visited_BB.clear();
      /*
        Check if intervening code can be moved
      */
      intervening_BB.push(AExitBlock);
      visited_BB[reinterpret_cast<uintptr_t>(AExitBlock)] = true;
      int Num_BB = 0;
      SmallVector<Instruction *, 4> SafeToMoveUp;
      SmallVector<Instruction *, 4> SafeToMoveDown;
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Num_BB++;
        bool movable = false;
        if (!BB_dependent_on_firstloop(current_BB, Aloop, AMemReads, AMemWrites, Move_Up_BB, SafeToMoveUp, DI, DT, PDT, All_Check_BB)) {
          // Not dependent on first loop, potentially move up
          Move_Up_BB.push_back(current_BB);
          movable = true;
        }
        if (!BB_dependent_on_secondloop(current_BB, Bloop, BMemReads, BMemWrites, Move_Down_BB, SafeToMoveDown, DI, DT, PDT)) {
          // Not dependent on second loop, potentially move down
          Move_Down_BB.push_back(current_BB);
          movable = true;
        }
        if (!movable) {
          // Dependent on both loops, can't be fused
          // Restore Code
          restoreHoistNonCFEInterveningCode(BPreheader, BExitBlock, PreentryTermInst, Restore_PreentryTermInst,
            PostDominate_Aloop_BB_Term, Restore_PostDominate_Aloop_BB_Term,
            BHeaderTermInst, BExitBlock_Term_Index, Restore_BHeaderTermInst, Bloop, DT, PDT, F);
          // outs() << "!movable, restore Non CFE Intervening Code.\n";
          return false;
        }
        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && terminator->getSuccessor(i) != BPreheader){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            // outs() << "push " << *(terminator->getSuccessor(i)) << "to queue\n";
          }
        }
      }
      if(Num_BB == Move_Down_BB.size()){
        // outs() << "NonCFEInterveningCode can be move down\n";
        move_intervening_code_down(Aloop, Bloop, Move_Down_BB, DT, PDT, F);
        return true;
      }
      else if(Num_BB == Move_Up_BB.size()){
        // outs() << "NonCFEInterveningCode can be move up\n";
        move_intervening_code_up(Aloop, Bloop, Move_Up_BB, DT, PDT, F);
        return true;
      }
      // Restore Code
      restoreHoistNonCFEInterveningCode(BPreheader, BExitBlock, PreentryTermInst, Restore_PreentryTermInst,
        PostDominate_Aloop_BB_Term, Restore_PostDominate_Aloop_BB_Term,
        BHeaderTermInst, BExitBlock_Term_Index, Restore_BHeaderTermInst, Bloop, DT, PDT, F);
      // outs() << "Restore Non CFE Intervening Code.\n";
      return false;
  }

  void cloneHoistLoopToOtherBranch(Loop &Aloop, Loop &Bloop, BasicBlock* First_Dominate_BB,
    LoopInfo &LI, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
      ValueToValueMapTy VMap;
      BasicBlock *AHeader = Aloop.getHeader();
      BasicBlock *BPreheader = Bloop.getLoopPreheader();
      BasicBlock *BHeader = Bloop.getHeader();
      BasicBlock *BExitBlock = Bloop.getExitBlock();
      assert(pred_size(First_Dominate_BB) == 2 && "pred_size(First_Dominate_BB) != 2\n");
      BasicBlock *Loop_in_this_BB;
      BasicBlock *Cloned_loop_to_this_BB;
      // Determine to clone loop to which basicblock
      for(BasicBlock *Pred : predecessors(First_Dominate_BB)){
        if(DT.dominates(AHeader, Pred) && PDT.dominates(Pred, AHeader)){
          Loop_in_this_BB = Pred;
        }
        else{
          Cloned_loop_to_this_BB = Pred;
        }
      }
      // outs() << *Loop_in_this_BB << *Cloned_loop_to_this_BB;
      assert(Loop_in_this_BB && Cloned_loop_to_this_BB && "cloneHoistLoopToOtherBranch error\n");

      SmallVector<BasicBlock *, 16> Blocks;
      Loop *ClonedLoop = cloneLoopWithPreheader(BPreheader, BPreheader, &Bloop, VMap, "", &LI, &DT, Blocks);
      VMap[BExitBlock] = BPreheader; // chain: cloned loop -> original loop
      remapInstructionsInBlocks(Blocks, VMap);
      BasicBlock *ClonedPreheader = ClonedLoop->getLoopPreheader();
      BasicBlock *ClonedHeader = ClonedLoop->getHeader();
      BasicBlock *ClonedExitBlock = ClonedLoop->getExitBlock();
      int Cloned_loop_to_this_BB_index = -1;
      Instruction *Cloned_loop_to_this_BB_Term = Cloned_loop_to_this_BB->getTerminator();
      for(int i=0; i<Cloned_loop_to_this_BB_Term->getNumSuccessors(); i++){
        if(Cloned_loop_to_this_BB_Term->getSuccessor(i) == First_Dominate_BB){
          Cloned_loop_to_this_BB_index = i;
        }
      }
      assert(Cloned_loop_to_this_BB_index >= 0 && "Cloned_loop_to_this_BB_index < 0");
      // move all the blocks before Cloned_loop_to_this_BB
      for(BasicBlock *BB : reverse(ClonedLoop->blocks())){
        BB->moveAfter(Cloned_loop_to_this_BB);
      }
      // move the preheader before Cloned_loop_to_this_BB
      ClonedPreheader->moveAfter(Cloned_loop_to_this_BB);
      
      // setSuccessor()
      BasicBlock *Cloned_loop_to_this_BB_Term_Pred = Cloned_loop_to_this_BB_Term->getSuccessor(Cloned_loop_to_this_BB_index);
      Cloned_loop_to_this_BB_Term->setSuccessor(Cloned_loop_to_this_BB_index, ClonedPreheader);
      Instruction *ClonedHeader_TermInst = ClonedHeader->getTerminator();
      BranchInst *ClonedHeaderBr = dyn_cast<BranchInst>(ClonedHeader_TermInst);
      assert(ClonedHeaderBr->isConditional() && "cloned header is not conditional branch\n");
      int ClonedHeader_to_ExitBlock_index = -1;
      for(int i=0; i<ClonedHeader_TermInst->getNumSuccessors(); i++){
        if(ClonedHeader_TermInst->getSuccessor(i) == ClonedExitBlock){
          ClonedHeader_to_ExitBlock_index = i;
        }
      }
      assert(ClonedHeader_to_ExitBlock_index >= 0 && "ClonedHeader_to_ExitBlock_index < 0");
      ClonedHeader_TermInst->setSuccessor(ClonedHeader_to_ExitBlock_index, Cloned_loop_to_this_BB_Term_Pred);
      DT.recalculate(F);
      PDT.recalculate(F);
      return;
  }

  bool hoistNonCFELoop(Loop &Aloop, Loop &Bloop,
    SmallVector<Instruction *, 16> &AMemReads,
    SmallVector<Instruction *, 16> &AMemWrites,
    SmallVector<Instruction *, 16> &BMemReads,
    SmallVector<Instruction *, 16> &BMemWrites,
    LoopInfo &LI, DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT, Function &F){
      // outs() << "hoistNonCFELoop\n";
      // Find successors of Aheader until reaching Bheader
      std::queue<BasicBlock*> intervening_BB;
      std::unordered_map<uintptr_t, bool> visited_BB;
      SmallVector<BasicBlock*, 16> Move_Down_BB;
      BasicBlock *Aheader = Aloop.getHeader();
      BasicBlock *Bheader = Bloop.getHeader();
      BasicBlock *AExitBlock = Aloop.getExitBlock();
      BasicBlock *BPreheader = Bloop.getLoopPreheader();
      SmallVector<Instruction *, 4> SafeToMoveDown;
      intervening_BB.push(AExitBlock);
      visited_BB[reinterpret_cast<uintptr_t>(AExitBlock)] = true;
      int Num_BB = 0;
      // // outs() << "push " << *AExitBlock << "to queue\n";

      // Find successors of AExitBlock until reaching the first BB which is CFE with BPreheader. 
      BasicBlock *First_Dominate_BB;
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        if(DT.dominates(current_BB, Bheader)){
          First_Dominate_BB = current_BB;
          // // outs() << "Find the BB which dual-dominates the first loop\n";
          // // outs() << *First_Dominate_BB;
          break;
        }
        else{
          for(BasicBlock *Succ : successors(current_BB)){
            if(visited_BB[reinterpret_cast<uintptr_t>(Succ)] == false){
              intervening_BB.push(Succ);
              visited_BB[reinterpret_cast<uintptr_t>(Succ)] = true;
              // // outs() << "push " << *Succ << "to queue\n";
            }
          }
        }
      }
      // clear visited_BB and intervening_BB
      visited_BB.clear();
      while(!intervening_BB.empty()){
        intervening_BB.pop();
      }
      if(!First_Dominate_BB){
        return false;
      }
      // BBs before First_Dominate_BB does not dominate the second loop.
      // BBs after First_Dominate_BB dominates the second loop.

      SmallVector<BasicBlock*, 16> First_Dominate_BB_Pred;
      // outs() << "********";
      // outs() << *First_Dominate_BB << "\n";
      if(pred_size(First_Dominate_BB) != 2){
        outs() << "First_Dominate_BB->Num of Predecessors() != 2\n";
        return false;
      }
      for(BasicBlock *Pred : predecessors(First_Dominate_BB)){
        First_Dominate_BB_Pred.push_back(Pred);
        // outs() << "Pred"<< *Pred;
      }
      intervening_BB.push(First_Dominate_BB);
      visited_BB[reinterpret_cast<uintptr_t>(First_Dominate_BB)] = true;
      while(!intervening_BB.empty()){
        BasicBlock* current_BB = intervening_BB.front();
        intervening_BB.pop();
        Num_BB++;
        bool movable = false;
        if(!BB_dependent_on_secondloop(current_BB, Bloop, BMemReads, BMemWrites, Move_Down_BB, SafeToMoveDown, DI, DT, PDT)){
          Move_Down_BB.push_back(current_BB);
          movable = true;
        }

        if (!movable) {
          // Dependent on both loops, can't be fused
          // outs() << *current_BB << "!movable\n";
          return false;
        }

        Instruction *terminator = current_BB->getTerminator();
        for(int i=0; i<terminator->getNumSuccessors(); i++){
          if(visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] == false && terminator->getSuccessor(i) != BPreheader){
            intervening_BB.push(terminator->getSuccessor(i));
            visited_BB[reinterpret_cast<uintptr_t>(terminator->getSuccessor(i))] = true;
            // outs() << "push " << *(terminator->getSuccessor(i)) << "to queue\n";
          }
        }
      }

      if(Num_BB == Move_Down_BB.size()){
        // now check data dependency in the branch
        // outs() << "movable\n";
        Move_Down_BB.clear();
        SafeToMoveDown.clear();
        // move code to the NonCFE basic block(the branch basic block)
        // In checkHoistNonCFEInterveningCode, it moves code and restores code if return false;
        if(!checkHoistNonCFEInterveningCode(Aloop, Bloop,
          AMemReads, AMemWrites, BMemReads, BMemWrites, First_Dominate_BB_Pred, First_Dominate_BB, DI, DT, PDT, F)){  
          return false;
        }
        // TODO: clone loop to the other branch
        cloneHoistLoopToOtherBranch(Aloop, Bloop, First_Dominate_BB, LI, DT, PDT, F);
        return true;
      }

      // // outs() << "false\n";
      return false;
  }

  int codemotion(const SmallVector<Loop *, 4> &looplist, const SmallVector<const SCEV*, 4> &looptripcount,
  SmallVector<SmallVector<Instruction *, 16>> LoopMemReads, SmallVector<SmallVector<Instruction *, 16>> LoopMemWrites,
  DependenceInfo &DI, DominatorTree &DT, PostDominatorTree &PDT, LoopInfo &LI, Function &F, ScalarEvolution &SE){
    // find all adjacent loop
    // looplist.size()-1 will overflow?
    // declare looplist_size to store it 
    int looplist_size = looplist.size();
    if(!looplist_size){
      return 0;
    }
    bool already_fused_loop[looplist_size];
    for(int i=0; i<looplist_size; i++){
      already_fused_loop[i] = false;
    }
    int adjacentloop = 0;
    for(int i=0; i<looplist_size; i++){
      if(already_fused_loop[i]){
        continue;
      }
      for(int j=i+1; j<looplist_size; j++){
        if(i == j){
          continue;
        }
        if(already_fused_loop[j]){
          continue;
        }
        BasicBlock *Aheader = looplist[i]->getHeader();
        BasicBlock *Bheader = looplist[j]->getHeader();
        BasicBlock *AExitBlock = looplist[i]->getExitBlock();
        BasicBlock *BPreheader = looplist[j]->getLoopPreheader();
        SmallVector<Instruction *, 4> SafeToHoist;
        SmallVector<Instruction *, 4> SafeToSink;

        if(DT.dominates(Aheader, Bheader) && PDT.dominates(Bheader, Aheader)){
          if(!dependencesAllowFusion(*looplist[i], *looplist[j], DI,
          LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], SE, DT)){
            // outs() << "Memory dependencies do not allow fusion!\n";
            continue;
          }
          // // outs() << *Aheader << " and " << *Bheader;
          // outs() << "A and B are control flow equivalent\n";
          if(AExitBlock == BPreheader){
            if(collectMovablePreheaderInsts(*looplist[i], *looplist[j], SafeToHoist, SafeToSink,
            LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], DI, DT)){
              // outs() << "A and B can be fused\n";
              // outs() << *Aheader << " and " << *Bheader;
              already_fused_loop[i] = true;
              already_fused_loop[j] = true;
              unsigned L0count = 0;
              unsigned L1count = 0;
              if(auto *SCEV0 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[i])){
                L0count = SCEV0->getAPInt().getZExtValue();
              }
              if(auto *SCEV1 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[j])){
                L1count = SCEV1->getAPInt().getZExtValue();
              }
              if(L0count == L1count){
                adjacent_loop_same_tripcount++;
              }
              else{
                adjacent_loop_diff_tripcount++;
              }
              // adjacent_loop++;
              adjacentloop++;
              break;
            }
            else{
              // outs() << "adjacent_loop cannot be fused\n";
              continue;
            }
          }
          else{
            // splitPreheader(*looplist[i], DT, PDT, F);
            splitPreheader(*looplist[j], DT, PDT, F);
            if(moveMoreInterveningCode(*looplist[i], *looplist[j],
            LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], DI, DT, PDT, F)){
              // outs() << "A and B can be fused\n";
              already_fused_loop[i] = true;
              already_fused_loop[j] = true;
              unsigned L0count = 0;
              unsigned L1count = 0;
              if(auto *SCEV0 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[i])){
                L0count = SCEV0->getAPInt().getZExtValue();
              }
              if(auto *SCEV1 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[j])){
                L1count = SCEV1->getAPInt().getZExtValue();
              }
              if(L0count == L1count){
                nonadjacent_loop_same_tripcount++;
              }
              else{
                nonadjacent_loop_diff_tripcount++;
              }
              // nonadjacent_loop++;
              adjacentloop++;
              break;
            }
            else{
              mergePreheader(*looplist[j], DT, PDT, F);
              // outs() << "nonadjacent_loop cannot be fused\n";
              continue;
            }
            // mergePreheader(*looplist[i], DT, PDT, F);
            // mergePreheader(*looplist[j], DT, PDT, F);
          }
        }
        else if(DT.dominates(Aheader, Bheader) && !PDT.dominates(Bheader, Aheader)){
          if(!dependencesAllowFusion(*looplist[i], *looplist[j], DI,
          LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], SE, DT)){
            // outs() << "Memory dependencies do not allow fusion!\n";
            continue;
          }
          // outs() << "A dominates B but B does not post-dominate A\n";
          // Find predecessors of Bheader until reaching Aheader
          // splitExitBlock(*looplist[i], DT, PDT, F);
          splitPreheader(*looplist[i], DT, PDT, F);
          splitPreheader(*looplist[j], DT, PDT, F);
          if(sinkNonCFELoop(*looplist[i], *looplist[j],
          LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], LI, DI, DT, PDT, F)){
            // outs() << "can sink nonCFE loop\n";
            already_fused_loop[i] = true;
            already_fused_loop[j] = true;
            unsigned L0count = 0;
            unsigned L1count = 0;
            if(auto *SCEV0 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[i])){
              L0count = SCEV0->getAPInt().getZExtValue();
            }
            if(auto *SCEV1 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[j])){
              L1count = SCEV1->getAPInt().getZExtValue();
            }
            if(L0count == L1count){
              sink_loop_same_tripcount++;
            }
            else{
              sink_loop_diff_tripcount++;
            }
            // sink_loop++;
            adjacentloop++;
            break;
          }
          else{
            mergePreheader(*looplist[i], DT, PDT, F);
            mergePreheader(*looplist[j], DT, PDT, F);
            // outs() << "sink_loop cannot be fused\n";
            continue;
          }
          // mergePreheader(*looplist[i], DT, PDT, F);
          // mergePreheader(*looplist[j], DT, PDT, F);
        }
        else if(!DT.dominates(Aheader, Bheader) && PDT.dominates(Bheader, Aheader)){
          if(!dependencesAllowFusion(*looplist[i], *looplist[j], DI,
          LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], SE, DT)){
            // outs() << "Memory dependencies do not allow fusion!\n";
            continue;
          }
          // outs() << "A does not dominate B but B post-dominates A\n";
          splitPreheader(*looplist[i], DT, PDT, F);
          splitPreheader(*looplist[j], DT, PDT, F);
          // outs() << *(looplist[i]->getHeader());
          // outs() << *(looplist[j]->getHeader());
          if(hoistNonCFELoop(*looplist[i], *looplist[j],
          LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], LI, DI, DT, PDT, F)){
            // outs() << "can hoist nonCFE loop\n";
            // outs() << *(looplist[i]->getHeader());
            // outs() << *(looplist[j]->getHeader());
            already_fused_loop[i] = true;
            already_fused_loop[j] = true;
            unsigned L0count = 0;
            unsigned L1count = 0;
            if(auto *SCEV0 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[i])){
              L0count = SCEV0->getAPInt().getZExtValue();
            }
            if(auto *SCEV1 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[j])){
              L1count = SCEV1->getAPInt().getZExtValue();
            }
            if(L0count == L1count){
              hoist_loop_same_tripcount++;
            }
            else{
              hoist_loop_diff_tripcount++;
            }
            // hoist_loop++;
            adjacentloop++;
            break;
          }
          else{
            mergePreheader(*looplist[i], DT, PDT, F);
            mergePreheader(*looplist[j], DT, PDT, F);
            // outs() << "hoist_loop cannot be fused\n";
            continue;
          }
          // mergePreheader(*looplist[i], DT, PDT, F);
          // mergePreheader(*looplist[j], DT, PDT, F);
        }
      }
    }
    return adjacentloop;
  }
}

PreservedAnalyses CodeMotionPass::run(Function &F, FunctionAnalysisManager &FAM) {
    FAM.clear();
    LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
    ScalarEvolution &SE = FAM.getResult<ScalarEvolutionAnalysis>(F);
    DependenceInfo &DI = FAM.getResult<DependenceAnalysis>(F);
    DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
    PostDominatorTree &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
    SmallVector<Loop *, 4> looplist;
    SmallVector<const SCEV*, 4> looptripcount;
    SmallVector<SmallVector<Instruction *, 16>> LoopMemReads;
    SmallVector<SmallVector<Instruction *, 16>> LoopMemWrites;
    for(Loop *L : LI){
      if(!isValidLoop(L)){
        continue;
      }
      // The number of iteration of a loop can be computed by SCEV
      if (SE.hasLoopInvariantBackedgeTakenCount(L)) {
        const SCEV *LoopCount = SE.getBackedgeTakenCount(L);
        // Loop trip count is a constant
        if(isa<SCEVConstant>(LoopCount)){
          SmallVector<Instruction *, 16> MemReads;
          SmallVector<Instruction *, 16> MemWrites;
          for(BasicBlock *BB : L->blocks()){
            for(Instruction &I : *BB){
              if(I.mayWriteToMemory()){
                MemWrites.push_back(&I);
              }
              if(I.mayReadFromMemory()){
                MemReads.push_back(&I);
              }
            }
          }
          looplist.push_back(L);
          looptripcount.push_back(LoopCount);
          LoopMemReads.push_back(MemReads);
          LoopMemWrites.push_back(MemWrites);
        }
      }
      // outs() << *L;
    }
    // reverse loop list such that loop A will print earlier than loop B
    std::reverse(looplist.begin(), looplist.end());
    std::reverse(looptripcount.begin(), looptripcount.end());
    std::reverse(LoopMemReads.begin(), LoopMemReads.end());
    std::reverse(LoopMemWrites.begin(), LoopMemWrites.end());
    adjacent_loop_same_tripcount = 0;
    nonadjacent_loop_same_tripcount = 0;
    sink_loop_same_tripcount = 0;
    hoist_loop_same_tripcount = 0;
    adjacent_loop_diff_tripcount = 0;
    nonadjacent_loop_diff_tripcount = 0;
    sink_loop_diff_tripcount = 0;
    hoist_loop_diff_tripcount = 0;

    // adjacent_loop = 0;
    // nonadjacent_loop = 0;
    // sink_loop = 0;
    // hoist_loop = 0;
    // int adjacentloop = 0;
    int adjacentloop = codemotion(looplist, looptripcount, LoopMemReads, LoopMemWrites, DI, DT, PDT, LI, F, SE);
    if(adjacentloop){
      errs() << "Module: " << F.getParent()->getName() << " Function: " << F.getName() << "\n";
      // outs() << "All fusible loop: " << adjacentloop << "\n";
      errs() << "adjacent_loop_same_tripcount: " << adjacent_loop_same_tripcount << "\n";
      errs() << "adjacent_loop_diff_tripcount: " << adjacent_loop_diff_tripcount << "\n";
      errs() << "nonadjacent_loop_same_tripcount: " << nonadjacent_loop_same_tripcount << "\n";
      errs() << "nonadjacent_loop_diff_tripcount: " << nonadjacent_loop_diff_tripcount << "\n";
      errs() << "sink_loop_same_tripcount: " << sink_loop_same_tripcount << "\n";
      errs() << "sink_loop_diff_tripcount: " << sink_loop_diff_tripcount << "\n";
      errs() << "hoist_loop_same_tripcount: " << hoist_loop_same_tripcount << "\n";
      errs() << "hoist_loop_diff_tripcount: " << hoist_loop_diff_tripcount << "\n";
    }
    FAM.clear();
    return PreservedAnalyses::none();
  }
