#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/IR/Dominators.h"
#include <vector>
#include <algorithm>
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Transforms/Utils/PeelLoop.h"
using namespace llvm;

namespace{
  int twoloop_iden=0;
  int twoloop_diff=0;

  // split the preheader
  void splitPreheader(Loop &loop, DominatorTree &DT, Function &F){
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
  }

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

    // // outs() << "Checking if this mem inst can be hoisted.\n";
    for (Instruction *NotHoistedInst : NotHoisting) {
      if (auto D = DI.depends(&I, NotHoistedInst, true)) {
        // Dependency is not read-before-write, write-before-read or
        // write-before-write
        if (D->isFlow() || D->isAnti() || D->isOutput()) {
          // // outs() << "Inst depends on an instruction in FC1's preheader that is not being hoisted.\n";
          return false;
        }
      }
    }

    for (Instruction *ReadInst : AMemReads) {
      if (auto D = DI.depends(ReadInst, &I, true)) {
        // Dependency is not read-before-write
        if (D->isAnti()) {
          // // outs() << "Inst depends on a read instruction in FC0.\n";
          return false;
        }
      }
    }

    for (Instruction *WriteInst : AMemWrites) {
      if (auto D = DI.depends(WriteInst, &I, true)) {
        // Dependency is not write-before-read or write-before-write
        if (D->isFlow() || D->isOutput()) {
          // // outs() << "Inst depends on a write instruction in FC0.\n";
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
          // // outs() << "Inst depends on a read instruction in FC1.\n";
          return false;
        }
      }
    }

    for (Instruction *WriteInst : BMemWrites) {
      if (auto D = DI.depends(&I, WriteInst, true)) {
        // Dependency is not write-before-write or read-before-write
        if (D->isOutput() || D->isAnti()) {
          // // outs() << "Inst depends on a write instruction in FC1.\n";
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
          // // outs() << "Inst: " << I << " may throw or won't return.\n";
          return false;
        }
        // // outs() << "Checking Inst: " << I << "\n";
        if (I.isAtomic() || I.isVolatile()) {
          // // outs() << "\tInstruction is volatile or atomic. Cannot move it.\n";
          return false;
        }
        if (canHoistInst(I, SafeToHoist, NotHoisting, Aloop, AMemReads, AMemWrites, DI, DT)) {
          SafeToHoist.push_back(&I);
          // // outs() << "Safe to hoist.\n";
        } else {
          // // outs() << "\tCould not hoist. Trying to sink...\n";
          NotHoisting.push_back(&I);
          if (canSinkInst(I, Bloop, BMemReads, BMemWrites, DI)) {
            SafeToSink.push_back(&I);
            // // outs() << "\tSafe to sink.\n";
          } else {
            // // outs() << "\tCould not sink.\n";
            return false;
          }
        }
      }
      // // outs() << "All preheader instructions could be sunk or hoisted!\n";
      return true;
    }

  void movePreheaderInsts(const Loop &Aloop, const Loop &Bloop,
    SmallVector<Instruction *, 4> &HoistInsts,
    SmallVector<Instruction *, 4> &SinkInsts) {
      BasicBlock *AloopPreheader = Aloop.getLoopPreheader();
      BasicBlock *AloopExitBlock = Aloop.getExitBlock();
      BasicBlock *BloopPreheader = Bloop.getLoopPreheader();
      BasicBlock *BloopExitBlock = Bloop.getExitBlock();
      // All preheader instructions except the branch must be hoisted
      // assert(HoistInsts.size() + SinkInsts.size() == BloopPreheader->size() - 1 &&
      //      "Attempting to sink and hoist preheader instructions, but not all "
      //      "the preheader instructions are accounted for.");
      assert(HoistInsts.size() + SinkInsts.size() == AloopExitBlock->size() - 1 &&
            "Attempting to sink and hoist preheader instructions, but not all "
            "the preheader instructions are accounted for.");
      if (!HoistInsts.empty()){
        // // outs() << "Hoisting: \n";
      }
      for (Instruction *I : HoistInsts){
        // // outs() << *I << "\n";
      }
      if (!SinkInsts.empty()){
        // // outs() << "Sinking: \n";
      }
      for (Instruction *I : SinkInsts){
        // // outs() << *I << "\n";
      }
      for (Instruction *I : HoistInsts) {
        // assert(I->getParent() == BloopPreheader);
        assert(I->getParent() == AloopExitBlock);
        I->moveBefore(*AloopPreheader,
                      AloopPreheader->getTerminator()->getIterator());
      }
      // insert instructions in reverse order to maintain dominance relationship
      for (Instruction *I : reverse(SinkInsts)) {
        // assert(I->getParent() == BloopPreheader);
        assert(I->getParent() == AloopExitBlock);
        I->moveBefore(*BloopExitBlock, BloopExitBlock->getFirstInsertionPt());
      }
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
      // // // outs() << "accessDiffIsPositive\n";
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
    // // // outs() << "DepChoice = " <<DepChoice << "\n";
    switch (DepChoice) {
      case 0:
        return accessDiffIsPositive(Aloop, Bloop, I0, I1, AnyDep, SE, DT);
      case 1:
        {
          auto DepResult = DI.depends(&I0, &I1, true);
          if (!DepResult)
            return true;
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
    // // // outs() << "Check if " << Aloop << " can be fused with " << Bloop << "\n";
    assert((Aloop.getLoopDepth() == Bloop.getLoopDepth()));
    // assert((DT.dominates(Aloop.getEntryBlock(), Bloop.getEntryBlock())));
    int FusionDependenceAnalysis = 2;
    for (Instruction *WriteL0 : ALoopMemWrites) {
      for (Instruction *WriteL1 : BLoopMemWrites)
        if (!dependencesAllowFusion(Aloop, Bloop, *WriteL0, *WriteL1,
          /* AnyDep */ false, FusionDependenceAnalysis, DI, 
          ALoopMemReads, ALoopMemWrites, BLoopMemReads, BLoopMemWrites, SE, DT)) {
          // // outs() << "In Aloopwrite :write !dependencesAllowFusion\n";
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
              // // outs() << "InvalidDependencies\n";
              return false;
            }

    return true;
  }

  int calculate_value(Loop &TargetLoop, int initialValue, int peeling_times, bool equalpredicate){
    BasicBlock *TargetHeader = TargetLoop.getHeader();
    BasicBlock *TargetLatch = TargetLoop.getLoopLatch();
    BasicBlock *incomingBlock;
    Value *incomingValue;
    int step;
    int clonedendvalue = initialValue;
    int originalstartvalue;
    for(Instruction &I : *TargetHeader){
      if(PHINode *phinode = dyn_cast<PHINode>(&I)){
        // // outs() << "Find phinode, NumIncomingValues = " << phinode->getNumIncomingValues() << "\n";
        for(int i=0; i<phinode->getNumIncomingValues(); i++){
          if(phinode->getIncomingBlock(i) == TargetLatch){
            incomingBlock = phinode->getIncomingBlock(i);
            incomingValue = phinode->getIncomingValue(i);
            // // outs() << "Value = " << *incomingValue << "\n";
            if(Instruction *Inst = dyn_cast<Instruction>(incomingValue)){
              if(ConstantInt *constInt = dyn_cast<ConstantInt>(Inst->getOperand(1))){
                APInt value = constInt->getValue();
                step = value.getSExtValue();
              }
              // // outs() << "Step = " << step<< "\n";
              switch(Inst->getOpcode()){
                case Instruction::Add:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue + step;
                  }
                  originalstartvalue = clonedendvalue + step;
                  break;
                case Instruction::Sub:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue - step;
                  }
                  originalstartvalue = clonedendvalue - step;
                  break;
                case Instruction::Mul:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue * step;
                  }
                  originalstartvalue = clonedendvalue * step;
                  break;
                case Instruction::UDiv:
                  assert(false && "operation not supported\n");
                  break;
                case Instruction::SDiv:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue / step;
                  }
                  originalstartvalue = clonedendvalue / step;
                  break;
                case Instruction::URem:
                  assert(false && "operation not supported\n");
                  break;
                case Instruction::SRem:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue % step;
                  }
                  originalstartvalue = clonedendvalue % step;
                  break;
                case Instruction::Shl:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue << step;
                  }
                  originalstartvalue = clonedendvalue << step;
                  break;
                case Instruction::LShr:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue >> step;
                  }
                  originalstartvalue = clonedendvalue >> step;
                  break;
                case Instruction::AShr:
                  assert(false && "operation not supported\n");
                  break;
                case Instruction::And:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue && step;
                  }
                  originalstartvalue = clonedendvalue && step;
                  break;
                case Instruction::Or:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue || step;
                  }
                  originalstartvalue = clonedendvalue || step;
                  break;
                case Instruction::Xor:
                  for(int i=0; i<peeling_times-1; i++){
                    clonedendvalue = clonedendvalue ^ step;
                  }
                  originalstartvalue = clonedendvalue ^ step;
                  break;
                default:
                  assert(false && "operation not supported\n");
              }
            }
            else{
              assert(false && "Error: is not an instruction\n");
            }
            break;
          }
        }
      }
      break;
    }
    // // outs() << "endvalue = " << clonedendvalue << "\n";
    if(equalpredicate){
      return clonedendvalue;
    }
    return originalstartvalue;
  }

  Loop* cloneLoop(Loop &loop, LoopInfo &LI, DominatorTree &DT, Function &F, bool peelL0){
    ValueToValueMapTy VMap;
    BasicBlock *Loopheader = loop.getHeader();
    BasicBlock *Preheader = loop.getLoopPreheader();
    BasicBlock *Exitblock = loop.getExitBlock();
    BasicBlock *Preentry = Preheader->getUniquePredecessor();
    // // outs() << *Preentry;
    if(!Preentry){
      assert("the loop should have only one preheader");
    }
    // clone a loop with preheader
    SmallVector<BasicBlock *, 8> Blocks;
    Loop *ClonedLoop = cloneLoopWithPreheader(Preheader, Preheader, &loop, VMap, "", &LI, &DT, Blocks);
    VMap[Exitblock] = Preheader; // chain: cloned loop -> original loop
    remapInstructionsInBlocks(Blocks, VMap);
    BasicBlock *ClonedPreheader = ClonedLoop->getLoopPreheader();
    // Preentry setSuccessor to cloned loop
    Instruction *PreentryTermInst = Preentry->getTerminator();
    BranchInst *PreentryBr = dyn_cast<BranchInst>(PreentryTermInst);
    if(PreentryBr->isConditional()){
      assert("error: preentry branch is conditional branch\n");
    }
    if(peelL0){
      PreentryBr->setSuccessor(0, ClonedPreheader);
    }
    else{
      PreentryBr->setSuccessor(1, ClonedPreheader);
    }
    return ClonedLoop;
  }

  void PeelL0(Loop &loop, Loop &ClonedLoop, int peeling_times){
    // // outs() << "Analyses Cloned Loop\n";
    BasicBlock *ClonedPreheader = ClonedLoop.getLoopPreheader();
    BasicBlock *preheader = loop.getLoopPreheader();
    BasicBlock *ClonedHeader = ClonedLoop.getHeader();
    BasicBlock *header = loop.getHeader();
    BasicBlock *incomingBlock;
    Value *incomingValue;
    int initialValue;
    // Get the inital index of cloned loop
    for(Instruction &I : *ClonedHeader){
      if(PHINode *phinode = dyn_cast<PHINode>(&I)){
        // // outs() << "Find phinode, NumIncomingValues = " << phinode->getNumIncomingValues() << "\n";
        for(int i=0; i<phinode->getNumIncomingValues(); i++){
          if(phinode->getIncomingBlock(i) == ClonedPreheader){
            incomingBlock = phinode->getIncomingBlock(i);
            incomingValue = phinode->getIncomingValue(i);
            if(ConstantInt *constInt = dyn_cast<ConstantInt>(incomingValue)){
              // check the initial index
              APInt value = constInt->getValue();
              initialValue = value.getSExtValue();
              // // outs() << "The initial index is a constant: " << initialValue << "\n";
            }
            else{
              // // outs() << "Not a constant\n";
            }
            break;
          }
        }
      }
      break;
    }
    bool existequal = false;
    // find the predicate of the compare instruction
    for(Instruction &I : *ClonedHeader){
      if(BranchInst *BrInst = dyn_cast<BranchInst>(&I)){
        if(BrInst->isConditional()){
          Value *ConditionValue = BrInst->getCondition();
          if (ICmpInst *CmpInst = dyn_cast<ICmpInst>(ConditionValue)) {
            // // outs() << "ICmp Instruction: " << *CmpInst << "\n";
            if (CmpInst->getPredicate() == CmpInst::Predicate::ICMP_SLE
              || CmpInst->getPredicate() == CmpInst::Predicate::ICMP_SGE
              || CmpInst->getPredicate() == CmpInst::Predicate::ICMP_ULE
              || CmpInst->getPredicate() == CmpInst::Predicate::ICMP_UGE) {
              // // outs() << "Found equal comparison:\n";
              // // outs() << "\n";
              existequal = true;
            }
          }
        }
        break;
      }
    }
    int clonedendvalue = calculate_value(ClonedLoop, initialValue, peeling_times, existequal);
    int originalstartvalue = calculate_value(ClonedLoop, initialValue, peeling_times, false);
    // Set the condition of the cloned header
    for(Instruction &I : *ClonedHeader){
      if(BranchInst *BrInst = dyn_cast<BranchInst>(&I)){
        if(BrInst->isConditional()){
          Value *ConditionValue = BrInst->getCondition();
          if (ICmpInst *CmpInst = dyn_cast<ICmpInst>(ConditionValue)) {
            // // outs() << "Original ICmp Instruction: " << *CmpInst << "\n";
            // update the icmp value (i.e. the loop iteration)
            CmpInst->setOperand(1, ConstantInt::get(CmpInst->getOperand(1)->getType(), clonedendvalue));
            // // // outs() << *(CmpInst->getOperand(1)->getType()) << "\n";
            // // outs() << "Modified ICmp Instruction: " << *CmpInst << "\n";
          }
        }
        break;
      }
    }
    // Set the condition of the original header
    for(Instruction &I : *header){
      if(PHINode *phinode = dyn_cast<PHINode>(&I)){
        // // outs() << "Find phinode, NumIncomingValues = " << phinode->getNumIncomingValues() << "\n";
        assert(phinode->getNumIncomingValues() != 1 && "loop header phinode != 1");
        for(int i=0; i<phinode->getNumIncomingValues(); i++){
          if(phinode->getIncomingBlock(i) == preheader){
            incomingBlock = phinode->getIncomingBlock(i);
            incomingValue = phinode->getIncomingValue(i);
            if(ConstantInt *constInt = dyn_cast<ConstantInt>(incomingValue)){
              // check the initial index
              APInt value = constInt->getValue();
              int intValue = value.getSExtValue();
              // // outs() << "The initial index is a constant: " << intValue << "\n";
              // // outs() << "Original Phi Instruction: " << *phinode << "\n";
              phinode->setIncomingValue(i, ConstantInt::get(constInt->getType(), originalstartvalue));
              // // outs() << "Modified Phi Instruction: " << *phinode << "\n";
            }
            else{
              // // outs() << "not a constantInt\n";
            }
            break;
          }
        }
        break;
      }
    }
  }

  void PeelL1(Loop &loop, Loop &ClonedLoop, int peeling_times){
    // // outs() << "Peel L1: Analyses Cloned Loop\n";
    BasicBlock *ClonedPreheader = ClonedLoop.getLoopPreheader();
    BasicBlock *preheader = loop.getLoopPreheader();
    BasicBlock *ClonedHeader = ClonedLoop.getHeader();
    BasicBlock *header = loop.getHeader();
    BasicBlock *incomingBlock;
    Value *incomingValue;
    int initialValue;
    // Get the inital index of cloned loop
    for(Instruction &I : *ClonedHeader){
      if(PHINode *phinode = dyn_cast<PHINode>(&I)){
        for(int i=0; i<phinode->getNumIncomingValues(); i++){
          if(phinode->getIncomingBlock(i) == ClonedPreheader){
            incomingBlock = phinode->getIncomingBlock(i);
            incomingValue = phinode->getIncomingValue(i);
            if(ConstantInt *constInt = dyn_cast<ConstantInt>(incomingValue)){
              // check the initial index
              APInt value = constInt->getValue();
              initialValue = value.getSExtValue();
              // // outs() << "The initial index is a constant: " << initialValue << "\n";
            }
            else{
              // // outs() << "Not a constant\n";
            }
            break;
          }
        }
      }
      break;
    }
    bool existequal = false;
    // find the predicate of the compare instruction
    for(Instruction &I : *ClonedHeader){
      if(BranchInst *BrInst = dyn_cast<BranchInst>(&I)){
        if(BrInst->isConditional()){
          Value *ConditionValue = BrInst->getCondition();
          if (ICmpInst *CmpInst = dyn_cast<ICmpInst>(ConditionValue)) {
            // // outs() << "ICmp Instruction: " << *CmpInst << "\n";
            if (CmpInst->getPredicate() == CmpInst::Predicate::ICMP_SLE
              || CmpInst->getPredicate() == CmpInst::Predicate::ICMP_SGE
              || CmpInst->getPredicate() == CmpInst::Predicate::ICMP_ULE
              || CmpInst->getPredicate() == CmpInst::Predicate::ICMP_UGE) {
              // // outs() << "Found equal comparison:\n";
              // // outs() << "\n";
              existequal = true;
            }
          }
        }
        break;
      }
    }
    int clonedendvalue = calculate_value(ClonedLoop, initialValue, peeling_times, existequal);
    int originalstartvalue = calculate_value(ClonedLoop, initialValue, peeling_times, false);
    // Set the condition of the cloned header
    for(Instruction &I : *ClonedHeader){
      if(BranchInst *BrInst = dyn_cast<BranchInst>(&I)){
        if(BrInst->isConditional()){
          Value *ConditionValue = BrInst->getCondition();
          if (ICmpInst *CmpInst = dyn_cast<ICmpInst>(ConditionValue)) {
            // // outs() << "Original ICmp Instruction: " << *CmpInst << "\n";
            // update the icmp value (i.e. the loop iteration)
            CmpInst->setOperand(1, ConstantInt::get(CmpInst->getOperand(1)->getType(), clonedendvalue));
            // // // outs() << *(CmpInst->getOperand(1)->getType()) << "\n";
            // // outs() << "Modified ICmp Instruction: " << *CmpInst << "\n";
          }
        }
        break;
      }
    }
    // Set the condition of the original header
    for(Instruction &I : *header){
      if(PHINode *phinode = dyn_cast<PHINode>(&I)){
        // // outs() << "Find phinode, NumIncomingValues = " << phinode->getNumIncomingValues() << "\n";
        assert(phinode->getNumIncomingValues() != 1 && "loop header phinode != 1");
        for(int i=0; i<phinode->getNumIncomingValues(); i++){
          if(phinode->getIncomingBlock(i) == preheader){
            incomingBlock = phinode->getIncomingBlock(i);
            incomingValue = phinode->getIncomingValue(i);
            if(ConstantInt *constInt = dyn_cast<ConstantInt>(incomingValue)){
              // check the initial index
              APInt value = constInt->getValue();
              int intValue = value.getSExtValue();
              // // outs() << "The initial index is a constant: " << intValue << "\n";
              // // outs() << "Original Phi Instruction: " << *phinode << "\n";
              phinode->setIncomingValue(i, ConstantInt::get(constInt->getType(), originalstartvalue));
              // // outs() << "Modified Phi Instruction: " << *phinode << "\n";
            }
            else{
              // // outs() << "not a constantInt\n";
            }
            break;
          }
        }
        break;
      }
    }
  }

  bool Checkshareindex(Loop &L0, Loop &L1){
    // check if two loop can share the same index
    // condition 1: start value is the same
    // condition 2: step is the same
    // // outs() << "check if two loop can share the same index...\n";
    BasicBlock *L0Preheader = L0.getLoopPreheader();
    BasicBlock *L1Preheader = L1.getLoopPreheader();
    BasicBlock *L0Header = L0.getHeader();
    BasicBlock *L1Header = L1.getHeader();
    BasicBlock *L0Latch = L0.getLoopLatch();
    BasicBlock *L1Latch = L1.getLoopLatch();
    BasicBlock *incomingBlock;
    Value *incomingValue;
    Instruction *Terminator;
    int L0index, L1index;
    Type *L0indexType;
    Type *L1indexType;
    // check two start values
    // L0 start value
    Terminator = L0Header->getTerminator();
    // // outs() << *L0Header;
    // // outs() << *Terminator<<"\n";
    PHINode* L0indexphinode;
    if(BranchInst* Br = dyn_cast<BranchInst>(Terminator)){
      if(!Br->isConditional()){
        return false;
      }
      // assert(Br->isConditional() && "Branch instruction is not a conditional branch\n");
      // // outs() << *(dyn_cast<Instruction>(Br->getOperand(0))->getOperand(0)) << "\n";
      L0indexphinode = dyn_cast<PHINode>(dyn_cast<Instruction>(Br->getOperand(0))->getOperand(0));
      if(!L0indexphinode){
        return false;
      }
      L0indexType = L0indexphinode->getType();
      // assert(L0indexphinode && "phinode null\n");
    }
    // // outs() << *L0Preheader<<"\n";
    for(int i=0; i<L0indexphinode->getNumIncomingValues(); i++){
      if(L0indexphinode->getIncomingBlock(i) == L0Preheader){
        incomingBlock = L0indexphinode->getIncomingBlock(i);
        incomingValue = L0indexphinode->getIncomingValue(i);
        // // outs() << *incomingBlock<<"\n";
        // // outs() << *incomingValue<<"\n";
        if(ConstantInt *constInt = dyn_cast<ConstantInt>(incomingValue)){
          // check the initial index
          APInt value = constInt->getValue();
          L0index = value.getSExtValue();
          }
        else{
          // outs() << "Not a constant\n";
          return false;
        }
        break;
      }
    }
    // // outs() << L0index<<"\n";
    // L1 start value
    Terminator = L1Header->getTerminator();
    PHINode* L1indexphinode;
    if(BranchInst* Br = dyn_cast<BranchInst>(Terminator)){
      if(!Br->isConditional()){
        return false;
      }
      // assert(Br->isConditional() && "Branch instruction is not a conditional branch\n");
      L1indexphinode = dyn_cast<PHINode>(dyn_cast<Instruction>(Br->getOperand(0))->getOperand(0));
      if(!L1indexphinode){
        return false;
      }
      L1indexType = L1indexphinode->getType();
      // assert(L1indexphinode && "phinode null\n");
    }
    for(int i=0; i<L1indexphinode->getNumIncomingValues(); i++){
      if(L1indexphinode->getIncomingBlock(i) == L1Preheader){
        incomingBlock = L1indexphinode->getIncomingBlock(i);
        incomingValue = L1indexphinode->getIncomingValue(i);
        if(ConstantInt *constInt = dyn_cast<ConstantInt>(incomingValue)){
          // check the initial index
          APInt value = constInt->getValue();
          L1index = value.getSExtValue();
          }
        else{
          assert(false && "Not a constant\n");
        }
        break;
      }
    }
    // // outs() << "L0 index = " << L0index << "\t L1 index = " << L1index << "\n";
    if(L0indexType != L1indexType){
      return false;
    }
    if(L0index != L1index){
      // outs() << "L0 index = " << L0index << "\t L1 index = " << L1index << "\n";
      return false;
    }
    int L0step, L1step;
    int L0Op, L1Op;
    // check two step values and operations
    // L0 step and operation
    for(int i=0; i<L0indexphinode->getNumIncomingValues(); i++){
      if(L0indexphinode->getIncomingBlock(i) == L0Latch){
        incomingBlock = L0indexphinode->getIncomingBlock(i);
        incomingValue = L0indexphinode->getIncomingValue(i);
        if(Instruction *L0Oper = dyn_cast<Instruction>(incomingValue)){
          if(ConstantInt *constInt = dyn_cast<ConstantInt>(L0Oper->getOperand(1))){
            APInt value = constInt->getValue();
            L0step = value.getSExtValue();
            L0Op = L0Oper->getOpcode();
          }
        }
        else{
          return false;
          // assert(false && "Error: is not an instruction\n");
        }
        break;
      }
    }
    // L1 step and operation
    for(int i=0; i<L1indexphinode->getNumIncomingValues(); i++){
      if(L1indexphinode->getIncomingBlock(i) == L1Latch){
        incomingBlock = L1indexphinode->getIncomingBlock(i);
        incomingValue = L1indexphinode->getIncomingValue(i);
        if(Instruction *L1Oper = dyn_cast<Instruction>(incomingValue)){
          if(ConstantInt *constInt = dyn_cast<ConstantInt>(L1Oper->getOperand(1))){
            APInt value = constInt->getValue();
            L1step = value.getSExtValue();
            L1Op = L1Oper->getOpcode();
          }
        }
        else{
          return false;
          // assert(false && "Error: is not an instruction\n");
        }
        break;
      }
    }
    // // outs() << "L0 step = " << L0step << "\t L1 step = " << L1step << "\n";
    if(L0step != L1step){
      return false;
    }
    // // outs() << "L0 Op = " << L0Op << "\t L1 Op = " << L1Op << "\n";
    if(L0Op != L1Op){
      return false;
    }
    return true;
  }

  void shareindex(Loop &L0, Loop &L1){
    BasicBlock *L0Preheader = L0.getLoopPreheader();
    BasicBlock *L1Preheader = L1.getLoopPreheader();
    BasicBlock *L0Header = L0.getHeader();
    BasicBlock *L1Header = L1.getHeader();
    BasicBlock *L0Latch = L0.getLoopLatch();
    BasicBlock *L1Latch = L1.getLoopLatch();
    BasicBlock *incomingBlock;
    Value *incomingValue;
    // // outs() << "shareindex\n";
    // BB setName
    for(BasicBlock *BB : L0.blocks()){
      Twine Name = Twine(BB->getName()) + "_fused";
      BB->setName(Name.str());
    }
    for(BasicBlock *BB : L1.blocks()){
      Twine Name = Twine(BB->getName()) + "_fused";
      BB->setName(Name.str());
    }
    // Twine Name = Twine(L0Preheader->getName()) + "_fused";
    // L0Preheader->setName(Name.str());
    // Twine Name1 = Twine(L1Latch->getName()) + "_fused";
    // L1Latch->setName(Name1.str());
  }

  void Swaplooporder(Loop &ClonedLoop, Loop &L0, Loop &L1, DominatorTree &DT, Function &F){
    // // outs() << "swap loop:\n";
    splitPreheader(L0, DT, F);
    splitPreheader(L1, DT, F);
    BasicBlock *L0Header = L0.getHeader();
    BasicBlock *L0Preheader = L0.getLoopPreheader();
    BasicBlock *L0Exit = L0.getExitBlock();
    BasicBlock *L0PreheaderPredeccessor = L0Preheader->getUniquePredecessor();
    BasicBlock *L1Preheader = L1.getLoopPreheader();
    BasicBlock *L1Header = L1.getHeader();
    BasicBlock *L1Exit = L1.getExitBlock();
    if(!L0PreheaderPredeccessor){
      // return false;
      assert(false && "L0 Preheader Predecessor is not unique\n");
    }
    // Original: L0 Preheader Predeccessor -> L0 Preheader -> L0 Header -> L0 Exit -> L1 Preheader -> L1 Header -> L1 Exit
    // New V2:   L0 Preheader Predeccessor -> L1 Preheader -> L1 Header -> L0 Exit -> L0 Preheader -> L0 Header -> L1 Exit
    // TODO: split L0 Preheader, split L1 Preheader(i.e. L0 exit and L1 Preheader are not the same BB).

    // Change: L0 Preheader Predeccessor branch to L1 Preheader
    // L0 Preheader Predeccessor is cloned loop exit block
    Instruction *Terminator = L0PreheaderPredeccessor->getTerminator();
    BranchInst *Br = dyn_cast<BranchInst>(Terminator);
    // // // outs() << "L0PreheaderPredeccessor: " << *Br << Terminator->getNumSuccessors() << "\n";
    int successorindex = -1;
    for(int i=0; i<Terminator->getNumSuccessors(); i++){
      if(Br->getSuccessor(i) == L0Preheader){
        successorindex = i;
        break;
      }
    }
    assert( (successorindex>=0) && "successor index error\n");

    L1Preheader->moveBefore(L0Preheader);
    for(BasicBlock *BB : L1.blocks()){
      BB->moveBefore(L0Preheader);
    }
    L0Exit->moveBefore(L0Preheader);
    Br->setSuccessor(successorindex, L1Preheader);
    // // // outs() << "L1 Preheader:" << *L1Preheader << "\n";

    // Change: L1 Header branch to L0 Exit Block
    Terminator = L1Header->getTerminator();
    Br = dyn_cast<BranchInst>(Terminator);
    // // // outs() << "L1Header: " << *Br << Terminator->getNumSuccessors() << "\n";
    successorindex = -1;
    for(int i=0; i<Terminator->getNumSuccessors(); i++){
      if(Br->getSuccessor(i) == L1Exit){
        successorindex = i;
        break;
      }
    }
    assert( (successorindex>=0) && "successor index error\n");

    Br->setSuccessor(successorindex, L0Exit);

    // Change: L0 Exit Block branch to L0 Preheader
    Terminator = L0Exit->getTerminator();
    Br = dyn_cast<BranchInst>(Terminator);
    // // // outs() << "L0Exit: " << *Br << Terminator->getNumSuccessors() << "\n";
    successorindex = -1;
    for(int i=0; i<Terminator->getNumSuccessors(); i++){
      if(Br->getSuccessor(i) == L1Preheader){
        successorindex = i;
        break;
      }
    }
    assert( (successorindex>=0) && "successor index error\n");

    Br->setSuccessor(successorindex, L0Preheader);

    // Change: L0 Header branch to L1 Exit Block
    Terminator = L0Header->getTerminator();
    Br = dyn_cast<BranchInst>(Terminator);
    // // // outs() << "L0Header: " << *Br << Terminator->getNumSuccessors() << "\n";
    successorindex = -1;
    for(int i=0; i<Terminator->getNumSuccessors(); i++){
      if(Br->getSuccessor(i) == L0Exit){
        successorindex = i;
        break;
      }
    }
    assert( (successorindex>=0) && "successor index error\n");

    Br->setSuccessor(successorindex, L1Exit);
    // TODO: merge L0PreheaderPredeccessor(i.e Cloned Loop Exit Block) and L0 Preheader
    SmallVector<Instruction *, 16> L0PreheaderPredeccessor_Instruction;
    for(Instruction &I : *L0PreheaderPredeccessor){
      if(&I == L0PreheaderPredeccessor->getTerminator()){
        continue;
      }
      L0PreheaderPredeccessor_Instruction.push_back(&I);
    }
    for(Instruction *I : reverse(L0PreheaderPredeccessor_Instruction)){
      assert(I->getParent() == L0PreheaderPredeccessor);
      I->moveBefore(*L1Preheader, L1Preheader->getFirstInsertionPt());
    }

    Terminator = ClonedLoop.getHeader()->getTerminator();
    Br = dyn_cast<BranchInst>(Terminator);
    successorindex = -1;
    for(int i=0; i<Terminator->getNumSuccessors(); i++){
      if(Br->getSuccessor(i) == L0PreheaderPredeccessor){
        successorindex = i;
        break;
      }
    }
    assert( (successorindex>=0) && "successor index error\n");
    Br->setSuccessor(successorindex, L1Preheader);
    L0PreheaderPredeccessor->eraseFromParent();
    // TODO: merge L0 Exit Block and L0 Preheader
    SmallVector<Instruction *, 16> L0Exit_Instruction;
    for(Instruction &I : *L0Exit){
      if(&I == L0Exit->getTerminator()){
        continue;
      }
      L0Exit_Instruction.push_back(&I);
    }
    for(Instruction *I : reverse(L0Exit_Instruction)){
      assert(I->getParent() == L1Header);
      I->moveBefore(*L0Preheader, L0Preheader->getFirstInsertionPt());
    }
    Terminator = L1.getHeader()->getTerminator();
    Br = dyn_cast<BranchInst>(Terminator);
    successorindex = -1;
    for(int i=0; i<Terminator->getNumSuccessors(); i++){
      if(Br->getSuccessor(i) == L0Exit){
        successorindex = i;
        break;
      }
    }
    assert( (successorindex>=0) && "successor index error\n");
    Br->setSuccessor(successorindex, L0Preheader);
    L0Exit->eraseFromParent();
  }

  // case2:
  // the exit block of loop A if the preheader of loop B
  int findtwoloop(const SmallVector<Loop *, 4> &looplist, const SmallVector<const SCEV*, 4> &looptripcount,
  SmallVector<SmallVector<Instruction *, 16>> LoopMemReads, SmallVector<SmallVector<Instruction *, 16>> LoopMemWrites,
  DependenceInfo &DI, DominatorTree &DT, ScalarEvolution &SE, Function &F, LoopInfo &LI){
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
    int twoloop = 0;
    // // outs() << looplist_size << "\n";

    for(int i=0; i<looplist_size; i++){
      if(already_fused_loop[i]){
        continue;
      }
      for(int j=0; j<looplist_size; j++){
        if(i==j){
          continue;
        }
        if(already_fused_loop[j]){
          continue;
        }
      
        BasicBlock *Aheader = looplist[i]->getHeader();
        BasicBlock *Aexit = looplist[i]->getExitBlock();
        BasicBlock *Alatch = looplist[i]->getLoopLatch();
        BasicBlock *Bheader = looplist[j]->getHeader();
        BasicBlock *Bexit = looplist[j]->getExitBlock();
        BasicBlock *Blatch = looplist[j]->getLoopLatch();
        if(!Aexit || !Bexit){
          // // outs() << "exit block is null, maybe break\n";
          continue;
        }
        if(!Alatch || !Blatch){
          // // outs() << "latch is null, maybe continue";
          continue;
        }
        unsigned ANumBlocks = looplist[i]->getNumBlocks();
        BasicBlock *AExitBlock = looplist[i]->getExitBlock();
        BasicBlock *BPreheader = looplist[j]->getLoopPreheader();
        if(!AExitBlock || !BPreheader){
          continue;
        }

        SmallVector<Instruction *, 4> Aloopinstruction;
        SmallVector<Instruction *, 4> Bloopinstruction;

        if(AExitBlock == BPreheader){

          // collect the instruction of loop A
          for(BasicBlock *BB : looplist[i]->blocks()){
            for(Instruction &I : *BB){
              Aloopinstruction.push_back(&I);
              // // outs() << I << "\n";
            }
          }
          // collect the instruction of loop B
          for(BasicBlock *BB : looplist[j]->blocks()){
            for(Instruction &I : *BB){
              Bloopinstruction.push_back(&I);
              // // outs() << I << "\n";
            }
          }
          if(!dependencesAllowFusion(*looplist[i], *looplist[j], DI,
            LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], SE, DT)){
            // // outs() << "Memory dependencies do not allow fusion!\n";
            continue;
          }
          // // outs() << "Pass the dependencesAllowFusion check\n";
          // check if there is a data dependency between loop A exit block and loop A instruction
          SmallVector<Instruction *, 4> SafeToHoist;
          SmallVector<Instruction *, 4> SafeToSink;

          // data dependency analysis
          if(collectMovablePreheaderInsts(*looplist[i], *looplist[j], SafeToHoist, SafeToSink,
          LoopMemReads[i], LoopMemWrites[i], LoopMemReads[j], LoopMemWrites[j], DI, DT)){
            const SCEV *ACount = looptripcount[i];
            const SCEV *BCount = looptripcount[j];
            // // outs() << "\tTrip counts: " << *ACount << " & " << *BCount << " are " << (ACount == BCount ? "identical" : "different") << "\n";
            unsigned L0count = 0;
            unsigned L1count = 0;
            if(auto *SCEV0 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[i])){
              L0count = SCEV0->getAPInt().getZExtValue();
            }
            else{
              // outs() << "L0count is null\n";
            }
            if(auto *SCEV1 = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[j])){
              L1count = SCEV1->getAPInt().getZExtValue();
            }
            else{
              // outs() << "L1count is null\n";
            }
            // unsigned L0count = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[i])->getAPInt().getZExtValue();
            // unsigned L1count = llvm::dyn_cast<llvm::SCEVConstant>(looptripcount[i+1])->getAPInt().getZExtValue();
            // // outs() << "L0 trip count = " << L0count << ", L1 trip count = " << L1count << "\n";
            if(L0count == 0 || L1count == 0){
              // // outs() << "L0 trip count or L1 trip count = 0, cannot fused\n";
              continue;
            }
            twoloop++;
            if(ACount==BCount){
              twoloop_iden++;
              // // outs() << "trip count is the same\n";
            }
            else{
              twoloop_diff++;
              // // outs() << "trip count is not the same, peeling loop...\n";
            }
            int peeling_times = L0count - L1count;
            if(peeling_times > 0){ // L0 trip count > L1 trip count, peel L0
              // // outs() << "L0 peeling " << peeling_times << " times\n";
              // split L0 preheader
              splitPreheader(*looplist[i], DT, F);
              // clone L0
              Loop *ClonedLoop = cloneLoop(*looplist[i], LI, DT, F, true);
              // // outs() << "Cloned Loop: "<< *ClonedLoop;
              // // outs() << "Original Loop: " << *looplist[i];
              PeelL0(*looplist[i], *ClonedLoop, L1count);
              // hoist and sink the instructions
              movePreheaderInsts(*looplist[i], *looplist[j], SafeToHoist, SafeToSink);
              // TODO: merge pre-entry(i.e. entry basic block) and cloned loop preheader
              SmallVector<Instruction *, 16> clonedpreheader_Instruction;
              BasicBlock *clonedpreheader = ClonedLoop->getLoopPreheader();
              BasicBlock *clonedheader = ClonedLoop->getHeader();
              BasicBlock *preentry = clonedpreheader->getUniquePredecessor();
              assert(preentry && "GetUniquePredecessor() failed\n");
              for(Instruction &I : *clonedpreheader){
                if(&I == clonedpreheader->getTerminator()){
                  continue;
                }
                clonedpreheader_Instruction.push_back(&I);
              }
              for (Instruction *I : clonedpreheader_Instruction) {
                assert(I->getParent() == clonedpreheader);
                I->moveBefore(*preentry,
                              preentry->getTerminator()->getIterator());
              }
              Instruction *Terminator = preentry->getTerminator();
              BranchInst *Br = dyn_cast<BranchInst>(Terminator);
              clonedheader->replacePhiUsesWith(clonedpreheader, preentry);
              Br->setSuccessor(0, clonedheader);
              clonedpreheader->eraseFromParent();
              DT.recalculate(F);
              // Merge pre-entry(i.e. entry basic block) and cloned loop preheader complete
              
              if(Checkshareindex(*ClonedLoop, *looplist[j])){
                // // outs() << "unified index:\n";
                Swaplooporder(*ClonedLoop, *looplist[i], *looplist[j], DT, F);
                // shareindex(*ClonedLoop, *looplist[i+1]);
              }
              // Optimizepeeling();

              // check original loop and cloned loop
              // hoist and sink the instructions
              // movePreheaderInsts(*looplist[i], *looplist[i+1], SafeToHoist, SafeToSink);
            }
            else if(peeling_times < 0){ // L1 trip count > L0 trip count, peel L1
              // check original loop and cloned loop
              // hoist and sink the instructions
              movePreheaderInsts(*looplist[i], *looplist[j], SafeToHoist, SafeToSink);
              peeling_times = (-1) * peeling_times;
              // // outs() << "L1 peeling " << peeling_times << " times\n";
              // split L1 preheader
              // splitPreheader(*looplist[i+1], DT, F);
              // clone L1
              Loop *ClonedLoop = cloneLoop(*looplist[j], LI, DT, F, false);
              PeelL1(*looplist[j], *ClonedLoop, L0count);
              // check original loop and cloned loop
              if(Checkshareindex(*looplist[i], *ClonedLoop)){
                // // outs() << "unified index:\n";
                // shareindex(*looplist[i], *ClonedLoop);
              }
              else{
                // // outs() << "cannot share index\n";
              }
              // Optimizepeeling();
            }
            else{ // L0 trip count = L1 trip count
              if(Checkshareindex(*looplist[i], *looplist[j])){
                // shareindex(*looplist[i], *looplist[i+1]);
              }
            }
            already_fused_loop[i] = true;
            already_fused_loop[j] = true;
            break;
          }
          else{
            continue;
            // outs() << "Data dependency analysis not passed, cannot be fused\n";
          }
        }
      }
    }
    return twoloop;
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
}

PreservedAnalyses PeelLoopPass::run(Function &F, FunctionAnalysisManager &FAM) {
  FAM.clear();
  LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = FAM.getResult<ScalarEvolutionAnalysis>(F);
  DependenceInfo &DI = FAM.getResult<DependenceAnalysis>(F);
  DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
  SmallVector<Loop *, 4> looplist;
  SmallVector<const SCEV*, 4> looptripcount;
  SmallVector<SmallVector<Instruction *, 16>> LoopMemReads;
  SmallVector<SmallVector<Instruction *, 16>> LoopMemWrites;
  for(Loop *L : LI){
    if(!isValidLoop(L)){
      // // outs() << "invalid\n";
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
    
  }
  // reverse loop list such that loop A will print earlier than loop B
  std::reverse(looplist.begin(), looplist.end());
  std::reverse(looptripcount.begin(), looptripcount.end());
  std::reverse(LoopMemReads.begin(), LoopMemReads.end());
  std::reverse(LoopMemWrites.begin(), LoopMemWrites.end());
  // int num_twoloop = 0;
  // // outs() << "Module: " << F.getParent()->getName() << " Function: " << F.getName() << "\n";
  twoloop_iden = 0;
  twoloop_diff = 0;
  int num_twoloop = findtwoloop(looplist, looptripcount, LoopMemReads, LoopMemWrites, DI, DT, SE, F, LI);
  if(num_twoloop){
    errs() << "Module: " << F.getParent()->getName() << " Function: " << F.getName() << "\n";
    // // outs() << "Number of two loop = " << num_twoloop << "\n";
    errs() << "Twoloopidentical: " << twoloop_iden << "\n";
    errs() << "Twoloopdifferent: " << twoloop_diff << "\n";
  }
  FAM.clear();
  return PreservedAnalyses::none();
}