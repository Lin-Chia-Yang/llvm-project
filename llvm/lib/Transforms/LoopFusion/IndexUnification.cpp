#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/IR/Dominators.h"
#include <vector>
#include <algorithm>
#include <string>
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Transforms/Utils/IndexUnification.h"
using namespace llvm;

namespace{
  int sharesameindex = 0;
  SmallVector<Instruction *, 16> InstToRemove;
  void GetUserAndErase(Instruction *I){
    // outs() << "Check User: "<< *I << "\n";
    if(!I->getNumUses()){
      return;
    }
    for(User *UI : I->users()){
      if(!dyn_cast<PHINode>(UI)){
        // outs() << "Find User" << *UI << "\n";
        Instruction *EraseInst = dyn_cast<Instruction>(UI);
        GetUserAndErase(EraseInst);
        // outs() << "Push" << *EraseInst << "\n";
        InstToRemove.push_back(EraseInst);
        // outs() << "Return\n";
      }
    }
    return;
  }

  bool findindexname(PHINode *phi){
    Twine index_name = Twine(phi->getName());
    Twine unificationname = "_fuseindex";
    std::string str1 = index_name.str();
    std::string str2 = unificationname.str();
    if(str1.find(str2) != std::string::npos){
      return true;
    }
    return false;
  }
  
  void optimizeindex(Loop &L){
    BasicBlock *Header = L.getHeader();
    BasicBlock *Latch = L.getLoopLatch();
    SmallVector<PHINode *, 4> phiindex;

    // push back phinode
    for(PHINode &phi : Header->phis()){
      if(findindexname(&phi)){
        phiindex.push_back(&phi);
      }
    }

    // check the branch and compare instrucion in latch
    // outs() << "Header:" << *Header;
    // outs() << "Latch:" << *Latch;
    BranchInst *BrInst = dyn_cast<BranchInst>(Latch->getTerminator());
    if(!BrInst->isConditional()){
      return;
    }
    Instruction *CmpInst = dyn_cast<Instruction>(BrInst->getCondition());
    Value *CorrectOperand = CmpInst->getOperand(0);
    if(!CorrectOperand){
      outs() << "stop index unification\n";
      return;
    }
    // outs() << "CorrectOpernad: " << *CorrectOperand << "\n";
    
    // find index
    // CorrectIndex is the share index
    // OtherIndices need to be eliminated
    Instruction *CorrectIndex;
    SmallVector <Instruction *, 16> OtherIndex;
    for(int i=0; i<phiindex.size(); i++){
      for(int j=0; j<phiindex[i]->getNumIncomingValues(); j++){
        if(phiindex[i]->getIncomingBlock(j) == Latch){
          // outs() << "getIncomingValue: ";
          // outs() << *phiindex[i]->getIncomingValue(j) << "\n";
          if(phiindex[i]->getIncomingValue(j) == CorrectOperand){
            // outs() << "correct index: " << *(phiindex[i]) << "\n";
            CorrectIndex = dyn_cast<Instruction>(phiindex[i]);
          }
          else{
            // outs() << "other index: " << *(phiindex[i]) << "\n";
            OtherIndex.push_back(phiindex[i]);
          }
          break;
        }
      }
    }
    if(!CorrectIndex){
      outs() << "stop index unification\n";
      return;
    }
    // remove other index(i.e. phinode)
    SmallVector<Instruction *, 16> PhiToRemove;
    Value* CorrectValue = dyn_cast<Value>(CorrectIndex);
    for(int i=0; i<OtherIndex.size(); i++){
      // outs() << "original false: "<< *(OtherIndex[i]) << "\n";
      PHINode* otherphinode = dyn_cast<PHINode>(OtherIndex[i]);
      BasicBlock* incomingBlock;
      Value* otherindexvalue;
      for(int j=0; j<otherphinode->getNumIncomingValues(); j++){
        if(otherphinode->getIncomingBlock(j) == Latch){
          otherindexvalue = otherphinode->getIncomingValue(j);
          break;
        }
      }
      if(Instruction *I = dyn_cast<Instruction>(otherindexvalue)){
        GetUserAndErase(I);
        InstToRemove.push_back(I);
      }
      Value* OtherValue = dyn_cast<Value>(OtherIndex[i]);
      if(OtherValue->isUsedByMetadata())
        ValueAsMetadata::handleRAUW(OtherValue, UndefValue::get(OtherValue->getType()));
      // outs() << *CorrectValue << "\n";
      if(Instruction *I = dyn_cast<Instruction>(OtherValue)){
        // outs() << "replace" << *I << " to" << *CorrectValue << "\n";
        I->replaceAllUsesWith(CorrectValue);
      }
      PhiToRemove.push_back(OtherIndex[i]);
    }
    for(int i=0; i<PhiToRemove.size(); i++){
      // outs() << "phi to remove" << *(PhiToRemove[i]) << "\n";
      PhiToRemove[i]->eraseFromParent();
    }
    for(int i=0; i<InstToRemove.size(); i++){
      // outs() << "inst to remove" << *(InstToRemove[i]) << "\n";
      InstToRemove[i]->eraseFromParent();
    }
    PhiToRemove.clear();
    InstToRemove.clear();
    sharesameindex++;
  }

  bool findfusiblename(Loop &L){
    for(BasicBlock *BB : L.blocks()){
      Twine BB_Name = Twine(BB->getName());
      Twine canfusename = "_fused";
      std::string str1 = BB_Name.str();
      std::string str2 = canfusename.str();
      if(str1.find(str2) != std::string::npos){
        return true;
      }
    }
    return false;
  }
}

PreservedAnalyses IndexUnificationPass::run(Function &F, FunctionAnalysisManager &FAM) {
  LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
  for(Loop *L : LI){
    if(findfusiblename(*L)){
      optimizeindex(*L);
    }
  }

  if(sharesameindex){
    errs() << "Module: " << F.getParent()->getName() << " Function: " << F.getName() << "\n";
    errs() << "share same index = " << sharesameindex << "\n";
  }
  sharesameindex = 0;
  return PreservedAnalyses::none();
}
