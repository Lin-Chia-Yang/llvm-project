#include "llvm/IR/PassManager.h"

namespace llvm {

class CodeMotionPass : public PassInfoMixin<CodeMotionPass> {
public:
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

} // namespace llvm