#include "llvm/IR/PassManager.h"

namespace llvm {

class PeelLoopPass : public PassInfoMixin<PeelLoopPass> {
public:
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

} // namespace llvm