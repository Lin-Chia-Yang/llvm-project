#include "llvm/IR/PassManager.h"

namespace llvm {

class IndexUnificationPass : public PassInfoMixin<IndexUnificationPass> {
public:
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

} // namespace llvm