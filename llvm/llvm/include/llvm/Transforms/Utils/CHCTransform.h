#ifndef LLVM_TRANSFORMS_NEWPASSTEST_NEWPASSTEST_H
#define LLVM_TRANSFORMS_NEWPASSTEST_NEWPASSTEST_H

#include "llvm/IR/PassManager.h"

namespace llvm {

struct MyBasicBlock {
  BasicBlock *BB_link;
  std::string name;
  std::vector<llvm::Value *> vars;
  std::vector<BasicBlock *> preds;
  std::vector<BasicBlock *> succs;
};

class CHCTransform : public PassInfoMixin<NewPassTest> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_NEWPASSTEST_NEWPASSTEST_H