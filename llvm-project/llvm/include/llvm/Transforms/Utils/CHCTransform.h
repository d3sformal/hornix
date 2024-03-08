#ifndef LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H
#define LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H

#include "llvm/IR/PassManager.h"

namespace llvm {

struct MyBasicBlock {
  BasicBlock *BB_link;
  std::string name;
  std::vector<llvm::Value *> vars;
  std::vector<BasicBlock *> preds;
  std::vector<BasicBlock *> succs;
};

class CHCTransformPass : public PassInfoMixin<CHCTransformPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H