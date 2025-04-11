#ifndef LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H
#define LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class CHCTransformPass : public PassInfoMixin<CHCTransformPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);

  CHCTransformPass();
  ~CHCTransformPass();
  CHCTransformPass(CHCTransformPass const& other);
  CHCTransformPass(CHCTransformPass && other);
private:
  class impl;
  std::unique_ptr<impl> pimpl;
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H