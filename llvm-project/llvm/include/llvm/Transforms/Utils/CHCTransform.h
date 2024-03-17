#ifndef LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H
#define LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class Predicate {};

class BB_Predicate : public Predicate {
public:
  std::string name;
  std::vector<std::string> vars;
  std::string exp;
};
class Assign_Predicate : public Predicate {};

struct Implication {
  std::vector<BB_Predicate> predicates;
  BB_Predicate head;
};

struct MyBasicBlock {
  BasicBlock *BB_link;
  std::string name;
  std::uint8_t id;
  std::vector<llvm::Value *> vars;
  std::vector<std::uint8_t> preds;
  std::vector<std::uint8_t> succs;
};


class CHCTransformPass : public PassInfoMixin<CHCTransformPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H