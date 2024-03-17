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
  // Reference to basic block 
  BasicBlock *BB_link;
  // Name of basic block
  std::string name;
  // Id of basic block
  std::uint8_t id;
  // List of references to variables used in instructions of basic block and its predecessors
  std::vector<llvm::Value *> vars;
  // List of ids of predecessors of basic block
  std::vector<std::uint8_t> preds;
  // List of ids of successors of basic block
  std::vector<std::uint8_t> succs;
  // Reference to last br instruction of basic block 
  llvm::Instruction * last_instruction;
};


class CHCTransformPass : public PassInfoMixin<CHCTransformPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H