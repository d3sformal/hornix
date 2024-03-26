#ifndef LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H
#define LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H

#include "llvm/IR/PassManager.h"

namespace llvm {

enum MyPredicateType {
  BasicBlockHead,
  Expression,
  Unknown
};

struct Predicate {
  std::string name;
  std::vector<std::string> vars;
  std::string exp;
  MyPredicateType type;

  Predicate(std::string expression) { 
    exp = expression;
    type = MyPredicateType::Expression;
  }

  Predicate(std::string name_, std::vector<std::string> vars_) {
    name = name_;
    vars = vars_;
    type = MyPredicateType::BasicBlockHead;
  }

  Predicate() { type = MyPredicateType::Unknown;
  }
};

struct Implication {
  std::vector<Predicate> predicates;
  Predicate head;

  Implication(Predicate head_) {
    head = head_;
  }
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
  // Coded instruction for basic block except phi
  std::vector<Predicate> predicates;
  // Boolean to see if instructions where transformed
  bool transformed;
  // True if block calls wassert function and fails
  bool isFalseBlock;

  MyBasicBlock(BasicBlock* BB_link_, std::string name_, std::uint8_t id_) {
    BB_link = BB_link_;
    name = name_;
    id = id_;
    transformed = false;
    last_instruction = nullptr;
    isFalseBlock = false;
  }

  MyBasicBlock() {}
};


class CHCTransformPass : public PassInfoMixin<CHCTransformPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H