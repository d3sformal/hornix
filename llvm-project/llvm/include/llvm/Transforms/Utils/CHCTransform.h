#ifndef LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H
#define LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H

#include "llvm/IR/PassManager.h"

namespace llvm {

struct UnaryPredicate {
  std::string name;
  std::string value;
  
  UnaryPredicate(std::string name_, std::string value_) { 
    name = name_;
    value = value_;
  }

  std::string Print() {
    return name + " = " + value;
  }
};

struct BinaryPredicate {
  std::string name;
  std::string operand1;
  std::string sign;
  std::string operand2;

  BinaryPredicate(std::string name_, std::string op1, std::string sign_,
                 std::string op2) {
    name = name_;
    operand1 = op1;
    sign = sign_;
    operand2 = op2;
  }

  std::string Print() {
    return name + " = " + operand1 + " " + sign + " " + operand2;
  }
};

struct HeadPredicate {
  std::string name;
  std::vector<std::string> vars;
  
  HeadPredicate(std::string name_, std::vector<std::string> vars_) {
    name = name_;
    vars = vars_;
  }

  HeadPredicate() {}
};

struct Predicates {
  std::vector<UnaryPredicate> unary;
  std::vector<BinaryPredicate> binary;
  std::vector<HeadPredicate> head;
};

struct Implication {
  Predicates predicates;
  HeadPredicate head;

  Implication(HeadPredicate head_) {
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
  std::vector<std::uint8_t> predecessors;
  // List of ids of successors of basic block
  std::vector<std::uint8_t> successors;
  // Reference to last br instruction of basic block 
  llvm::Instruction * last_instruction;
  // True if block calls wassert function and fails
  bool isFalseBlock;

  MyBasicBlock(BasicBlock* BB_link_, std::string name_, std::uint8_t id_) {
    BB_link = BB_link_;
    name = name_;
    id = id_;
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