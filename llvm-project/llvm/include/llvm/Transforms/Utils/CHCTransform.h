#ifndef LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H
#define LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H

#include "llvm/IR/PassManager.h"
#include <map>
#include <unordered_set>

namespace llvm {

  const auto PRIME_SIGN = 'p';

enum MyPredicateType {
  HEAD,
  BINARY,
  UNARY,
  FUNCTION
};

struct MyVariable {
  std::string name;
  std::string type;
  bool isPrime;
  std::string constVal;
  bool isConstant;

  MyVariable(std::string name_, std::string type_, bool isPrime_) {
    name = name_;
    type = type_;
    isPrime = isPrime_;
    isConstant = false;
  }

  MyVariable(std::string name_, std::string type_) {
    name = name_;
    type = type_;
    isPrime = false;
    isConstant = false;
  }

  MyVariable(std::string val) {
    name = val;
    isPrime = false;
    isConstant = true;
  }

  MyVariable() {}
};

struct MyPredicate {
  MyPredicateType type;
  std::string name;
  std::string operand1;
  std::string sign;
  std::string operand2;
  std::map<std::string, MyVariable> vars;
  std::string changed_var;

  MyPredicate(std::string name_, std::string value_) {
    name = name_;
    operand1 = value_;
    type = UNARY;
  }

  MyPredicate(std::string name_, std::string op1, std::string sign_,
                  std::string op2) {
    name = name_;
    operand1 = op1;
    sign = sign_;
    operand2 = op2;
    type = BINARY;
  }

  MyPredicate(std::string name_,
                std::map<std::string, MyVariable> vars_) {
    name = name_;
    vars = vars_;
    type = HEAD;
  }

  MyPredicate(std::string name_) {
    name = name_;
    type = HEAD;
  }

  MyPredicate() {
  }

  std::string Print() {
    std::string res;
    switch (type) { 
      case BINARY:
        return name + " = " + operand1 + " " + sign + " " + operand2;
      case UNARY:
        return name + " = " + operand1;
      case HEAD:
      case FUNCTION:
        res = name;
        if (vars.size() > 0) {
          res += "( ";
          auto first = 1;
          for (auto &v : vars) {
            if (!first) {
              res += ", ";
            } else {
              first = 0;
            }
            res +=
                v.second.isPrime ? v.second.name + PRIME_SIGN : v.second.name;
          }
          res += " )";
        }
        return res;
      default:
        return "Unknown type";
    }
  }

};



//struct UnaryPredicate {
//  std::string name;
//  std::string value;
//  
//  UnaryPredicate(std::string name_, std::string value_) { 
//    name = name_;
//    value = value_;
//  }
//
//  std::string Print() {
//    return name + " = " + value;
//  }
//};
//
//struct BinaryPredicate {
//  std::string name;
//  std::string operand1;
//  std::string sign;
//  std::string operand2;
//
//  BinaryPredicate(std::string name_, std::string op1, std::string sign_,
//                 std::string op2) {
//    name = name_;
//    operand1 = op1;
//    sign = sign_;
//    operand2 = op2;
//  }
//
//  std::string Print() {
//    return name + " = " + operand1 + " " + sign + " " + operand2;
//  }
//};
//
//struct HeadPredicate {
//  std::string name;
//  std::unordered_map<std::string, MyVariable> vars;
//  
//  HeadPredicate(std::string name_, std::unordered_map<std::string, MyVariable> vars_) {
//    name = name_;
//    vars = vars_;
//  }
//
//  HeadPredicate(std::string name_) { 
//    name = name_;
//  }
//
//  HeadPredicate() {}
//};
//
//struct Predicates {
//  std::vector<UnaryPredicate> unary;
//  std::vector<BinaryPredicate> binary;
//  std::vector<HeadPredicate> head;
//};

struct Implication {
  //Predicates predicates;
  //HeadPredicate head;

  std::vector<MyPredicate> predicates;
  MyPredicate head;

  Implication(MyPredicate head_) {
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
  std::unordered_set<llvm::Value *> vars;
  // List of ids of predecessors of basic block
  std::vector<std::uint8_t> predecessors;
  // List of ids of successors of basic block
  std::vector<std::uint8_t> successors;
  // Reference to last br instruction of basic block 
  llvm::Instruction * last_instruction;
  // True if block calls wassert function and fails
  bool isFalseBlock;
  bool isLastBlock;

  MyBasicBlock(BasicBlock* BB_link_, std::string name_, std::uint8_t id_) {
    BB_link = BB_link_;
    name = name_;
    id = id_;
    last_instruction = nullptr;
    isFalseBlock = false;
    isLastBlock = false;
  }

  MyBasicBlock() {}
};


class CHCTransformPass : public PassInfoMixin<CHCTransformPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H