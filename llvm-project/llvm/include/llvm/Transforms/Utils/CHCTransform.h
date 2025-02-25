#ifndef LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H
#define LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H

#include "llvm/IR/PassManager.h"
#include <map>
#include <unordered_set>
#include <sstream>

namespace llvm {

const auto PRIME_SIGN = 'p';

const std::unordered_set<std::string> ASSERT_FUNCTIONS = {
  "__assert",
  "__assert2",
  "__assert_fail",
  "__assert_perror_fail",
  "__assert_rtn",
  "_assert",
  "_wassert"
};

const std::string UNSIGNED_UINT_FUNCTION = "__VERIFIER_nondet_uint";
const std::string UNSIGNED_USHORT_FUNCTION = "__VERIFIER_nondet_ushort";
const std::string UNSIGNED_SHORT_FUNCTION = "__VERIFIER_nondet_short";
const std::string UNSIGNED_UCHAR_FUNCTION = "__VERIFIER_nondet_uchar";
const std::string UNSIGNED_CHAR_FUNCTION = "__VERIFIER_nondet_char";


const std::unordered_set<std::string> MAIN_FUNCTIONS = {
    "main"
};

enum MyPredicateType {
  BINARY,
  UNARY,
  COMPARISON,
  ITE,
  LOAD,
  STORE,
  PREDICATE,
  FUNCTION
};

struct MyVariable {
  std::string name;
  std::string type;
  bool isPrime;
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

  MyVariable() {
    isConstant = false;
    isPrime = false;
  }
};

struct MyConstraint {
  virtual ~MyConstraint() {}
  virtual std::string Print() = 0;
  virtual MyPredicateType GetType() = 0;
  virtual std::string GetSMT() = 0;
};

struct MyPredicate : MyConstraint {
  std::string name;
  std::vector<MyVariable> vars;
  virtual ~MyPredicate() {}
  MyPredicate() {  }
  MyPredicate(std::string name_) {
    name = name_;
  }
  MyPredicate(std::string name_, std::vector<MyVariable> vars_) {
    name = name_;
    vars = vars_;
  }

  std::string Print() override {
    auto res = name;
    if (vars.size() > 0) {
        res += "( ";
        auto first = 1;
        for (auto &v : vars) {
          if (!first) {
            res += ", ";
          } else {
            first = 0;
          }
          res += v.isPrime ? v.name + PRIME_SIGN : v.name;
        }
        res += " )";
    }
    return res;
  }

  std::string GetSMT() override {
    std::ostringstream res;
    auto var_size = vars.size();
    if (var_size > 0) {
        res << "(";
    }

    res << name;
    for (auto v : vars) {
        auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
        res << " " << name;
    }
    if (var_size > 0) {
        res << " )";
    }

    return res.str();
  }
  
  MyPredicateType GetType() override { return PREDICATE; }
};

struct FunctionPredicate : MyPredicate {
  std::string changed_var;
  virtual ~FunctionPredicate() {}
  FunctionPredicate() { }
  FunctionPredicate(std::string name_) {
    name = name_;
  }
  FunctionPredicate(std::string name_, std::vector<MyVariable> vars_) {
    name = name_;
    vars = vars_;
  }

  MyPredicateType GetType() override { return FUNCTION; }
};
struct ITEConstraint : MyConstraint {
  std::string result;
  std::string operand1;
  std::string operand2;
  std::string condition;
  virtual ~ITEConstraint() {}
  ITEConstraint(std::string result_, std::string operand1_, std::string condition_,
                   std::string operand2_) {
    result = result_;
    operand1 = operand1_;
    condition = condition_;
    operand2 = operand2_;
  }
  std::string Print() override {
    return result + "=ite(" + condition + "," + operand1 + "," + operand2 + ")";
  }

  std::string GetSMT() override 
  {
    return + "(= " + result + " (ite " + condition + " " + operand1 
      + " " + operand2 + " ))";
  }

  MyPredicateType GetType() override { return ITE; }
};
struct BinaryConstraint : MyConstraint {
  std::string result;
  std::string operand1;
  std::string sign;
  std::string operand2;
  virtual ~BinaryConstraint() {}
  BinaryConstraint(std::string result_, std::string operand1_,
                   std::string sign_, std::string operand2_) {
    result = result_;
    operand1 = operand1_;
    sign = sign_;
    operand2 = operand2_;
  }
  std::string Print() override {
    return result + " = " + operand1 + " " + sign + " " + operand2;
  }

  std::string GetSMT() override 
  {
    if (sign == "!=") {
        return "(= " + result + " (not (= " + operand1 + " " + operand2 + " )))";
    } else {
        return "(= " + result + " (" + sign + " " + operand1 + " " + operand2 + " ))";
    }  
  }

  MyPredicateType GetType() override { return BINARY; }
};
struct UnaryConstraint : MyConstraint {
  std::string result;
  std::string value;
  virtual ~UnaryConstraint() {}
  UnaryConstraint(std::string result_, std::string value_) {
    result = result_;
    value = value_;
  }
  std::string Print() override { return result + " = " + value;
  }

  std::string GetSMT() override { return "(= " + result + " " + value + " )"; }

  MyPredicateType GetType() override { return UNARY; }
};
struct ComparisonConstraint : MyConstraint {
  std::string operand1;
  std::string operand2;
  std::string sign;
  virtual ~ComparisonConstraint() {}
  ComparisonConstraint(std::string operand1_, std::string sign_,
                       std::string operand2_) {
    operand1 = operand1_;
    operand2 = operand2_;
    sign = sign_;
  }
  std::string Print() override { return operand1 + sign + operand2; }
  std::string GetSMT() override 
  {
    return "(" + sign + " " + operand1 + " " + operand2 + " )"; 
  }
  MyPredicateType GetType() override { return COMPARISON; }
};
struct LoadConstraint : MyConstraint {
  std::string result;
  std::string value;
  virtual ~LoadConstraint() {}
  LoadConstraint() {}
  LoadConstraint(std::string name_, std::string value_) {
    result = name_;
    value = value_;
  }
  std::string Print() override { return result + " = " + value;
  }

  std::string GetSMT() override { return "(= " + result + " " + value + " )"; }

  MyPredicateType GetType() override { return LOAD; }
};
struct StoreConstraint : MyConstraint {
  std::string result;
  std::string value;
  virtual ~StoreConstraint() {}
  StoreConstraint() {}
  StoreConstraint(std::string result_, std::string value_) {
    result = result_;
    value = value_;
  }
  std::string Print() override { return result + " = " + value;
  }

  std::string GetSMT() override { return "(= " + result + " " + value + " )"; }

  MyPredicateType GetType() override { return STORE; }
};

struct Implication {
  // Implications structured as "predicates -> head"
  std::vector<MyConstraint *> constraints;
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
  // True if it contains return instruction
  bool isLastBlock;
  // True if there is call instruction in basic block
  bool isFunctionCalled;

  MyBasicBlock(BasicBlock* BB_link_, std::string name_, std::uint8_t id_) {
    BB_link = BB_link_;
    name = name_;
    id = id_;
    last_instruction = nullptr;
    isFalseBlock = false;
    isLastBlock = false;
    isFunctionCalled = false;
  }

  MyBasicBlock() {
    BB_link = NULL;
    id = 0;
    isFalseBlock = false;
    isLastBlock = false;
    last_instruction = NULL;
    isFunctionCalled = false;
  }
};

struct MyFunctionInfo {
  // Indexed map of basic blocks
  std::map<std::uint8_t, MyBasicBlock> basic_blocks;
  // Function name
  std::string function_name;
  // True if function name is from MAIN_FUNCTIONS list
  bool is_main_function;
  // Type of variable to return from function
  MyVariable return_value;
  // Pointer to llvm function struct
  Function *function_pointer;
  // Error index
  int e_index;

  MyFunctionInfo(Function * function_pointer_, std::string function_name_, bool is_main_) {
    function_pointer = function_pointer_;
    function_name = function_name_;
    is_main_function = is_main_;
    e_index = 0;
  }
};


class CHCTransformPass : public PassInfoMixin<CHCTransformPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_CHCTRANSFORM_CHCTRANSFORM_H