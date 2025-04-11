#include "llvm/Transforms/Utils/CHCTransform.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"

#include <iostream>
#include <map>
#include <sstream>
#include <unordered_set>

using namespace llvm;

namespace {

const std::unordered_set<std::string> MAIN_FUNCTIONS = {
    "main"
};

const std::unordered_set<std::string> ASSERT_FUNCTIONS = {
    "__assert",     "__assert2", "__assert_fail", "__assert_perror_fail",
    "__assert_rtn", "_assert",   "_wassert"};

constexpr char PRIME_SIGN = 'p';

const std::string UNSIGNED_UINT_FUNCTION = "__VERIFIER_nondet_uint";
const std::string UNSIGNED_USHORT_FUNCTION = "__VERIFIER_nondet_ushort";
const std::string UNSIGNED_SHORT_FUNCTION = "__VERIFIER_nondet_short";
const std::string UNSIGNED_UCHAR_FUNCTION = "__VERIFIER_nondet_uchar";
const std::string UNSIGNED_CHAR_FUNCTION = "__VERIFIER_nondet_char";


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
  virtual std::string Print() const = 0;
  virtual MyPredicateType GetType() const = 0;
  virtual std::string GetSMT() const = 0;
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

  std::string Print() const override {
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

  std::string GetSMT() const override {
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

  MyPredicateType GetType() const override { return PREDICATE; }
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

  MyPredicateType GetType() const override { return FUNCTION; }
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
  std::string Print() const override {
    return result + "=ite(" + condition + "," + operand1 + "," + operand2 + ")";
  }

  std::string GetSMT() const override
  {
    return + "(= " + result + " (ite " + condition + " " + operand1
      + " " + operand2 + " ))";
  }

  MyPredicateType GetType() const override { return ITE; }
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
  std::string Print() const override {
    return result + " = " + operand1 + " " + sign + " " + operand2;
  }

  std::string GetSMT() const override
  {
    if (sign == "!=") {
        return "(= " + result + " (not (= " + operand1 + " " + operand2 + " )))";
    } else {
        return "(= " + result + " (" + sign + " " + operand1 + " " + operand2 + " ))";
    }
  }

  MyPredicateType GetType() const override { return BINARY; }
};
struct UnaryConstraint : MyConstraint {
  std::string result;
  std::string value;
  virtual ~UnaryConstraint() {}
  UnaryConstraint(std::string result_, std::string value_) {
    result = result_;
    value = value_;
  }
  std::string Print() const override { return result + " = " + value;
  }

  std::string GetSMT() const override { return "(= " + result + " " + value + " )"; }

  MyPredicateType GetType() const override { return UNARY; }
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
  std::string Print() const override { return operand1 + sign + operand2; }
  std::string GetSMT() const override
  {
    return "(" + sign + " " + operand1 + " " + operand2 + " )";
  }
  MyPredicateType GetType() const override { return COMPARISON; }
};
struct LoadConstraint : MyConstraint {
  std::string result;
  std::string value;
  virtual ~LoadConstraint() {}
  LoadConstraint(std::string name_, std::string value_) {
    result = name_;
    value = value_;
  }
  std::string Print() const override { return result + " = " + value;
  }

  std::string GetSMT() const override { return "(= " + result + " " + value + " )"; }

  MyPredicateType GetType() const override { return LOAD; }
};
struct StoreConstraint : MyConstraint {
  std::string result;
  std::string value;
  virtual ~StoreConstraint() = default;
  StoreConstraint(std::string result_, std::string value_) {
    result = std::move(result_);
    value = std::move(value_);
  }
  std::string Print() const override { return result + " = " + value;
  }

  std::string GetSMT() const override { return "(= " + result + " " + value + " )"; }

  MyPredicateType GetType() const override { return STORE; }
};

struct Implication {
  using Constraints = std::vector<std::unique_ptr<MyConstraint>>;
  // Implications structured as "predicates -> head"
  Constraints constraints;
  MyPredicate head;

  Implication(MyPredicate head_) {
    head = head_;
  }

  Implication(Implication && other) = default;
  Implication(Implication const & other) = delete;
  Implication& operator=(Implication const & other) = delete;
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
  // True if block calls assert function and fails
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
  using BasicBlocks = std::map<unsigned, MyBasicBlock>;
  // Indexed map of basic blocks
  BasicBlocks basic_blocks;
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

bool isMainFunction(std::string const & function_name) {
  return MAIN_FUNCTIONS.find(function_name) != MAIN_FUNCTIONS.end();
}

bool isFailedAssertCall(Instruction * I) {

  if (CallInst * call_inst = dyn_cast<CallInst>(I)) {

    Function * fn = call_inst->getCalledFunction();
    if (fn) {
      auto function_name = fn->getName().str();
      for (auto assert : ASSERT_FUNCTIONS) {
        // Platforms transforms function name differently,
        // check function name also as substring or added
        // '?' at the beginning
        if (assert == function_name) {
          return true;
        } else if (function_name.find('?' + assert) == 0) {
          return true;
        } else if (function_name.find(assert) == 0) {
          return true;
        }
      }
    }
  }
  return false;
}

// Get type of variable
std::string get_type(Type *type) {
  if (type->isIntegerTy()) {
    auto w = cast<IntegerType>(type)->getBitWidth();
    return w == 1 ? "Bool" : "Int";
  }
  throw std::logic_error("Unknown type of variable.");
}

// Set variable in head predicate as prime when assigned new value in constraint
void set_prime_var_in_head(MyPredicate & head_predicate, std::string const & var_name) {
  for (unsigned int i = 0; i < head_predicate.vars.size(); i++) {
    if (head_predicate.vars[i].name == var_name) {
      head_predicate.vars[i].isPrime = true;
      break;
    }
  }
}

std::string convert_name_to_string(Value const * const value) {
  std::string block_address;
  raw_string_ostream string_stream(block_address);

  value->printAsOperand(string_stream, false);

  return block_address;
}

// Convert operand to std::string, if negative string,
// return as function (-) with positive value (e.g. -100 => (- 100))
std::string convert_operand_to_string(Value *value) {
  if (get_type(value->getType()) == "Int") {
    if (auto asConstant = dyn_cast<ConstantInt>(value)) {
      auto num = asConstant->getSExtValue();
      if (num < 0) {
        return "(- " + std::to_string(num * -1) + ')';
      }
      return std::to_string(num);
    }
  }

  return convert_name_to_string(value);
}

// Return variable to for end of the predicate if function is called in basic block
MyVariable get_function_call_var(MyBasicBlock const & BB, int e_index,
                                 MyBasicBlock const & successor) {
  if (BB.last_instruction != nullptr && BB.successors.size() > 0) {
    if (BB.successors.size() != 2 ||
         successor.BB_link == BB.last_instruction->getOperand(2)) {
      return MyVariable("false");
    } else {
      return MyVariable("e" + std::to_string(e_index), "Bool");
    }
  } else {
    return MyVariable("false");
  }
}

std::optional<std::int8_t> get_block_id_by_link(BasicBlock const * block,
    MyFunctionInfo::BasicBlocks const & my_blocks) {
  for (auto const & [id, my_block] : my_blocks) {
    if (my_block.BB_link == block) {
      return id;
    }
  }
  return std::nullopt;
}

MyFunctionInfo load_basic_info(Function& F) {
  auto function_name = F.getName().str();
  bool is_main_function = isMainFunction(function_name);
  MyFunctionInfo function_info(&F, function_name, is_main_function);

  return function_info;
}

MyFunctionInfo::BasicBlocks load_basic_blocks(Function & F) {
  MyFunctionInfo::BasicBlocks basic_blocks;
  unsigned bb_index = 1;
  std::string const function_name = F.getName().str();

  for (BasicBlock & BB : F) {
    auto name = function_name + std::to_string(bb_index);
    BB.setName(name);

    MyBasicBlock myBB(&BB, name, bb_index);
    basic_blocks.insert(std::make_pair(bb_index, myBB));
    ++bb_index;
  }

  return basic_blocks;
}

class SMTOutput {
public:
  SMTOutput() : output(std::cout) {}

  void smt_print_implications(std::vector<Implication> const & implications);

private:
  void smt_declare_functions(std::vector<Implication> const & implications);

  void smt_declare_function(MyConstraint const & predicate);

  void smt_print_constraints(Implication::Constraints const & constraints);

  void smt_declare_implication(Implication const & implication);

  void smt_declare_implications(std::vector<Implication> const & implications) {
    for (auto const & implication : implications) {
    smt_declare_implication(implication);
  }
}

  int smt_quantifiers(Implication const & implication, int indent);

  std::ostream & output;
  std::unordered_set<std::string> declared_functions;
};

}

class CHCTransformPass::impl {
public:
  void run(Function & F, FunctionAnalysisManager & AM);
private:
  void set_global_variables(Module * module);

  void add_global_variables(MyPredicate & predicate, MyFunctionInfo const & function_info);

  void initialize_global_variables(Implication & implication, MyFunctionInfo const & function_info);

  void add_variable(Value * var, MyBasicBlock * my_block);

  void set_basic_block_info(MyFunctionInfo * function_info);

  MyFunctionInfo load_my_function_info(Function & F);

  Implication::Constraints transform_function_call(Instruction * I, MyFunctionInfo & function_info);

  std::vector<Implication> transform_basic_blocks(MyFunctionInfo & function_info);

  Implication::Constraints transform_instructions(MyBasicBlock const & BB, MyFunctionInfo & function_info);

  std::unique_ptr<LoadConstraint> transform_load_operand(Instruction * I);

  std::unique_ptr<StoreConstraint> transform_store_operand(Instruction * I);

  std::vector<std::unique_ptr<UnaryConstraint>> transform_phi_instructions(MyBasicBlock const & predecessor, MyBasicBlock const & successor);

  std::vector<Implication> get_entry_block_implications(MyFunctionInfo const & function_info, MyBasicBlock const & BB1);

  MyPredicate create_basic_block_predicate(MyBasicBlock const & BB, bool isEntry, MyFunctionInfo const & function_info);

  Implication create_entry_to_exit(MyBasicBlock const & BB, MyFunctionInfo & function_info);

  MyPredicate get_function_predicate(MyFunctionInfo const & function_info, MyVariable e_in, MyVariable e_out);

  MyPredicate get_fail_block_predicate(MyFunctionInfo const & function_info);

  std::unordered_map<std::string, int> global_vars;
  bool first_function = true;
  unsigned int var_index = 0;
  SMTOutput smt_output;
};


void CHCTransformPass::impl::run(Function &F,
                                        FunctionAnalysisManager &AM) {
if (first_function) {
    set_global_variables(F.getParent());
    first_function = false;
  } else {
  }

  auto function_info = load_my_function_info(F);

  //print_info(function_info.basic_blocks);

  auto implications = transform_basic_blocks(function_info);

  // print_implications(implications);

  smt_output.smt_print_implications(implications);
}

void CHCTransformPass::impl::set_global_variables(Module * module) {
  auto globals = module->globals();
  unsigned j = 0u;
  for (GlobalValue & var : globals) {
    if (var.getValueType()->isIntegerTy()) {
      auto name = "g" + std::to_string(j);
      var.setName(name);
      global_vars[name] = 0;
      j++;
    }
  }
}

// Set name for variable and add to basic block info if not presented
void CHCTransformPass::impl::add_variable(Value * var, MyBasicBlock * my_block) {
  // Skip labels and pointers
  if (var->getType()->isLabelTy() or var->getType()->isPointerTy()) {
    return;
  }

  if (!var->hasName()) {
    var->setName("x" + std::to_string(var_index));
    ++var_index;
  }

  my_block->vars.insert(var);
}

MyFunctionInfo CHCTransformPass::impl::load_my_function_info(Function &F) {
  MyFunctionInfo function_info = load_basic_info(F);

  function_info.basic_blocks = load_basic_blocks(F);

  set_basic_block_info(&function_info);

  return function_info;
}


void CHCTransformPass::impl::set_basic_block_info(MyFunctionInfo *function_info) {
  for (auto &it : function_info->basic_blocks) {
    MyBasicBlock *BB = &it.second;
    BasicBlock *block_link = BB->BB_link;

    // Set Predecessors of blocks and variables from them
    for (auto pred : predecessors(block_link)) {
      // Find predecessor id
      auto maybe_pred_id = get_block_id_by_link(pred, function_info->basic_blocks);
      if (maybe_pred_id.has_value()) {
        auto pred_id = maybe_pred_id.value();
        // Add predecessor
        BB->predecessors.push_back(pred_id);

        // Add new variables from predecessor
        for (auto v : function_info->basic_blocks[pred_id].vars) {
          add_variable(v, BB);
        }
      }
    }

    // First basic block without predecessors load function arguments
    if (predecessors(block_link).empty()) {
      Function *F = function_info->function_pointer;
      // Load arguments as variables
      for (auto arg = F->arg_begin(); arg != F->arg_end(); ++arg) {
        add_variable(arg, BB);
      }
    }

    // Set successors of block
    for (auto succ : successors(block_link)) {
      auto maybe_succ_id = get_block_id_by_link(succ, function_info->basic_blocks);
      assert(maybe_succ_id.has_value());
      BB->successors.push_back(maybe_succ_id.value());
    }

    // Find all used variables in instructions
    for (Instruction &I : block_link->instructionsWithoutDebug()) {

      // See if basic block handles failed assertion
      if (isFailedAssertCall(&I)) {
        BB->isFalseBlock = true;
        break;
      }

      // Remember function called in basic block (no assert)
      if (I.getOpcode() == Instruction::Call) {
        auto fn = dyn_cast<CallInst>(&I)->getCalledFunction();
        if (fn && !fn->isDeclaration()) {
          BB->isFunctionCalled = true;
        }
      }

      // Remember last br instruction (should be only one)
      if (I.getOpcode() == Instruction::Br) {
        BB->last_instruction = &I;
      }

      // Remember return value of function
      if (I.getOpcode() == Instruction::Ret) {
        if (!function_info->function_pointer->getReturnType()->isVoidTy()) {
          auto o = I.getOperand(0);
          if (o->getValueID() != Value::ConstantIntVal) {
            function_info->return_value =
                MyVariable(convert_name_to_string(o), get_type(o->getType()));
          } else {
            function_info->return_value =
                MyVariable(convert_operand_to_string(o));
          }
        }
        BB->isLastBlock = true;
      }

      // Add instructions returning void
      if (!I.getType()->isVoidTy()) {
        add_variable(&I, BB);
      }

      // Add all variables from instruction
      for (auto &o : I.operands()) {
        add_variable(o, BB);
      }
    }
  }
}

// Add global variables to basic block predicate
void CHCTransformPass::impl::add_global_variables(MyPredicate & predicate, MyFunctionInfo const & function_info) {
  for (auto const & [name, index] : global_vars) {
    if (not function_info.is_main_function) {
      // No main function needs input value of global variable
      predicate.vars.push_back(MyVariable(name, "Int"));
    }
    predicate.vars.push_back(
        MyVariable(name + "_" + std::to_string(index), "Int"));
  }
}

/// Methods of the world-facing transformation pass

CHCTransformPass::CHCTransformPass() : pimpl(std::make_unique<impl>()) { }

CHCTransformPass::~CHCTransformPass() { }

CHCTransformPass::CHCTransformPass(CHCTransformPass const & other) {
  this->pimpl = std::make_unique<impl>(*other.pimpl);
}

CHCTransformPass::CHCTransformPass(CHCTransformPass && other) = default;


PreservedAnalyses CHCTransformPass::run(Function &F, FunctionAnalysisManager &AM) {
  pimpl->run(F, AM);
  return PreservedAnalyses::all();
}

#pragma region Print my basic blocks
// Print debug information about basic blocks
[[maybe_unused]]
void print_info(std::map<std::uint8_t, MyBasicBlock> my_blocks) {

  for (auto &it : my_blocks) {
    MyBasicBlock &BB = it.second;
    errs() << "BB: " << BB.name << " : " << BB.BB_link << "\n";

    errs() << "IsFailed: " << (BB.isFalseBlock ? "yes"
                                              : "no")
                                                    << "\n";

    errs() << "Preds: "
           << "\n";
    for (auto pred : BB.predecessors) {
      my_blocks[pred].BB_link->printAsOperand(errs(), true);
      errs() << " -> " << std::to_string(pred) << "\n";
    }
    errs() << "\n";

    errs() << "Succs: "
           << "\n";
    for (auto succ : BB.successors) {
      my_blocks[succ].BB_link->printAsOperand(errs(), true);
      errs() << " -> " << std::to_string(succ) << "\n";
    }
    errs() << "\n";

    errs() << "Vars: "
           << "\n";
    for (auto var : BB.vars) {
      var->printAsOperand(errs(), true);
      errs() << "\n";
    }
    errs() << "\n";
  }
}
#pragma endregion

#pragma region Transform basic blocks


// Transform Cmp instruction
std::string cmp_sign(Instruction *I) {
  CmpInst *CmpI = cast<CmpInst>(I);
  switch (CmpI->getPredicate()) {
  case CmpInst::ICMP_EQ:
    return "=";
  case CmpInst::ICMP_NE:
    return "!=";
  case CmpInst::ICMP_UGT:
  case CmpInst::ICMP_SGT:
    return ">";
  case CmpInst::ICMP_UGE:
  case CmpInst::ICMP_SGE:
    return ">=";
  case CmpInst::ICMP_ULT:
  case CmpInst::ICMP_SLT:
    return "<";
  case CmpInst::ICMP_ULE:
  case CmpInst::ICMP_SLE:
    return "<=";
  default:
    throw std::logic_error("Unknown comparison symbol.");
    break;
  }
}

// Create constraint for br instruction
std::unique_ptr<UnaryConstraint> transform_br(Instruction *I, BasicBlock * successor) {
  // Instruction must have 3 operands to jump
  if (I->getNumOperands() != 3) {
    throw new std::logic_error(
        "Wrong instruction. Too few function operands.");
  }

  std::string res = successor == I->getOperand(2) ? "true" : "false";

  return std::make_unique<UnaryConstraint>(convert_name_to_string(I->getOperand(0)), res);
}

// Create binary constraint for comparison instruction
std::unique_ptr<BinaryConstraint> transform_comparison(Instruction *I) {
  CmpInst *comparison = cast<CmpInst>(I);
  auto sign = cmp_sign(comparison);
  auto * lhs = comparison->getOperand(0);
  auto * rhs = comparison->getOperand(1);

  // Get constant value as signed or unsigned based on type of comparison
  auto asString = [&](Value* val) -> std::string {
    if (auto asConstant = dyn_cast<ConstantInt>(val)) {
      if (comparison->isSigned()) {
        auto value = asConstant->getSExtValue();
        if (value < 0) {
          return "(- " + std::to_string(value * -1) + ')';
        }
        return std::to_string(value);
      } else {
        auto value = asConstant->getZExtValue();
        return std::to_string(value);
      }
    }
    return convert_name_to_string(val);
  };
  
  return std::make_unique<BinaryConstraint>(convert_name_to_string(comparison), asString(lhs), sign, asString(rhs));
}

// Create binary constraint from binary instructions
std::unique_ptr<BinaryConstraint> transform_binary_inst(Instruction *I) {
  std::string sign;
  switch (I->getOpcode()) {
  case Instruction::ICmp: 
    return transform_comparison(I);
  case Instruction::Add:
    sign = "+";
    break;
  case Instruction::Sub:
    sign = "-";
    break;
  case Instruction::Mul:
    sign = "*";
    break;
  case Instruction::UDiv:
  case Instruction::SDiv:
    sign = "div";
    break;
  case Instruction::URem:
  case Instruction::SRem:
    sign = "mod";
    break;
  case Instruction::Xor:
    sign = "xor";
    break;
  case Instruction::And:
    sign = "and";
    break;
  case Instruction::Or:
    sign = "or";
    break;
  default:
    throw new std::logic_error("Wrong binary instruction.");
  }

  return std::make_unique<BinaryConstraint>(convert_name_to_string(I),
                              convert_operand_to_string(I->getOperand(0)), sign,
                              convert_operand_to_string(I->getOperand(1)));
}

// Create constraints for function call
Implication::Constraints
CHCTransformPass::impl::transform_function_call(
    Instruction * I, MyFunctionInfo & function_info) {
  Implication::Constraints result;
  CallInst *call_inst = cast<CallInst>(I);
  
  // Get function from instruction
  Function * fn = call_inst->getCalledFunction();
  std::string function_name = "";

  // If no function, name can be taken from instruction operand
  if (fn) {
    function_name = fn->getName().str();
  } else {
    function_name = convert_name_to_string(I->getOperand(0));
  }
  
  // If function not declared, check name for predefined non-deterministic functions
  if (!fn || fn->isDeclaration()) {
    if (function_name.find(UNSIGNED_UINT_FUNCTION, 0) != std::string::npos) {
      
      result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "4294967295"));
    } else if (function_name.find(UNSIGNED_SHORT_FUNCTION, 0) !=
               std::string::npos) {
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "(- 32768)"));
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "32767"));
    } else if (function_name.find(UNSIGNED_USHORT_FUNCTION, 0) !=
               std::string::npos) {
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "65535"));

    } else if (function_name.find(UNSIGNED_UCHAR_FUNCTION, 0) !=
               std::string::npos) {
      
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "255"));
    
    } else if (function_name.find(UNSIGNED_CHAR_FUNCTION, 0) != std::string::npos) {
    
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "(- 128)"));
      result.push_back(
          std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "127"));
    
    } else {
      // If no predefined function, ignore call and add true constraint
      result.push_back(std::make_unique<MyPredicate>("true"));
    }   
    return result;
  }
  
  auto predicate = std::make_unique<FunctionPredicate>(function_name);
  std::string var_name;
  std::string var_type;

  // Add parameters
  for (auto arg = call_inst->arg_begin(); arg != call_inst->arg_end(); ++arg) {
    if (arg->get()->getValueID() != Value::ConstantIntVal) {
      var_name = convert_name_to_string(arg->get());
      var_type = get_type(arg->get()->getType());

      predicate->vars.push_back(MyVariable(var_name, var_type));
    } else {
      var_name = convert_operand_to_string(arg->get());

      predicate->vars.push_back(MyVariable(var_name));
    }
  }

  // Add return variable
  if (!fn->getReturnType()->isVoidTy()) {
    var_name = convert_name_to_string(I);

    predicate->vars.push_back(MyVariable(var_name, get_type(fn->getReturnType()), true));
    predicate->changed_var = var_name;
  }

  // Add variables for input error variable
  if (function_info.e_index == 0) {
    predicate->vars.push_back(MyVariable("false"));
  } else {
    predicate->vars.push_back(
        MyVariable("e" + std::to_string(function_info.e_index), "Bool"));
  }
  
  // Add variables for output error variable
  ++function_info.e_index;
  predicate->vars.push_back(
      MyVariable("e" + std::to_string(function_info.e_index), "Bool"));

  // Add global variables input and output values
  for (auto &var : global_vars) {
    predicate->vars.push_back(
        MyVariable(var.first + "_" + std::to_string(var.second), "Int"));
    var.second++;
    predicate->vars.push_back(
        MyVariable(var.first + "_" + std::to_string(var.second), "Int"));
  }
 
  result.push_back(std::move(predicate));
  return result;
}

// Create constraint for zext instruction
std::unique_ptr<MyConstraint> transform_zext(Instruction *I) {
  MyVariable input(convert_name_to_string(I->getOperand(0)),
                   get_type(I->getOperand(0)->getType()));
  MyVariable output(convert_name_to_string(I),
                   get_type(I->getType()));
  
  if (input.type == "Bool" && output.type == "Int") {    
    return std::make_unique<ITEConstraint>(output.name, "1", input.name, "0");
  } else {
    return std::make_unique<UnaryConstraint>(output.name, input.name);
  }
}

// Create constraint for trunc instruction 
std::unique_ptr<MyConstraint> transform_trunc(Instruction *I) {
  MyVariable input(convert_name_to_string(I->getOperand(0)),
                   get_type(I->getOperand(0)->getType()));
  MyVariable output(convert_name_to_string(I), get_type(I->getType()));
  
  if (input.type == "Int" && output.type == "Bool") {
    return std::make_unique<BinaryConstraint>(output.name, input.name, "!=", "0");
  } else {
    return std::make_unique<UnaryConstraint>(output.name, input.name);
  }
}

// Create equality constraint for sext instruction
std::unique_ptr<UnaryConstraint> transform_sext(Instruction *I)
{
  return std::make_unique<UnaryConstraint>(convert_name_to_string(I),
                     convert_name_to_string(I->getOperand(0)));
}

// Create constraint for logic instruction with boolean variables
std::unique_ptr<BinaryConstraint> transform_logic_operand(Instruction *I) {
  auto op1_type = get_type(I->getOperand(0)->getType());
  auto op2_type = get_type(I->getOperand(1)->getType());

  if (op1_type == "Bool" && op2_type == "Bool") {
    return transform_binary_inst(I);
  } else {
    throw std::logic_error("Logic operation not on Bool");
  }
}

// Create constraint for load instruction with global variable
std::unique_ptr<LoadConstraint> CHCTransformPass::impl::transform_load_operand(Instruction *I) {

  std::string global_var_name = I->getOperand(0)->getName().str();
  int index = global_vars[global_var_name];

  auto result = convert_name_to_string(I);
  auto value = global_var_name + "_" + std::to_string(index);
  
  return std::make_unique<LoadConstraint>(std::move(result), std::move(value));
}

// Create constraint for store instruction with global variable
std::unique_ptr<StoreConstraint> CHCTransformPass::impl::transform_store_operand(Instruction *I) {
  
  std::string global_var_name = I->getOperand(1)->getName().str();
  global_vars[global_var_name]++;
  int index = global_vars[global_var_name];

  return std::make_unique<StoreConstraint>(global_var_name + "_" + std::to_string(index), convert_operand_to_string(I->getOperand(0)));
}

// Transform instructions to constraints from instructions in basic block
Implication::Constraints CHCTransformPass::impl::transform_instructions(MyBasicBlock const & BB, MyFunctionInfo & function_info) {

  Implication::Constraints result;
  function_info.e_index = 0;

  for (Instruction & I: BB.BB_link->instructionsWithoutDebug()) {
    switch (I.getOpcode()) {
    // Instructions with no constraint
    case Instruction::Br:
    case Instruction::CallBr:
    case Instruction::IndirectBr:
    case Instruction::PHI:
    case Instruction::Ret:
    case Instruction::Unreachable:
      break;
    // Instructions with 1 constraint
    case Instruction::ICmp:
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::SRem: 
      result.push_back(transform_binary_inst(&I));
      break;
    case Instruction::ZExt:
      result.push_back(transform_zext(&I));
      break;
    case Instruction::Trunc:
      result.push_back(transform_trunc(&I));
      break;
    case Instruction::SExt:
      result.push_back(transform_sext(&I));
      break;
    case Instruction::Load:
      result.push_back(transform_load_operand(&I));
      break;
    case Instruction::Store:
      result.push_back(transform_store_operand(&I));
      break;
    // Transform logic instruction on booleans
    case Instruction::Xor:
    case Instruction::And:
    case Instruction::Or: 
      result.push_back(transform_logic_operand(&I));
      break;
    case Instruction::Call: {
      auto predicates = transform_function_call(&I, function_info);
      std::move(predicates.begin(), predicates.end(), std::back_inserter(result));
      break;
    }    
    default:
      throw std::logic_error("Not implemented instruction");
    }
  }
  return result;
}

// Create current function predicate not for call instruction
MyPredicate CHCTransformPass::impl::get_function_predicate(MyFunctionInfo const & function_info, MyVariable e_in, MyVariable e_out) {

  // Create predicate
  std::string var_name;
  std::string var_type;
  Function * F = function_info.function_pointer;
  MyPredicate predicate{F->getName().str()};
  
  // Add parameters
  for (auto arg = F->arg_begin(); arg != F->arg_end(); ++arg) {
    if (arg->getValueID() != Value::ConstantIntVal) {
      var_name = convert_name_to_string(arg);
      var_type = get_type(arg->getType());

      predicate.vars.push_back(MyVariable(var_name, var_type));
    }
  }

  // Add return value
  if (!F->getReturnType()->isVoidTy()) {
    predicate.vars.push_back(function_info.return_value);
  }

  if (!function_info.is_main_function) {
    // Add input and output errors
    predicate.vars.push_back(e_in);
    predicate.vars.push_back(e_out);
  }
   
  add_global_variables(predicate, function_info);

  return predicate;
}

// Return fail block predicate
MyPredicate CHCTransformPass::impl::get_fail_block_predicate(MyFunctionInfo const & function_info) {
  if (function_info.is_main_function) {
    // Return new predicate if main function
    return MyPredicate(function_info.function_name + "_error");
  } else {
    // Return function predicate with output error
    return get_function_predicate(
        function_info, MyVariable("false"), MyVariable("true"));
  }
}

// Create predicate for basic block: Format {name}({variables}), ex. BB1(%x1,%x2)
MyPredicate CHCTransformPass::impl::create_basic_block_predicate(
  MyBasicBlock const & BB,
  bool isEntry,
  MyFunctionInfo const & function_info
)
{

  // Failed assert block
  if (BB.isFalseBlock) {
    return get_fail_block_predicate(function_info);
  }

  // Convert variables
  std::vector<MyVariable> vars;
  std::string var_name;
  std::string var_type;
  for (auto &v : BB.vars) {
    if (v->getValueID() != Value::ConstantIntVal) {
      var_name = convert_name_to_string(v);
      var_type = get_type(v->getType());

      vars.push_back(MyVariable(var_name, var_type));
    }
  }

  std::string suffix = isEntry ? "_entry" : "_exit" ;
  return MyPredicate(BB.name + suffix, vars);
}

// Add constraints for global variables initialized values
void CHCTransformPass::impl::initialize_global_variables(Implication & implication,
                                                     MyFunctionInfo const & function_info) {
  if (function_info.is_main_function) {
    // Main function takes initial values of variable
    auto globals = function_info.function_pointer->getParent()->globals();

    for (auto &var : globals) {
      if (var.getValueType()->isIntegerTy()) {
        auto name = var.getName().str();
        ++global_vars[name];

        auto result = name + "_" + std::to_string(global_vars[name]);
        auto value = convert_operand_to_string(var.getInitializer());
        implication.constraints.push_back(std::make_unique<StoreConstraint>(result, value));
      }
    }
  } else {
    // No main function takes values of global variable
    // from input global variable in predicate
    for (auto &var : global_vars) {
      ++var.second;

      auto result = var.first + "_" + std::to_string(var.second);
      auto value = var.first;

      implication.constraints.push_back(std::make_unique<StoreConstraint>(result, value));
    }
  }
}

// Create first implication for function input and transfer to BB1
std::vector<Implication> CHCTransformPass::impl::get_entry_block_implications(MyFunctionInfo const & function_info, MyBasicBlock const & BB1) {
  std::vector<Implication> result;

  // Create predicate for entry basic block with function arguments
  MyBasicBlock BB_entry(nullptr, function_info.function_name + "0", 0);
  Function * F = function_info.function_pointer;
  for (auto arg = F->arg_begin(); arg != F->arg_end(); ++arg) {
    add_variable(arg, &BB_entry);
  }
  auto predicate = create_basic_block_predicate(BB_entry, true, function_info);
  add_global_variables(predicate, function_info);

  // Create first implication (true -> BBentry(x1,..))
  result.emplace_back(predicate);

  // Create implication for transfer to first basic block 
  // with initialized global variables
  auto BB1_predicate = create_basic_block_predicate(BB1, true, function_info);
  Implication imp1(BB1_predicate);
  imp1.constraints.push_back(std::make_unique<MyPredicate>(predicate));
 
  initialize_global_variables(imp1, function_info);
  
  if (!BB1.isFalseBlock) {
    add_global_variables(BB1_predicate, function_info);
  }
  imp1.head = BB1_predicate;

  result.push_back(std::move(imp1));

  return result;
}

// Set variables for phi instruction, depending on label before
std::vector<std::unique_ptr<UnaryConstraint>> CHCTransformPass::impl::transform_phi_instructions(MyBasicBlock const & predecessor, MyBasicBlock const & successor) {

  std::vector<std::unique_ptr<UnaryConstraint>> result;

  for (Instruction &I : successor.BB_link->instructionsWithoutDebug()) {
    if (I.getOpcode() == Instruction::PHI) {
      Value * translation = I.DoPHITranslation(successor.BB_link, predecessor.BB_link);

      result.push_back(std::make_unique<UnaryConstraint>(convert_name_to_string(&I),
                       convert_operand_to_string(translation)));
    }
  }
  return result;
}

// Create implication from entry to exit point in basic block
Implication CHCTransformPass::impl::create_entry_to_exit(MyBasicBlock const & BB, MyFunctionInfo & function_info) {
  
  MyPredicate entry_predicate = create_basic_block_predicate(BB, true, function_info);
  add_global_variables(entry_predicate, function_info);
  
  Implication::Constraints constraints = transform_instructions(BB, function_info);
  
  auto exit_predicate = create_basic_block_predicate(BB, false, function_info);
  add_global_variables(exit_predicate, function_info);

  // Add last output error variable if some function called in BB
  if (BB.isFunctionCalled) {
    exit_predicate.vars.push_back(MyVariable("e" + std::to_string(function_info.e_index), "Bool"));
  }

  std::unordered_set<std::string> prime_vars;

  // Create prime variables in predicates when new assignment
  for (auto & constraint : constraints) {
    
    if (FunctionPredicate *fp = dynamic_cast<FunctionPredicate *>(constraint.get())) {
      
      set_prime_var_in_head(exit_predicate, fp->changed_var);
      prime_vars.insert(fp->changed_var);
      
      // Set variables when assigned 
      for (unsigned int i = 0; i < fp->vars.size(); i++) {
        if (prime_vars.find(fp->vars[i].name) != prime_vars.end()) {
          fp->vars[i].isPrime = true;
        }
      }
    }
    else if (BinaryConstraint *bc = dynamic_cast<BinaryConstraint *>(constraint.get())) {
            
      // Set operands when assigned before
      if (prime_vars.find(bc->operand1) != prime_vars.end()) {
        bc->operand1 = bc->operand1 + PRIME_SIGN;
      }
      if (prime_vars.find(bc->operand2) != prime_vars.end()) {
        bc->operand2 = bc->operand2 + PRIME_SIGN;
      }

      // Set assigned variable as prime in current constraint and head predicate
      set_prime_var_in_head(exit_predicate, bc->result);
      prime_vars.insert(bc->result);
      bc->result = bc->result + PRIME_SIGN;
    }

    else if (UnaryConstraint *uc = dynamic_cast<UnaryConstraint *>(constraint.get())) {
      
      // Set operands when assigned before
      if (prime_vars.find(uc->value) != prime_vars.end()) {
        uc->value = uc->value + PRIME_SIGN;
      }

      // Set assigned variable as prime in current constraint and head predicate
      set_prime_var_in_head(exit_predicate, uc->result);
      prime_vars.insert(uc->result);
      uc->result = uc->result + PRIME_SIGN;
    }

    else if (ITEConstraint *ite = dynamic_cast<ITEConstraint *>(constraint.get())) {
      
      // Set condition operand as prime when assigned before
      if (prime_vars.find(ite->condition) != prime_vars.end()) {
        ite->condition = ite->condition + PRIME_SIGN;
      }

      // Set assigned variable as prime in current constraint and head predicate
      set_prime_var_in_head(exit_predicate, ite->result);
      prime_vars.insert(ite->result);
      ite->result = ite->result + PRIME_SIGN;
    } 
    
    else if (LoadConstraint *lc = dynamic_cast<LoadConstraint *>(constraint.get())) {

      // Set assigned variable as prime in current constraint and head predicate
      set_prime_var_in_head(exit_predicate, lc->result);
      prime_vars.insert(lc->result);
      lc->result = lc->result + PRIME_SIGN;
    } 
    
    else if (StoreConstraint *sc = dynamic_cast<StoreConstraint *>(constraint.get())) {
      
      // Set operand as prime when assigned before
      if (prime_vars.find(sc->value) != prime_vars.end()) {
        sc->value = sc->value + PRIME_SIGN;
      }
    }
  }
  constraints.push_back(std::make_unique<MyPredicate>(entry_predicate));
  Implication implication(exit_predicate);
  implication.constraints = std::move(constraints);
  return implication;
}

// Transform basic blocks to implications
std::vector<Implication> CHCTransformPass::impl::transform_basic_blocks(MyFunctionInfo & function_info) {
  
  std::vector<Implication> result;
  result = get_entry_block_implications(function_info, function_info.basic_blocks.at(1));

  for (auto const & entry : function_info.basic_blocks) {
    MyBasicBlock const & BB = entry.second;

    // Skip failed assert basic blocks
    if (BB.isFalseBlock) {
      continue;
    }

    // Create implication of current basic block (entry -> exit)
    result.push_back(create_entry_to_exit(BB, function_info));
    
    // Create implications for transfers to successors
    for (auto & succ : BB.successors) {
      auto current_exit_predicate =
          create_basic_block_predicate(BB, false, function_info);
      add_global_variables(current_exit_predicate, function_info);

      auto const & successor = function_info.basic_blocks.at(succ);
      auto succ_predicate = create_basic_block_predicate(successor, true, function_info);

      // Create implication
      Implication implication(succ_predicate);

      if (BB.isFunctionCalled) {
          current_exit_predicate.vars.push_back(get_function_call_var(BB, function_info.e_index, successor));
      }            

      // Add current BB exit predicate
      implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

      // Translate phi instructions
      for (auto && constraint : transform_phi_instructions(BB, successor)) {
        // Set prime variables
        set_prime_var_in_head(succ_predicate, constraint->result);
        constraint->result = constraint->result + PRIME_SIGN;
        implication.constraints.push_back(std::move(constraint));
      }

      // Branch predicate if 2 successors
      if (BB.last_instruction != nullptr && BB.successors.size() > 0) {
        if (BB.successors.size() == 2) {
          auto br = transform_br(BB.last_instruction, successor.BB_link);
          if ((br->result == "true" && br->value == "false") ||
              (br->result == "false" && br->value == "true")) {
              continue;
          }
          implication.constraints.push_back(std::move(br));
        }
      }

      if (not successor.isFalseBlock) {
        add_global_variables(succ_predicate, function_info);
      }
      implication.head = succ_predicate;
      result.push_back(std::move(implication));
    }

    // Add predicate if error in called function
    if (BB.isFunctionCalled) {
      auto fail = get_fail_block_predicate(function_info);
      Implication implication(fail);
      
      MyPredicate current_exit_predicate = create_basic_block_predicate(BB, false, function_info);
      add_global_variables(current_exit_predicate, function_info);
      current_exit_predicate.vars.push_back(MyVariable("true"));
      implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

      result.push_back(std::move(implication));
    }

    // From return instruction to function predicate implication
    if (BB.isLastBlock) {
      auto fun_predicate = get_function_predicate(
          function_info, MyVariable("false"), MyVariable("false"));

      auto implication = Implication(fun_predicate);

      MyPredicate current_exit_predicate =
          create_basic_block_predicate(BB, false, function_info);
      add_global_variables(current_exit_predicate, function_info);
      if (BB.isFunctionCalled) {
        current_exit_predicate.vars.push_back(MyVariable("false"));
      }
      implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

      result.push_back(std::move(implication));
    }
  }

  // Add error case implication
  if (function_info.is_main_function) {
    Implication implication = Implication(MyPredicate("false"));
    MyPredicate fail_predicate = get_fail_block_predicate(function_info);
    implication.constraints.push_back(std::make_unique<MyPredicate>(fail_predicate));
    result.push_back(std::move(implication));
  } else {
    auto function_predicate =  get_function_predicate(function_info, MyVariable("true"), MyVariable("true"));
    result.emplace_back(function_predicate);
  }

  return result;
}

#pragma endregion

#pragma region Print implication
// Print implication into console in readable form
[[maybe_unused]]
void print_implications(std::vector<Implication> const & implications)
{
  errs() << "\nImplications:\n";
  for (auto &i : implications) {

    if (!i.constraints.empty()) {
      // Print predicates
      auto first = 1;
      for (auto &p : i.constraints) {
         if (!first) {
          errs() << " & ";
         } else {
          first = 0;
         }
         errs() << p->Print();
      }
      errs() << " -> ";
    }
    //Print head
    errs() << i.head.Print();
    errs() << "\n";
  }
}



#pragma endregion

#pragma region Print SMT-LIB format
// Print function declaration
void SMTOutput::smt_declare_function(MyConstraint const & predicate) {
  if (predicate.GetType() == PREDICATE || predicate.GetType() == FUNCTION) {
    if (auto const * pred = dynamic_cast<MyPredicate const *>(&predicate)) {
      if (declared_functions.find(pred->name) == declared_functions.end() 
          && pred->name != "true"
          && pred->name != "false") {
 
        output << "(declare-fun |" << pred->name << "| (";

        for (auto v : pred->vars) {
          if (v.isConstant) {
              if (v.name != "false" && v.name != "true") {
              output << " "
                      << "Int";
              } else {
              output << " "
                      << "Bool";
              }
          } else {
              output << " " << v.type;
          }
        }

        output << ") Bool )" << std::endl;

        declared_functions.insert(pred->name);
      }
    }  
  }  
}

// Declare predicates as functions
void SMTOutput::smt_declare_functions(std::vector<Implication> const & implications) {
  for (auto const & implication : implications) {
    smt_declare_function(implication.head);
    for (auto const & constraint : implication.constraints) {
      smt_declare_function(*constraint);
    }
  }
}

// Print all constraints from implication
void SMTOutput::smt_print_constraints(Implication::Constraints const & constraints) {
  auto count = constraints.size();

  if (count == 1) {
      output << constraints[0]->GetSMT();
  } else {
      output << "(and ";

      for (auto const & p: constraints) {
        output << p->GetSMT();
        output << " ";
      }

    output << ')';
  }
}

// Print all variables from predicates in implication
int SMTOutput::smt_quantifiers(Implication const & implication, int indent) {
  std::map<std::string, std::string> vars;

  // Variables from head of implication
  for (auto v : implication.head.vars) {
      if (!v.isConstant) {
      auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
      vars.insert(std::make_pair(name, v.type));
      }
  }

  // Variables in predicates 
  for (auto const & constraint : implication.constraints) {
    if (MyPredicate *pred = dynamic_cast<MyPredicate *>(constraint.get())) {
      for (auto &v : pred->vars) {
         if (!v.isConstant) {
            auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
            vars.insert(std::make_pair(name, v.type));
         }
      }
    }    
    else if (LoadConstraint *load = dynamic_cast<LoadConstraint *>(constraint.get())) {
      vars.insert(std::make_pair(load->value, "Int"));
    }
    else if (StoreConstraint *store = dynamic_cast<StoreConstraint *>(constraint.get())) {
      vars.insert(std::make_pair(store->result, "Int"));
    }
  }

  // Print variables
  if (vars.size() > 0) {
    output << std::string(indent++, ' ') << "(forall ( ";
    for (auto v : vars) {
      output << "( " << v.first << " " << v.second << " )";
    }
    output << " )" << std::endl;
  }

  return indent;
}

// Create assert for implication
void SMTOutput::smt_declare_implication(Implication const & implication) {
  int indent = 0;
  output << std::string(indent++, ' ') << "(assert " << std::endl;

  // Write all variables used in implication
  indent = smt_quantifiers(implication, indent);

  if (!implication.constraints.empty()) {
    output << std::string(indent++, ' ') << "(=>  " << std::endl;

    // Convert predicates
    output << std::string(indent, ' ');
    smt_print_constraints(implication.constraints);
    output << std::endl;
  }
  // Convert head of implication
  output << std::string(indent, ' ');

  output << implication.head.GetSMT();
  output << std::endl;
  indent--;

  // Add ending parentheses
  while (indent >= 0) {
    output << std::string(indent--, ' ') << ")" << std::endl;
  }
}

// Convert my chc representation to SMT-LIB format
void SMTOutput::smt_print_implications(std::vector<Implication> const & implications) {

  /*output << "(set-logic HORN)" << std::endl;
  output << "(set-info :status sat)"
         << std::endl
         << std::endl;*/

  smt_declare_functions(implications);
  output << '\n';

  smt_declare_implications(implications);

  output << std::endl;
  //output << "(check-sat)" << std::endl;

}

#pragma endregion
