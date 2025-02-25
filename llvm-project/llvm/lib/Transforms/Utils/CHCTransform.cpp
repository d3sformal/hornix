#include "llvm/Transforms/Utils/CHCTransform.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "iostream"
#include <map>
#include <unordered_set>

using namespace llvm;

int var_index = 0;
auto &output = std::cout;
std::unordered_set<std::string> declared_functions;
std::unordered_map<std::string, int> global_vars;
bool first_function = true;

std::string get_type(Type *type);
std::string convert_name_to_string(Value *BB);
std::string convert_operand_to_string(Value *value);

#pragma region Create my basic blocks
// Set name for variable and add to basic block info if not presented
void add_variable(Value *var, MyBasicBlock* my_block) {

  // Skip labels and pointers
  if (var->getType()->isLabelTy() || var->getType()->isPointerTy()) {
    return;
  }

  // Set name
  if (!var->hasName()) {
    var->setName("x" + std::to_string(var_index));
    ++var_index;
  }

  my_block->vars.insert(var);
}

// Find id of basic block by reference to llvm class
std::int8_t get_block_id_by_link(
    BasicBlock *block,
    std::map<std::uint8_t, MyBasicBlock> my_blocks) {

  for (auto &bb : my_blocks) {
    if (bb.second.BB_link == block) {
      return bb.first;
    }
  }

  return -1;
}

// See if call instruction calls assert function
bool isFailedAssertCall(Instruction *I) {

  if (CallInst *call_inst = dyn_cast<CallInst>(I)) {

    Function *fn = call_inst->getCalledFunction();
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

// True if function name from expected main function names
bool isMainFunction(std::string function_name) {
  return (MAIN_FUNCTIONS.find(function_name) != MAIN_FUNCTIONS.end());
}

// Set information about current function
MyFunctionInfo load_basic_info(Function& F) {

  auto function_name = F.getName().str();
  auto is_main_function = isMainFunction(function_name);
  MyFunctionInfo function_info(&F, function_name, is_main_function);

  return function_info;
}

// Name all basic blocks and create MyBasicBlock for each
std::map<std::uint8_t, MyBasicBlock> load_basic_blocks(Function *F) {
  
  int bb_index = 1;
  std::map<std::uint8_t, MyBasicBlock> basic_blocks;
  std::string function_name = F->getName().str();

  for (BasicBlock &BB : *F) {
    auto name = function_name + std::to_string(bb_index);
    BB.setName(name);
     
    MyBasicBlock myBB(&BB, name, bb_index);
    basic_blocks.insert(std::make_pair(bb_index, myBB));
    ++bb_index;
  }

  return basic_blocks;
}

// Set information about basic blocks (vars, functions,...)
void set_basic_block_info(MyFunctionInfo *function_info) {
  
  for (auto &it : function_info->basic_blocks) {
    MyBasicBlock *BB = &it.second;
    BasicBlock *block_link = BB->BB_link;

    // Set Predecessors of blocks and variables from them
    for (auto pred : predecessors(block_link)) {
      // Find predecessor id
      auto pred_id = get_block_id_by_link(pred, function_info->basic_blocks);
      if (pred_id != -1) {
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
      BB->successors.push_back(
          get_block_id_by_link(succ, function_info->basic_blocks));
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

// Name basic blocks and create own structs for basic blocks
MyFunctionInfo load_my_function_info(Function &F) {
  
  MyFunctionInfo function_info = load_basic_info(F);
  
  function_info.basic_blocks = load_basic_blocks(&F);

  set_basic_block_info(&function_info);
  
  return function_info;
}
#pragma endregion

#pragma region Print my basic blocks
// Print debug information about basic blocks
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

// Add global variables to basic block predicate
void add_global_variables(MyPredicate* predicate, MyFunctionInfo* function_info) {

  for (auto v : global_vars) {
    if (!function_info->is_main_function) {
      // No main function needs input value of global variable
      predicate->vars.push_back(MyVariable(v.first, "Int"));  
    }
    predicate->vars.push_back(
        MyVariable(v.first + "_" + std::to_string(v.second), "Int"));
  }
}

// Convert Value name to std::string
std::string convert_name_to_string(Value *value) {
  std::string block_address;
  raw_string_ostream string_stream(block_address);

  value->printAsOperand(string_stream, false);

  return string_stream.str();
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

// Get type of variable
std::string get_type(Type *type) {
  if (type->isIntegerTy()) {
    auto w = cast<IntegerType>(type)->getBitWidth();
    if (w == 1) {
      return "Bool";
    }
    return "Int";
  } else {
    throw std::logic_error("Unknown type of variable.");
  }
}

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
UnaryConstraint * transform_br(Instruction *I, BasicBlock * successor) {
  // Instruction must have 3 operands to jump
  if (I->getNumOperands() != 3) {
    throw new std::logic_error(
        "Wrong instruction. Too few function operands.");
  }

  std::string res = successor == I->getOperand(2) ? "true" : "false";

  return new UnaryConstraint(convert_name_to_string(I->getOperand(0)), res);
}

// Create binary constraint for comparison instruction
BinaryConstraint * transform_comparison(Instruction *I) {
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
  
  return new BinaryConstraint(convert_name_to_string(comparison), asString(lhs), sign, asString(rhs));
}

// Create binary constraint from binary instructions
BinaryConstraint * transform_binary_inst(Instruction *I) {
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

  return new BinaryConstraint(convert_name_to_string(I),
                              convert_operand_to_string(I->getOperand(0)), sign,
                              convert_operand_to_string(I->getOperand(1)));
}

// Create constraints for function call
std::vector<MyConstraint *> tranform_function_call(Instruction *I,
                                   MyFunctionInfo *function_info) {

  std::vector<MyConstraint *> result;
  CallInst *call_inst = cast<CallInst>(I);
  
  // Get function from instruction
  Function *fn = call_inst->getCalledFunction();
  std::string function_name = "";

  // If no function, name can be taken from instruction operand
  if (fn) {
    function_name = fn->getName().str();
  } else {
    function_name = convert_name_to_string(I->getOperand(0));
  }
  
  // If function no declared, check name for predefined non-deterministic functions
  if (!fn || fn->isDeclaration()) {
    if (function_name.find(UNSIGNED_UINT_FUNCTION, 0) != std::string::npos) {
      
      result.push_back(new ComparisonConstraint(convert_name_to_string(I), ">=", "0"));
      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), "<=", "4294967295"));     
    
    } else if (function_name.find(UNSIGNED_SHORT_FUNCTION, 0) !=
               std::string::npos) {

      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), ">=", "(- 32768)"));
      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), "<=", "32767"));

    } else if (function_name.find(UNSIGNED_USHORT_FUNCTION, 0) !=
               std::string::npos) {

      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), ">=", "0"));
      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), "<=", "65535"));

    } else if (function_name.find(UNSIGNED_UCHAR_FUNCTION, 0) !=
               std::string::npos) {
      
      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), ">=", "0"));
      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), "<=", "255"));
    
    } else if (function_name.find(UNSIGNED_CHAR_FUNCTION, 0) != std::string::npos) {
    
      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), ">=", "(- 128)"));
      result.push_back(
          new ComparisonConstraint(convert_name_to_string(I), "<=", "127"));
    
    } else {
      // If no predefined function, ignore call and add true constraint
      result.push_back(new MyPredicate("true"));
    }   
    return result;
  }
  
  auto predicate = new FunctionPredicate(function_name);
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
  if (function_info->e_index == 0) {
    predicate->vars.push_back(MyVariable("false"));
  } else {
    predicate->vars.push_back(
        MyVariable("e" + std::to_string(function_info->e_index), "Bool"));
  }
  
  // Add variables for output error variable
  ++function_info->e_index;
  predicate->vars.push_back(
      MyVariable("e" + std::to_string(function_info->e_index), "Bool"));

  // Add global variables input and output values
  for (auto &var : global_vars) {
    predicate->vars.push_back(
        MyVariable(var.first + "_" + std::to_string(var.second), "Int"));
    var.second++;
    predicate->vars.push_back(
        MyVariable(var.first + "_" + std::to_string(var.second), "Int"));
  }
 
  result.push_back(predicate);
  return result;
}

// Create constraint for zext instruction
MyConstraint * transform_zext(Instruction *I) {
  MyVariable input(convert_name_to_string(I->getOperand(0)),
                   get_type(I->getOperand(0)->getType()));
  MyVariable output(convert_name_to_string(I),
                   get_type(I->getType()));
  
  if (input.type == "Bool" && output.type == "Int") {    
    return new ITEConstraint(output.name, "1", input.name, "0");  
  } else {
    return new UnaryConstraint(output.name, input.name);
  }
}

// Create constraint for trunc instruction 
MyConstraint* transform_trunc(Instruction *I) {
  MyVariable input(convert_name_to_string(I->getOperand(0)),
                   get_type(I->getOperand(0)->getType()));
  MyVariable output(convert_name_to_string(I), get_type(I->getType()));
  
  if (input.type == "Int" && output.type == "Bool") {
    return new BinaryConstraint(output.name, input.name, "!=", "0");
  } else {
    return new UnaryConstraint(output.name, input.name);
  }
}

// Create equality constraint for sext instruction
MyConstraint * transform_sext(Instruction *I) 
{
  return new UnaryConstraint(convert_name_to_string(I),
                     convert_name_to_string(I->getOperand(0)));
}

// Create constraint for logic instruction with boolean variables
BinaryConstraint * transform_logic_operand(Instruction *I) {
  auto op1_type = get_type(I->getOperand(0)->getType());
  auto op2_type = get_type(I->getOperand(1)->getType());

  if (op1_type == "Bool" && op2_type == "Bool") {
    return transform_binary_inst(I);
  } else {
    throw std::logic_error("Logic operation not on Bool");
  }
}

// Create constraint for load instruction with global variable
MyConstraint* transform_load_operand(Instruction *I) {

  std::string global_var_name = I->getOperand(0)->getName().str();
  int index = global_vars[global_var_name];

  LoadConstraint * con = new LoadConstraint();
  con->result = convert_name_to_string(I);
  con->value = global_var_name + "_" + std::to_string(index);
  
  return con;
}

// Create constraint for store instruction with global variable
MyConstraint * transform_store_operand(Instruction *I) {
  
  std::string global_var_name = I->getOperand(1)->getName().str();
  global_vars[global_var_name]++;
  int index = global_vars[global_var_name];

  StoreConstraint *con = new StoreConstraint();
  con->result = global_var_name + "_" + std::to_string(index);
  con->value = convert_operand_to_string(I->getOperand(0));

  return con;
}

// Transform instructions to constraints from instructions in basic block
std::vector<MyConstraint *> transform_instructions(MyBasicBlock *BB,
                                                MyFunctionInfo *function_info) {

  std::vector<MyConstraint *> result;
  function_info->e_index = 0;

  for (Instruction &I: BB->BB_link->instructionsWithoutDebug()) {
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
      std::vector<MyConstraint *> predicates =
          tranform_function_call(&I, function_info);
      result.insert(result.end(), predicates.begin(), predicates.end());
      break;
    }    
    default:
      throw std::logic_error("Not implemented instruction");
    }
  }
  return result;
}

// Create current function predicate not for call instruction
MyPredicate * get_function_predicate(MyFunctionInfo *function_info ,MyVariable e_in, MyVariable e_out) {

  // Create predicate
  std::string var_name;
  std::string var_type;
  Function *F = function_info->function_pointer;
  auto predicate = new MyPredicate(F->getName().str());
  
  // Add parameters
  for (auto arg = F->arg_begin(); arg != F->arg_end(); ++arg) {
    if (arg->getValueID() != Value::ConstantIntVal) {
      var_name = convert_name_to_string(arg);
      var_type = get_type(arg->getType());

      predicate->vars.push_back(MyVariable(var_name, var_type));
    }
  }

  // Add return value
  if (!F->getReturnType()->isVoidTy()) {
    predicate->vars.push_back(function_info->return_value);
  }

  if (!function_info->is_main_function) {
    // Add input and output errors
    predicate->vars.push_back(e_in);
    predicate->vars.push_back(e_out);
  }
   
  add_global_variables(predicate, function_info);

  return predicate;
}

// Return fail block predicate
MyPredicate * get_fail_block_predicate(MyFunctionInfo* function_info) {
  if (function_info->is_main_function) {
    // Return new predicate if main function
    return new MyPredicate(function_info->function_name + "_error");
  } else {
    // Return function predicate with output error
    return get_function_predicate(
        function_info, MyVariable("false"), MyVariable("true"));
  }
}

// Create predicate for basic block: Format {name}({variables}), ex. BB1(%x1,%x2)
MyPredicate * get_basic_block_predicate(MyBasicBlock *BB, bool isEntry,
                                MyFunctionInfo *function_info) {

  // Failed assert block
  if (BB->isFalseBlock) {
    return get_fail_block_predicate(function_info);
  }

  // Convert variables
  std::vector<MyVariable> vars;
  std::string var_name;
  std::string var_type;
  for (auto &v : BB->vars) {
    if (v->getValueID() != Value::ConstantIntVal) {
      var_name = convert_name_to_string(v);
      var_type = get_type(v->getType());

      vars.push_back(MyVariable(var_name, var_type));
    }
  }

  std::string suffix = isEntry ? "_entry" : "_exit" ;
  return new MyPredicate(BB->name + suffix, vars);
}

// Add constraints for global variables initialized values
void initialize_global_variables(Implication *implication,
                                                     MyFunctionInfo * function_info) {
  if (function_info->is_main_function) {
    // Main function takes initial values of variable
    auto globals = function_info->function_pointer->getParent()->globals();

    for (auto &var : globals) {
      if (var.getValueType()->isIntegerTy()) {
        auto name = var.getName().str();
        ++global_vars[name];

        StoreConstraint *store = new StoreConstraint();
        store->result = name + "_" + std::to_string(global_vars[name]);
        store->value = convert_operand_to_string(var.getInitializer());

        implication->constraints.push_back(store);
      }
    }
  } else {
    // No main function takes values of global variable
    // from input global variable in predicate
    for (auto &var : global_vars) {
      ++var.second;

      StoreConstraint * store = new StoreConstraint();
      store->result = var.first + "_" + std::to_string(var.second);
      store->value = var.first;

      implication->constraints.push_back(store);
    }
  }
}

// Add predicates for global variables initialized values
void initialize_global_variables(Implication *implication,
                                                     MyFunctionInfo * function_info) {
  if (function_info->is_main_function) {
    auto globals = function_info->function_pointer->getParent()->globals();

    for (auto &var : globals) {
      if (var.getValueType()->isIntegerTy()) {
        auto name = var.getName().str();
        ++global_vars[name];

        MyPredicate store;
        store.type = STORE;
        store.name = name + "_" + std::to_string(global_vars[name]);
        store.operand1 = convert_name_to_string(var.getInitializer());

        implication->predicates.push_back(store);
      }
    }
  } else {
    for (auto &var : global_vars) {
      ++var.second;

      MyPredicate store;
      store.type = STORE;
      store.name = var.first + "_" + std::to_string(var.second);
      store.operand1 = var.first;

      implication->predicates.push_back(store);
    }
  }
}

// Create first implication for function input and transfer to BB1
std::vector<Implication> get_entry_block_implications(MyFunctionInfo* function_info, MyBasicBlock * BB1) {

  std::vector<Implication> result;

  // Create predicate for entry basic block with function arguments
  MyBasicBlock BB_entry(nullptr, function_info->function_name + "0", 0);  
  Function *F = function_info->function_pointer;
  for (auto arg = F->arg_begin(); arg != F->arg_end(); ++arg) {
    add_variable(arg, &BB_entry);
  }
  auto predicate = get_basic_block_predicate(&BB_entry, true, function_info);
  add_global_variables(predicate, function_info);

  // Create first implication (true -> BBentry(x1,..))
  Implication implication(*predicate);
  implication.constraints.push_back(new MyPredicate("true"));
  result.push_back(implication);

  // Create implication for transfer to first basic block 
  // with initialized global variables
  auto BB1_predicate = get_basic_block_predicate(BB1, true, function_info);  
  Implication imp1(*BB1_predicate);
  imp1.constraints.push_back(predicate);
 
  initialize_global_variables(&imp1, function_info);
  
  if (!BB1->isFalseBlock) {
    add_global_variables(BB1_predicate, function_info);
  }
  imp1.head = *BB1_predicate;

  result.push_back(imp1);

  return result;
}

// Set variables for phi instruction, depending on label before
std::vector<UnaryConstraint *> transform_phi_instructions(MyBasicBlock *predecessor,
                                     MyBasicBlock *successor) {

  std::vector<UnaryConstraint *> result;
  Value *translation;

  for (Instruction &I : successor->BB_link->instructionsWithoutDebug()) {
    if (I.getOpcode() == Instruction::PHI) {
      translation = I.DoPHITranslation(successor->BB_link, predecessor->BB_link);

      result.push_back(new UnaryConstraint(convert_name_to_string(&I),
                       convert_operand_to_string(translation)));
    }
  }
  return result;
}

// Set variable in head predicate as prime when assigned new value in constraint
void set_prime_var_in_head(MyPredicate* head_predicate, std::string var_name) {
  for (unsigned int i = 0; i < head_predicate->vars.size(); i++) {
    if (head_predicate->vars[i].name == var_name) {
      head_predicate->vars[i].isPrime = true;
      break;
    }
  }
}

// Create implication from entry to exit point in basic block
Implication create_entry_to_exit(MyBasicBlock *BB, MyFunctionInfo *function_info) {
  
  auto entry_predicate = get_basic_block_predicate(BB, true, function_info);
  add_global_variables(entry_predicate, function_info);
  
  auto constraints = transform_instructions(BB, function_info);
  
  auto exit_predicate = get_basic_block_predicate(BB, false, function_info);
  add_global_variables(exit_predicate, function_info);

  // Add last output error variable if some function called in BB
  if (BB->isFunctionCalled) {
    exit_predicate->vars.push_back(MyVariable("e" + std::to_string(function_info->e_index), "Bool"));
  }
  
  Implication implication(*exit_predicate);
  implication.constraints.push_back(entry_predicate);

  std::unordered_set<std::string> prime_vars;

  // Create prime variables in predicates when new assignemnt
  for (auto constraint : constraints) { 
    
    if (FunctionPredicate *fp = dynamic_cast<FunctionPredicate *>(constraint)) {
      
      set_prime_var_in_head(exit_predicate, fp->changed_var);
      prime_vars.insert(fp->changed_var);
      
      // Set variables when assigned 
      for (unsigned int i = 0; i < fp->vars.size(); i++) {
        if (prime_vars.find(fp->vars[i].name) != prime_vars.end()) {
          fp->vars[i].isPrime = true;
        }
      }
    }

    else if (BinaryConstraint *bc = dynamic_cast<BinaryConstraint *>(constraint)) {
            
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

    else if (UnaryConstraint *uc = dynamic_cast<UnaryConstraint *>(constraint)) {
      
      // Set operands when assigned before
      if (prime_vars.find(uc->value) != prime_vars.end()) {
        uc->value = uc->value + PRIME_SIGN;
      }

      // Set assigned variable as prime in current constraint and head predicate
      set_prime_var_in_head(exit_predicate, uc->result);
      prime_vars.insert(uc->result);
      uc->result = uc->result + PRIME_SIGN;
    }

    else if (ITEConstraint *ite = dynamic_cast<ITEConstraint *>(constraint)) {
      
      // Set condition operand as prime when assigned before
      if (prime_vars.find(ite->condition) != prime_vars.end()) {
        ite->condition = ite->condition + PRIME_SIGN;
      }

      // Set assigned variable as prime in current constraint and head predicate
      set_prime_var_in_head(exit_predicate, ite->result);
      prime_vars.insert(ite->result);
      ite->result = ite->result + PRIME_SIGN;
    } 
    
    else if (LoadConstraint *lc = dynamic_cast<LoadConstraint *>(constraint)) {

      // Set assigned variable as prime in current constraint and head predicate
      set_prime_var_in_head(exit_predicate, lc->result);
      prime_vars.insert(lc->result);
      lc->result = lc->result + PRIME_SIGN;
    } 
    
    else if (StoreConstraint *sc = dynamic_cast<StoreConstraint *>(constraint)) {
      
      // Set operand as prime when assigned before
      if (prime_vars.find(sc->value) != prime_vars.end()) {
        sc->value = sc->value + PRIME_SIGN;
      }
    }
      
    implication.constraints.push_back(constraint);
  }
  implication.head = *exit_predicate;

  return implication;
}

// Return variable to for end of the predicate if function is called in basic block
MyVariable get_function_call_var(MyBasicBlock *BB, int e_index,
                                 MyBasicBlock *successor) {
  if (BB->last_instruction != nullptr && BB->successors.size() > 0) {
    if (BB->successors.size() != 2 ||
         successor->BB_link == BB->last_instruction->getOperand(2)) {
      return MyVariable("false");
    } else {
      return MyVariable("e" + std::to_string(e_index), "Bool");
    }
  } else {
    return MyVariable("false");
  }
}

// Transform basic blocks to implications
std::vector<Implication>
transform_basic_blocks(MyFunctionInfo* function_info) {
  
  std::vector<Implication> result;
  result = get_entry_block_implications(function_info, &function_info->basic_blocks[1]);

  for (auto &it : function_info->basic_blocks) {
    MyBasicBlock * BB = &it.second;

    // Skip failed assert basic blocks
    if (BB->isFalseBlock) {
      continue;
    }

    // Create implication of current basic block (entry -> exit)
    result.push_back(create_entry_to_exit(BB, function_info));
    
    // Create implications for transfers to successors
    for (auto &succ : BB->successors) {
      auto current_exit_predicate =
          get_basic_block_predicate(BB, false, function_info);
      add_global_variables(current_exit_predicate, function_info);

      add_global_variables(&current_exit_predicate, function_info);

      auto successor = &function_info->basic_blocks[succ];
      auto succ_predicate = get_basic_block_predicate(successor, true, function_info);

      // Create implication
      Implication implication(*succ_predicate);

      // Translate phi instructions
      auto phi_constraints = transform_phi_instructions(BB, successor);

      if (BB->isFunctionCalled) {
          current_exit_predicate->vars.push_back(get_function_call_var(BB, function_info->e_index, successor));
      }            

      // Add current BB exit predicate
      implication.constraints.push_back(current_exit_predicate);

      if (phi_constraints.size() > 0) {
        // Set prime variables
        for (auto constraint : phi_constraints) { 
          set_prime_var_in_head(succ_predicate, constraint->result);
          constraint->result = constraint->result + PRIME_SIGN;
          implication.constraints.push_back(constraint);          
        }
      }
      
      // Branch predicate if 2 successors
      if (BB->last_instruction != nullptr && BB->successors.size() > 0) {
        if (BB->successors.size() == 2) {
          auto br = transform_br(BB->last_instruction, successor->BB_link);
          if ((br->result == "true" && br->value == "false") ||
              (br->result == "false" && br->value == "true")) {
              continue;
          }
          implication.constraints.push_back(br);
        }
      }

      if (!successor->isFalseBlock) {
        add_global_variables(succ_predicate, function_info);
      }
      implication.head = *succ_predicate;
      result.push_back(implication);
    }

    // Add predicate if error in called function
    if (BB->isFunctionCalled) {
      auto fail = get_fail_block_predicate(function_info);
      Implication implication(*fail);
      
      auto current_exit_predicate = get_basic_block_predicate(BB, false, function_info);
      add_global_variables(current_exit_predicate, function_info);
      current_exit_predicate->vars.push_back(MyVariable("true"));
      implication.constraints.push_back(current_exit_predicate);

      result.push_back(implication);
    }

    // From return instruction to function predicate implication
    if (BB->isLastBlock) {
      auto fun_predicate = get_function_predicate(
          function_info, MyVariable("false"), MyVariable("false"));

      auto implication = Implication(*fun_predicate);

      auto current_exit_predicate =
          get_basic_block_predicate(BB, false, function_info);
      add_global_variables(current_exit_predicate, function_info);
      if (BB->isFunctionCalled) {
        current_exit_predicate->vars.push_back(MyVariable("false"));
      }
      implication.constraints.push_back(current_exit_predicate);

      result.push_back(implication);

    }
  }

  // Add error case implication
  if (function_info->is_main_function) {
    Implication implication = Implication(MyPredicate("false"));
    auto fail_predicate = get_fail_block_predicate(function_info);
    implication.constraints.push_back(fail_predicate);
    result.push_back(implication);
  } else {
    auto function_predicate =  get_function_predicate(function_info, MyVariable("true"), MyVariable("true"));
    Implication implication(*function_predicate);
    result.push_back(implication);
  }

  return result;
}

#pragma endregion

#pragma region Print implication
// Print implication into console in readable form
void print_implications(std::vector<Implication> implications)
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
void smt_declare_function(MyConstraint *predicate) {
  if (predicate->GetType() == PREDICATE || predicate->GetType() == FUNCTION) {
    if (MyPredicate *pred = dynamic_cast<MyPredicate *>(predicate)) {
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
void smt_declare_functions(std::vector<Implication> *implications) {
  std::unordered_set<std::string> declared;

  for (auto implication : *implications) {
    smt_declare_function(&implication.head);
    for (auto constraint : implication.constraints) {
      smt_declare_function(constraint);
    }
  }
}

// Print all constraints from implication
void smt_print_constraints(std::vector<MyConstraint *> constraints) {
  auto count = constraints.size();

  if (count == 1) {
      output << constraints[0]->GetSMT();
  } else {
      output << "(and ";

      for (auto p: constraints) {
        output << p->GetSMT();
        output << " ";
      }

    output << ')';
  }
}

// Print all variables from predicates in implication
int smt_quantifiers(Implication *implication, int indent) {
  std::map<std::string, std::string> vars;

  // Variables from head of implication
  for (auto v : implication->head.vars) {
      if (!v.isConstant) {
      auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
      vars.insert(std::make_pair(name, v.type));
      }
  }

  // Variables in predicates 
  for (auto &constraint : implication->constraints) {
    if (MyPredicate *pred = dynamic_cast<MyPredicate *>(constraint)) {
      for (auto &v : pred->vars) {
         if (!v.isConstant) {
            auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
            vars.insert(std::make_pair(name, v.type));
         }
      }
    }    
    else if (LoadConstraint *load = dynamic_cast<LoadConstraint *>(constraint)) {
      vars.insert(std::make_pair(load->value, "Int"));
    }
    else if (StoreConstraint *store = dynamic_cast<StoreConstraint *>(constraint)) {
      vars.insert(std::make_pair(store->result, "Int"));
    }
    if (p.type == LOAD) {
      vars.insert(std::make_pair(p.operand1, "Int"));
    }
    if (p.type == STORE) {
      vars.insert(std::make_pair(p.name, "Int"));
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
void smt_declare_implication(Implication* implication) {
  int indent = 0;
  output << std::string(indent++, ' ') << "(assert " << std::endl;

  // Write all variables used in implication
  indent =smt_quantifiers(implication, indent);

  if (!implication->constraints.empty()) {
    output << std::string(indent++, ' ') << "(=>  " << std::endl;

    // Convert predicates
    output << std::string(indent, ' ');
    smt_print_constraints(implication->constraints);
    output << std::endl;
  }
  // Convert head of implication
  output << std::string(indent, ' ');

  output << implication->head.GetSMT();
  output << std::endl;
  indent--;

  // Add ending parentheses
  while (indent >= 0) {
    output << std::string(indent--, ' ') << ")" << std::endl;
  }
}

// Convert implications
void smt_declare_implications(std::vector<Implication> *implications) {
  for (auto implication : *implications) {
    smt_declare_implication(&implication);
  }
}

// Convert my chc representation to SMT-LIB format
void smt_print_implications(std::vector<Implication> *implications) {

  /*output << "(set-logic HORN)" << std::endl;
  output << "(set-info :status sat)"
         << std::endl
         << std::endl;*/

  smt_declare_functions(implications);
  output << std::endl;

  smt_declare_implications(implications);

  output << std::endl;
  //output << "(check-sat)" << std::endl;

}

#pragma endregion

// Set global variables into vector at the beginning of pass
void set_global_variables(Function *F) {
  auto globals = F->getParent()->globals();

  int j = 0;
  for (auto &var : globals) {

    if (var.getValueType()->isIntegerTy()) {
      auto name = "g" + std::to_string(j);
      var.setName(name);

      global_vars[name] = 0;      

      j++;
    }    
  }
}

PreservedAnalyses CHCTransformPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {
  
  if (first_function) {
    set_global_variables(&F);

    first_function = false;
  }

  auto function_info = load_my_function_info(F);

  //print_info(function_info.basic_blocks);

  auto implications = transform_basic_blocks(&function_info);

  //print_implications(implications);

  smt_print_implications(&implications);

  return PreservedAnalyses::all();
}