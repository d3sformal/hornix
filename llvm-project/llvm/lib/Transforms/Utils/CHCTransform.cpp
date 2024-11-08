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

std::string get_type(Type *type);
std::string convert_name_to_string(Value *BB);

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

  if (I->getOpcode() == Instruction::Call) {
    
    if (CallInst *call_inst = dyn_cast<CallInst>(I)) {

      Function *fn = call_inst->getCalledFunction();
      if (fn) {

        auto function_name = fn->getName().str();

        for (auto assert : ASSERT_FUNCTIONS) {

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
            function_info->return_value = MyVariable(convert_name_to_string(o));
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
// Convert Value name to std::string
std::string convert_name_to_string(Value *BB) {
  std::string block_address;
  raw_string_ostream string_stream(block_address);

  BB->printAsOperand(string_stream, false);

  return string_stream.str();
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
  std::string sign;
  CmpInst *CmpI = (CmpInst *)I;
  switch (CmpI->getPredicate()) {
  case CmpInst::ICMP_EQ:
    sign = "=";
    break;
  case CmpInst::ICMP_NE:
    sign = "!=";
    break;
  case CmpInst::ICMP_UGT:
  case CmpInst::ICMP_SGT:
    sign = ">";
    break;
  case CmpInst::ICMP_UGE:
  case CmpInst::ICMP_SGE:
    sign = ">=";
    break;
  case CmpInst::ICMP_ULT:
  case CmpInst::ICMP_SLT:
    sign = "<";
    break;
  case CmpInst::ICMP_ULE:
  case CmpInst::ICMP_SLE:
    sign = "<=";
    break;
  default:
    sign = "?";
    throw std::logic_error("Unknown comparison symbol.");
    break;
  }
  return sign;
}

// Create predicate for br instruction
MyPredicate transform_br(Instruction *I, BasicBlock * successor) {
  // Instruction must have 3 operands to jump
  if (I->getNumOperands() != 3) {
    throw new std::logic_error(
        "Wrong instruction. Too few function operands.");
  }

  std::string res = successor == I->getOperand(2) ? "true" : "false";

  return MyPredicate(convert_name_to_string(I->getOperand(0)), res);
}

// Create binary predicate from binary instructions
MyPredicate transform_binary_inst(Instruction *I) {
  std::string sign;
  switch (I->getOpcode()) {
  case Instruction::ICmp:
    sign = cmp_sign(I);
    break;
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

  return MyPredicate(convert_name_to_string(I),
                         convert_name_to_string(I->getOperand(0)), sign,
                         convert_name_to_string(I->getOperand(1)));
}

// Create function predicate for function call
MyPredicate tranform_function_call(Instruction *I,
                                   MyFunctionInfo *function_info) {

  // Get function from instruction
  CallInst *call_inst = dyn_cast<CallInst>(I);
  Function *fn = call_inst->getCalledFunction();
  std::string function_name = "";
  if (fn) {
    function_name = fn->getName().str();
  }
  
  if (!fn || fn->isDeclaration()) {
    if (function_name.find(UNSIGNED_INT_FUNCTION, 0) != std::string::npos) {
      return MyPredicate(convert_name_to_string(I), ">=", "0");
    } else {
      return MyPredicate("true");
    }    
  }

  auto predicate = MyPredicate(function_name);

  predicate.type = FUNCTION;
  std::string var_name;
  std::string var_type;

  // Add parameters
  for (auto arg = call_inst->arg_begin(); arg != call_inst->arg_end(); ++arg) {
    if (arg->get()->getValueID() != Value::ConstantIntVal) {
      var_name = convert_name_to_string(arg->get());
      var_type = get_type(arg->get()->getType());

      predicate.vars.push_back(MyVariable(var_name, var_type));
    } else {
      var_name = convert_name_to_string(arg->get());

      predicate.vars.push_back(MyVariable(var_name));
    }
  }

  // Add return variable
  if (!fn->getReturnType()->isVoidTy()) {
    var_name = convert_name_to_string(I);

    predicate.vars.push_back(MyVariable(var_name, get_type(fn->getReturnType()), true));
    predicate.changed_var = var_name;
  }

  // Add variables for input and output error
  if (function_info->e_index == 0) {
    predicate.vars.push_back(MyVariable("false"));
  } else {
    predicate.vars.push_back(
        MyVariable("e" + std::to_string(function_info->e_index), "Bool"));
  }
  ++function_info->e_index;
  predicate.vars.push_back(
      MyVariable("e" + std::to_string(function_info->e_index), "Bool"));
 
  return predicate;
}

// Create predicate for zext instruction from i1 to i8
MyPredicate transform_zext(Instruction *I) {
  MyVariable input(convert_name_to_string(I->getOperand(0)),
                   get_type(I->getOperand(0)->getType()));
  MyVariable output(convert_name_to_string(I),
                   get_type(I->getType()));
  
  if (input.type == "Bool" && output.type == "Int")
  {
    // Transform zext to ite predicate;
    MyPredicate pred;
    pred.type = ITE;
    pred.name = output.name;
    pred.condition = input.name;
    pred.operand1 = "1";
    pred.operand2 = "0";
    
    return pred;  
  } else {
    return MyPredicate(output.name, input.name);
  }
}

// Create predicate for trunc instruction from i8 to i1
MyPredicate transform_trunc(Instruction *I) {
  MyVariable input(convert_name_to_string(I->getOperand(0)),
                   get_type(I->getOperand(0)->getType()));
  MyVariable output(convert_name_to_string(I), get_type(I->getType()));
  

  if (input.type == "Int" && output.type == "Bool") {
    // Transform trunc to binary predicate
    return MyPredicate(output.name, input.name, "!=", "0");
  }

  return MyPredicate("true");
}

// Create equality predicate for sext instruction
MyPredicate transform_sext(Instruction *I) 
{
  return MyPredicate(convert_name_to_string(I),
                     convert_name_to_string(I->getOperand(0)));
}

MyPredicate transform_logic_operand(Instruction *I) {
  auto op1_type = get_type(I->getOperand(0)->getType());
  auto op2_type = get_type(I->getOperand(1)->getType());

  if (op1_type == "Bool" && op2_type == "Bool") {
    return transform_binary_inst(I);
  } else {
    throw std::logic_error("Logic operation not on Bool");
  }
}

// Transform instructions to predicates from instructions in basic block
std::vector<MyPredicate> transform_instructions(MyBasicBlock *BB,
                                                MyFunctionInfo *function_info) {

  std::vector<MyPredicate> result;
  function_info->e_index = 0;

  for (Instruction &I: BB->BB_link->instructionsWithoutDebug()) {

    switch (I.getOpcode()) {
    // Instructions with no predicate
    case Instruction::Br:
    case Instruction::CallBr:
    case Instruction::IndirectBr:
    case Instruction::PHI:
    case Instruction::Ret:
    case Instruction::Unreachable:
      break;
    // Instructions with 1 predicate
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
    // Transform logic instruction on booleans
    case Instruction::Xor:
    case Instruction::And:
    case Instruction::Or:
      result.push_back(transform_logic_operand(&I));
      break;
    case Instruction::Call:
      result.push_back(tranform_function_call(&I, function_info));
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
    default:
      throw std::logic_error("Not implemented instruction");
      break;
    }
  }
  return result;
}

// Create function predicate for current function
MyPredicate get_function_predicate(MyFunctionInfo *function_info ,MyVariable e_in, MyVariable e_out) {

  // Create predicate
  std::string var_name;
  std::string var_type;
  Function *F = function_info->function_pointer;
  auto predicate =
      MyPredicate(function_info->function_pointer->getName().str());
  
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
    predicate.vars.push_back(function_info->return_value);
  }

  if (!function_info->is_main_function) {
    // Add input and output errors
    predicate.vars.push_back(e_in);
    predicate.vars.push_back(e_out);
  }

  return predicate;
}

// Return fail block predicate
MyPredicate get_fail_block_predicate(MyFunctionInfo* function_info) {
  if (function_info->is_main_function) {
    // Return new predicate if main function
    return MyPredicate(function_info->function_name + "_error");
  } else {
    // Return function predicate with output error
    return get_function_predicate(function_info, MyVariable("false"), MyVariable("true"));
  }
}

// Create MyPredicate for basic : Format {name}({variables}), ex. BB1(%x1,%x2)
MyPredicate get_head_predicate(MyBasicBlock *BB, bool isEntry, MyFunctionInfo* function_info ) {

  // Failed assert block
  if (BB->isFalseBlock) {
    return get_fail_block_predicate(function_info);
  }

  // Normal basic block header
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

  return MyPredicate(BB->name + suffix, vars);

}

// Create first implication for function input and transfer to BB1
std::vector<Implication> get_entry_block_implications(MyFunctionInfo* function_info, MyBasicBlock * BB1) {

  std::vector<Implication> result;

  // Create basic block for entry
  MyBasicBlock BB_entry(nullptr, function_info->function_name + "0", 0);
  
  Function *F = function_info->function_pointer;
  // Load arguments as variables
  for (auto arg = F->arg_begin(); arg != F->arg_end(); ++arg) {
    add_variable(arg, &BB_entry);
  }

  MyPredicate predicate = get_head_predicate(&BB_entry, true, function_info);

  // Create first implication (true -> BBentry(x1,..))
  Implication imp(predicate);
  imp.predicates.push_back(
      MyPredicate("true"));

  result.push_back(imp);

  // Create transfer to BB1
  Implication imp1(get_head_predicate(BB1, true, function_info));
  imp1.predicates.push_back(predicate);
  result.push_back(imp1);

  return result;
}

// Set variables for phi instruction, depending on label before
std::vector<MyPredicate> transform_phi_instructions(MyBasicBlock *predecessor,
                                     MyBasicBlock *successor) {

  std::vector<MyPredicate> result;
  Value *translation;

  for (Instruction &I : successor->BB_link->instructionsWithoutDebug()) {
    if (I.getOpcode() == Instruction::PHI) {
      translation = I.DoPHITranslation(successor->BB_link, predecessor->BB_link);

      result.push_back(MyPredicate(convert_name_to_string(&I),
                       convert_name_to_string(translation)));
    }
  }
  return result;
}

// Create implication from entry to exit point in basic block
Implication create_entry_to_exit(MyBasicBlock *BB, MyFunctionInfo *function_info) {
  
  MyPredicate entry_predicate = get_head_predicate(BB, true, function_info);
  auto predicates = transform_instructions(BB, function_info);
  MyPredicate exit_predicate = get_head_predicate(BB, false, function_info);

  // Add last output error variable if some function called in BB
  if (BB->isFunctionCalled) {
    exit_predicate.vars.push_back(MyVariable("e" + std::to_string(function_info->e_index), "Bool"));
  }
  
  Implication imp(exit_predicate);
  imp.predicates.push_back(entry_predicate);

  std::unordered_set<std::string> prime_vars;

  // Create prime variables in predicates
  for (auto pred : predicates) { 

    if (pred.type == FUNCTION) {
      auto var_changed = pred.changed_var;

      for (unsigned int i = 0; i < exit_predicate.vars.size(); i++) {
        if (exit_predicate.vars[i].name == var_changed) {
            exit_predicate.vars[i].isPrime = true;
            break;
        }
      }

      prime_vars.insert(var_changed);

      for (unsigned int i = 0; i < pred.vars.size(); i++) {
        if (prime_vars.find(pred.vars[i].name) != prime_vars.end()) {
            pred.vars[i].isPrime = true;
        }
      }
    }

    else if (pred.type == UNARY || pred.type == BINARY || pred.type == ITE) {

      for (unsigned int i = 0; i < exit_predicate.vars.size(); i++) {
        if (exit_predicate.vars[i].name == pred.name) {
          exit_predicate.vars[i].isPrime = true;
          break;
        }
      }

      if (pred.type == ITE &&
          prime_vars.find(pred.condition) != prime_vars.end()) {
        pred.condition = pred.condition + PRIME_SIGN;
      } else {

        if (prime_vars.find(pred.operand1) != prime_vars.end()) {
          pred.operand1 = pred.operand1 + PRIME_SIGN;
        }

        if (pred.type == BINARY &&
            prime_vars.find(pred.operand2) != prime_vars.end()) {
          pred.operand2 = pred.operand2 + PRIME_SIGN;
        }
      }
      

      prime_vars.insert(pred.name);
      pred.name = pred.name + PRIME_SIGN;
    }

    imp.predicates.push_back(pred);
  }
  imp.head = exit_predicate;

  return imp;
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
      MyPredicate current_exit_predicate =
          get_head_predicate(BB, false, function_info);

      auto successor = &function_info->basic_blocks[succ];
      auto succ_predicate = get_head_predicate(successor, true, function_info);

      // Create implication
      Implication imp(succ_predicate);

      // Translate phi instructions
      auto phi_predicates = transform_phi_instructions(BB, successor);

      if (BB->isFunctionCalled) {
          current_exit_predicate.vars.push_back(get_function_call_var(BB, function_info->e_index, successor));
      }
      
      // Current BB exit predicate
      imp.predicates.push_back(current_exit_predicate);

      if (phi_predicates.size() > 0) {

        // Set prime variables
        for (auto pred : phi_predicates) { 

          for (unsigned int i = 0; i < succ_predicate.vars.size(); i++) {
              if (succ_predicate.vars[i].name == pred.name) {
                succ_predicate.vars[i].isPrime = true;
                break;
              }
          }
          pred.name = pred.name + PRIME_SIGN;
          imp.predicates.push_back(pred);
        }
      }
      
      // Branch predicate if 2 successors
      if (BB->last_instruction != nullptr && BB->successors.size() > 0) {
        if (BB->successors.size() == 2) {
          imp.predicates.push_back(
              transform_br(BB->last_instruction, successor->BB_link));
        }
      }

      imp.head = succ_predicate;
      result.push_back(imp);
    }

    // Add predicate if error in called function
    if (BB->isFunctionCalled) {
      Implication imp(get_fail_block_predicate(function_info));
      
      MyPredicate current_exit_predicate = get_head_predicate(BB, false, function_info);
      current_exit_predicate.vars.push_back(MyVariable("true"));
      imp.predicates.push_back(current_exit_predicate);

      result.push_back(imp);
    }

    // From return instruction to function predicate implication
    if (BB->isLastBlock) {
      auto imp = Implication(get_function_predicate(
          function_info, MyVariable("false"), MyVariable("false")));

      MyPredicate current_exit_predicate =
          get_head_predicate(BB, false, function_info);
      if (BB->isFunctionCalled) {
        current_exit_predicate.vars.push_back(MyVariable("false"));
      }
      imp.predicates.push_back(current_exit_predicate);

      result.push_back(imp);

    }
  }

  // Add error case implication
  if (function_info->is_main_function) {
    Implication i = Implication(MyPredicate("false"));
    i.predicates.push_back(MyPredicate(function_info->function_name + "_error"));
    result.push_back(i);
  } else {
    Implication i = Implication(
        get_function_predicate(function_info, MyVariable("true"), MyVariable("true")));
    result.push_back(i);
  }

  return result;
}

#pragma endregion

#pragma region Print implication
void print_head_predicate(MyPredicate *p) {
  errs() << p->name;

  if (p->vars.size() > 0) {
    errs() << "( ";
    auto first = 1;
    for (auto &v : p->vars) {
      if (!first) {
         errs() << ", ";
      } else {
         first = 0;
      }
      errs() << v.name ;
    }
    errs() << " )";
  }
}

void print_unary_predicate(MyPredicate *p) {
  errs() << p->Print();
}

void print_binary_predicate(MyPredicate *p) {
  errs() << p->Print();
}

void print_implications(std::vector<Implication> implications)
{
  errs() << "\nImplications:\n";
  for (auto &i : implications) {

    if (!i.predicates.empty()) {
      // Print predicates
      auto first = 1;
      for (auto &p : i.predicates) {
         if (!first) {
          errs() << " & ";
         } else {
          first = 0;
         }

         errs() << p.Print();
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
void smt_declare_function(MyPredicate *predicate) {
  if ( (predicate->type != FUNCTION && predicate->type != HEAD) ||
    predicate->name == "false" || predicate->name == "true" ||
    declared_functions.find(predicate->name) != declared_functions.end()
    ) {
    return;
  }
  output << "(declare-fun |" << predicate->name << "| (";

  for (auto v : predicate->vars) {
    if (v.isConstant) {
      if (v.name != "false" && v.name != "true") {
        output << " " << "Int";
      } else {
        output << " " << "Bool";
      }
    } else {
      output << " " << v.type;
    }
  }

  output << ") Bool )" << std::endl;

  declared_functions.insert(predicate->name);
}

// Declare basic blocks as functions
void smt_declare_functions(std::vector<Implication> *implications) {
  std::unordered_set<std::string> declared;

  for (auto imp : *implications) {
    smt_declare_function(&imp.head);
    for (auto predicate : imp.predicates) {
      smt_declare_function(&predicate);
    }
  }
}

// Print HeadPredicate
void smt_print_head_predicate(MyPredicate* predicate) {
  auto var_size = predicate->vars.size();
  if (var_size > 0) {
    output << "(";
  }

  output << predicate->name;
  for (auto v : predicate->vars) {
    auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
    output << " " << name;
  }
  if (var_size > 0) {
    output << " )";
  }
}

// Print UnaryPredicate
void smt_print_unary_predicate(MyPredicate *predicate) {
  output << "(= " << predicate->name << " " << predicate->operand1 << " )";
}

// Print ComparisionPredicate
void smt_print_comparison_predicate(MyPredicate *predicate) {
  output << "(" << predicate->sign << " " << predicate->name << " "
         << predicate->operand1 << " )";
}

// Print BinaryPredicate
void smt_print_binary_predicate(MyPredicate *predicate) {
  if (predicate->sign == "!=") {
    output << "(= " << predicate->name << " (not (= "
           << predicate->operand1 << " " << predicate->operand2 << " )))";
  } else {
    output << "(= " << predicate->name << " (" << predicate->sign << " "
           << predicate->operand1 << " " << predicate->operand2 << " ))";
  }
}

// Print ITE
void smt_print_ite_predicate(MyPredicate *predicate) {
  output << "(= " << predicate->name << " (ite " << predicate->condition << " "
         << predicate->operand1
           << " " << predicate->operand2 << " ))";
}

// Call print for predicate
void smt_print_predicate(MyPredicate *predicate) {
  switch (predicate->type) {
    case BINARY:
      smt_print_binary_predicate(predicate);
      return;
    case UNARY:
      smt_print_unary_predicate(predicate);
      return;
    case COMPARISON:
      smt_print_comparison_predicate(predicate);
      return;
    case HEAD:
    case FUNCTION:
      smt_print_head_predicate(predicate);
      return;
    case ITE:
      smt_print_ite_predicate(predicate);
      return;
    case UNKNOWN:
      return;
  }
}

// Print all predicates from implication
void smt_print_predicates(std::vector<MyPredicate> predicates) {
  auto predicate_size = predicates.size();

  if (predicate_size == 1) {
      smt_print_predicate(&predicates[0]);
  } else {
      output << "(and ";

      for (auto p: predicates) {
        smt_print_predicate(&p);
        output << " ";
      }

    output << ')';
  }
}

// Print all variables from implication. All variables are in head predicates.
int smt_quantifiers(Implication *imp, int indent) {
  std::map<std::string, std::string> vars;

  // Variables from head of implication
  for (auto v : imp->head.vars) {
      if (!v.isConstant) {
      auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
      vars.insert(std::make_pair(name, v.type));
      }
  }

  // Variables from head predicates from predicates
  for (auto &p : imp->predicates) {
    for (auto &v : p.vars) {
      if (!v.isConstant) {
        auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
        vars.insert(std::make_pair(name, v.type));
      }
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

  if (!implication->predicates.empty()) {
    output << std::string(indent++, ' ') << "(=>  " << std::endl;

    // Convert predicates
    output << std::string(indent, ' ');
    smt_print_predicates(implication->predicates);
    output << std::endl;
  }
  // Convert head of implication
  output << std::string(indent, ' ');

  smt_print_head_predicate(&implication->head);
  output << std::endl;
  indent--;

  // Add ending parentheses
  while (indent >= 0) {
    output << std::string(indent--, ' ') << ")" << std::endl;
  }
}

// Convert implications
void smt_declare_implications(std::vector<Implication> *implications) {
  for (auto imp : *implications) {
    smt_declare_implication(&imp);
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

PreservedAnalyses CHCTransformPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {

  auto function_info = load_my_function_info(F);

  auto implications = transform_basic_blocks(&function_info);

  //print_info(function_info.basic_blocks);

  //print_implications(implications);

  smt_print_implications(&implications);

  return PreservedAnalyses::all();
}