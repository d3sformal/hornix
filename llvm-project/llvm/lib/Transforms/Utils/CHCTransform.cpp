#include "llvm/Transforms/Utils/CHCTransform.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "iostream"
#include <map>
#include <unordered_set>

using namespace llvm;

const auto PRIME_SIGN = 'x';
int var_index = 0;
auto &output = std::cout;

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

  // Find in basic block info
  if (std::find(my_block->vars.begin(), my_block->vars.end(), var) !=
      my_block->vars.end()) {
    return;
  }

  // Add to basic block info
  my_block->vars.push_back(var);
}

// Find id of basic block by reference to llvm class
std::uint8_t get_block_id_by_link(
    BasicBlock *block,
    std::unordered_map<std::uint8_t, MyBasicBlock> my_blocks) {

  for (auto &bb : my_blocks) {
    if (bb.second.BB_link == block) {
      return bb.first;
    }
  }

  throw std::exception("Unkown basic block.");
}

// See if call instruction calls _wassert function
bool isFailedAssertCall(Instruction *I) {

  if (I->getOpcode() == Instruction::Call) {
    if (CallInst *call_inst = dyn_cast<CallInst>(I)) {
      Function *fn = call_inst->getCalledFunction();
      return fn->getName() == StringRef("_wassert");
    }
  }

  return false;
}

// Name basic blocks and create own structs for basic blocks
std::unordered_map<std::uint8_t, MyBasicBlock>
load_basic_block_info(Function &F) {
  std::unordered_map<std::uint8_t, MyBasicBlock> myBasicBlocks;

  int bb_index = 1;

  // Name all basic blocks and create MyBasicBlock for each
  for (BasicBlock &BB : F) {
    if (!BB.hasName()) {
      auto name = "BB" + std::to_string(bb_index);
      BB.setName(name);
      
      MyBasicBlock myBB(&BB, name, bb_index);
      myBasicBlocks.insert(std::pair<std::uint8_t, MyBasicBlock>(bb_index, myBB));

      ++bb_index;
    }
  }

  // Set MyBasicBlock info
  for (auto &it : myBasicBlocks) {
    MyBasicBlock *BB = &it.second;
    BasicBlock *block_link = BB->BB_link;

    // Set Predecessors of blocks and variables from them
    for (auto pred : predecessors(block_link)) {
      // Find predecessor id
      auto pred_id = get_block_id_by_link(pred, myBasicBlocks);
      
      // Add predecessor
      BB->predecessors.push_back(pred_id);
      
      // Add new variables from predecessor
      for (auto v : myBasicBlocks[pred_id].vars) {
          add_variable(v, BB);
      }
    }

    // Set successors of block
    for (auto succ : successors(block_link)) {
      BB->successors.push_back(get_block_id_by_link(succ, myBasicBlocks));
    }

    // Find all used variables in instructions
    for (Instruction &I : block_link->instructionsWithoutDebug()) {
      
      // See if basic block handles failed assertion
      if (isFailedAssertCall(&I)) {
          BB->isFalseBlock = true;
          break;
      }

      // Remember last br instruction (should be only one)
      if (I.getOpcode() == Instruction::Br) {
          BB->last_instruction = &I;
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

  return myBasicBlocks;
}
#pragma endregion

#pragma region Print my basic blocks
void print_info(std::unordered_map<std::uint8_t, MyBasicBlock> my_blocks) {
  
  for (auto &it : my_blocks) {
    MyBasicBlock &BB = it.second;
    errs() << "BB: " << BB.name << " : " << BB.BB_link << "\n";

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
    return "Dif";
  }
}

// Transform Cmp instruction
std::string cmp_sign(Instruction *I) { 
  std::string sign;
  CmpInst *CmpI = (CmpInst *)I;
  switch (CmpI->getPredicate()) {
  case CmpInst::ICMP_EQ:
    sign = " = ";
    break;
  case CmpInst::ICMP_NE:
    sign = " != ";
    break;
  case CmpInst::ICMP_UGT:
  case CmpInst::ICMP_SGT:
    sign = " > ";
    break;
  case CmpInst::ICMP_UGE:
  case CmpInst::ICMP_SGE:
    sign = " >= ";
    break;
  case CmpInst::ICMP_ULT:
  case CmpInst::ICMP_SLT:
    sign = " < ";
    break;
  case CmpInst::ICMP_ULE:
  case CmpInst::ICMP_SLE:
    sign = " <= ";
    break;
  default:
    sign = " ? ";
    //throw std::bad_exception("Unknown symbol");
    break;
  }
  return sign;
}

// Create predicate for br instruction
UnaryPredicate transform_br(Instruction *I, BasicBlock * successor) { 
  // Instruction must have 3 operands to jump
  if (I->getNumOperands() != 3) {
    throw new std::bad_exception(
        "Wrong instruction. Too few function operands");
  }
  
  std::string res = successor == I->getOperand(2) ? "true" : "false";
  
  return UnaryPredicate(convert_name_to_string(I->getOperand(0)), res);
}

// Create binary predicate from binary instructions
BinaryPredicate transform_binary_inst(Instruction *I) {
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
  default:
    throw new std::exception("Wrong binary instruction.");
  }

  return BinaryPredicate(convert_name_to_string(I),
                         convert_name_to_string(I->getOperand(0)), sign,
                         convert_name_to_string(I->getOperand(1)));
}

// Transform instructions to predicates from instructions in basic block
Predicates transform_instructions(MyBasicBlock *BB) {
  
  Predicates result;
  
  for (Instruction &I: BB->BB_link->instructionsWithoutDebug()) {
        
    switch (I.getOpcode()) { 
    // Instructions with no predicate
    case Instruction::Br:
    case Instruction::PHI:
      break; 
    // Instructions with 1 predicate
    case Instruction::ICmp:
    case Instruction::Add:
    case Instruction::Sub:
      result.binary.push_back(transform_binary_inst(&I));
      break;
    default:
      //throw std::bad_exception("Not implemented instruction");
      break;
    }    
  }
  return result;
}

// Create Predicate for basic : Format {name}({variables}), ex. BB1(%x1,%x2)
HeadPredicate get_head_predicate(MyBasicBlock * BB, bool isEntry) {

  // Failed assert block
  if (BB->isFalseBlock) {
    return HeadPredicate("BB_error");
  }

  // Normal basic block header
  std::unordered_map<std::string, MyVariable> vars;
  std::string var_name;
  std::string var_type;
  for (auto &v : BB->vars) {
    if (v->getValueID() != Value::ConstantIntVal) {
      var_name = convert_name_to_string(v);
      var_type = get_type(v->getType());
      
      vars.insert(std::pair<std::string, MyVariable>(var_name, MyVariable(var_name, var_type)));
    }
  }

  std::string suffix = isEntry ? "_entry" : "_exit" ;
    
  return HeadPredicate(BB->name + suffix, vars);

}

// Create first implication for function input and transfer to BB1 
std::vector<Implication> get_entry_block_implications(Function &F, MyBasicBlock * BB1) {
  
  std::vector<Implication> result;

  // Create basic block for entry
  MyBasicBlock BB_entry(nullptr, "BB0", 0);
  // Load arguments as variables
  for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
    add_variable(arg, &BB_entry);
  }

  HeadPredicate predicate = get_head_predicate(&BB_entry, true);

  // Create first implication (true -> BBentry(x1,..))
  Implication imp(predicate);  
  imp.predicates.head.push_back(
      HeadPredicate("true"));

  result.push_back(imp);
  
  // Create transfer to BB1 
  Implication imp1(get_head_predicate(BB1, true));
  imp1.predicates.head.push_back(predicate);
  result.push_back(imp1);

  return result;
}

// Set variables for phi instruction, depending on label before
std::vector<UnaryPredicate> transform_phi_instructions(MyBasicBlock *predecessor,
                                     MyBasicBlock *successor) {

  std::vector<UnaryPredicate> result;
  Value *translation;

  for (Instruction &I : successor->BB_link->instructionsWithoutDebug()) {
    if (I.getOpcode() == Instruction::PHI) {
      translation = I.DoPHITranslation(successor->BB_link, predecessor->BB_link);

      result.push_back(UnaryPredicate(convert_name_to_string(&I),
                       convert_name_to_string(translation)));
    }    
  }
  return result;
}

// Create implication from entry to exit point in basic block
Implication create_entry_to_exit(MyBasicBlock *BB) {
  HeadPredicate entry_predicate = get_head_predicate(BB, true);
  HeadPredicate exit_predicate = get_head_predicate(BB, false);
  
  auto predicates = transform_instructions(BB);
  
  // Find changed variables
  for (unsigned int i = 0; i < predicates.unary.size(); i++) {
    exit_predicate.vars[predicates.unary[i].name].isPrime = true;
    predicates.unary[i].name = predicates.unary[i].name + PRIME_SIGN;
  }
  for (unsigned int i = 0; i < predicates.binary.size(); i++) {
    exit_predicate.vars[predicates.binary[i].name].isPrime = true;
    predicates.binary[i].name = predicates.binary[i].name + PRIME_SIGN;
  }

  // Create implication
  Implication imp(exit_predicate);
  imp.predicates = predicates;
  imp.predicates.head.push_back(entry_predicate);
  return imp;
}

// Transform basic blocks to implications
std::vector<Implication>
transform_basic_blocks(std::unordered_map<std::uint8_t, MyBasicBlock> my_blocks,
            Function &F) {
  
  std::vector<Implication> result;
  result = get_entry_block_implications(F, &my_blocks[1]);

  for (auto &it : my_blocks) {
    MyBasicBlock * BB = &it.second;
    
    // Skip failed assert basic blocks
    if (BB->isFalseBlock) {
      continue;
    }

    // Create implication of current basic block (entry -> exit)
    result.push_back(create_entry_to_exit(BB));
    
    HeadPredicate current_exit_predicate = get_head_predicate(BB, false);

    // Create implications for transfers to successors
    for (auto &succ : BB->successors) {
      auto successor = &my_blocks[succ];
      auto succ_predicate = get_head_predicate(successor, true);
      
      // Translate phi instructions
      auto phi_predicates = transform_phi_instructions(BB, successor);
      // Find changed variables
      for (unsigned int i = 0; i < phi_predicates.size(); i++) {
        succ_predicate.vars[phi_predicates[i].name].isPrime = true;
        phi_predicates[i].name = phi_predicates[i].name + PRIME_SIGN;        
      }

      // Create implication
      Implication imp(succ_predicate);

      imp.predicates.unary = phi_predicates;

      // Current BB exit predicate
      imp.predicates.head.push_back(current_exit_predicate);

      // Branch predicate if 2 successors
      if (BB->last_instruction != nullptr && BB->successors.size() == 2) {
         imp.predicates.unary.push_back(
             transform_br(BB->last_instruction, successor->BB_link));
      }
      
      result.push_back(imp); 
    }
  }

  // Add error case implication
  Implication i = Implication(HeadPredicate("false"));
  i.predicates.head.push_back(
      HeadPredicate("BB_error"));
  result.push_back(i);

  return result;
}
#pragma endregion

#pragma region Print implication
void print_head_predicate(HeadPredicate *p) {
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
      errs() << v.second.name ;
    }
    errs() << " )";
  }
}

void print_unary_predicate(UnaryPredicate *p) { 
  errs() << p->Print();
}

void print_binary_predicate(BinaryPredicate *p) { 
  errs() << p->Print(); 
}

void print_implications(std::vector<Implication> implications) 
{ 
  errs() << "\nImplications:\n";
  for (auto &i : implications) {
    
    // Print predicates
    auto first = 1;
    for (auto &p : i.predicates.head) {
      if (!first) {
        errs() << " & ";
      } else {
        first = 0;
      }
      
      print_head_predicate(&p);
    }

    for (auto &p : i.predicates.unary) {
      if (!first) {
        errs() << " & ";
      } else {
        first = 0;
      }

      print_unary_predicate(&p);
    }

    for (auto &p : i.predicates.binary) {
      if (!first) {
        errs() << " & ";
      } else {
        first = 0;
      }

      print_binary_predicate(&p);
    }

    errs() << " -> ";

    //Print head
    print_head_predicate(&i.head);
    errs() << "\n";
  }
}
#pragma endregion

#pragma region Print SMT-LIB format
// Print function declaration
void smt_declare_function(HeadPredicate *predicate) { 
  output << "(declare-fun |" << predicate->name << "| (";

  for (auto v : predicate->vars) {
    output << " " << v.second.type;
  }

  output << ") Bool )" << std::endl;
}

// Declare basic blocks as functions
void smt_declare_functions(std::vector<Implication> *implications) { 
  std::unordered_set<std::string> declared; 

  for (auto imp : *implications) {
    auto search = declared.find(imp.head.name);
    if (imp.head.name != "false") {
      if (search == declared.end()) {
        smt_declare_function(&imp.head);
        declared.insert(imp.head.name);
      }
    }
  }
}

// Print HeadPredicate
void smt_print_head_predicate(HeadPredicate* predicate) { 
  auto var_size = predicate->vars.size();
  if (var_size > 0) {
    output << "(";
  }
  
  output << predicate->name;
  for (auto v : predicate->vars) {
    auto name = v.second.isPrime ? v.first + PRIME_SIGN : v.first;
    output << " " << name;
  }
  if (var_size > 0) {
    output << " )";
  }
}

// Print UnaryPredicate
void smt_print_unary_predicate(UnaryPredicate *predicate) {
  output << "(= " << predicate->name << " " << predicate->value << " )";
}

// Print BinaryPredicate
void smt_print_binary_predicate(BinaryPredicate *predicate) {
  output << "(= " << predicate->name 
         << " (" << predicate->sign << " "
         << predicate->operand1 << " " 
         << predicate->operand2
    << " ))";
}

// Print first predicate from implication
void smt_print_first_predicate(Predicates* predicates) {
  if (predicates->head.size() > 0) {
    smt_print_head_predicate(&predicates->head[0]);
  } else if (predicates->unary.size() > 0) {
    smt_print_unary_predicate(
        &predicates->unary[0]);
  } else if (predicates->binary.size() > 0) {
    smt_print_binary_predicate(
        &predicates->binary[0]);
  }
}

// Print all predicates from implication
void smt_print_predicates(Predicates *predicates) { 
  auto predicate_size = predicates->head.size() + predicates->unary.size() +
                        predicates->binary.size();
  
  if (predicate_size == 1) {
    smt_print_first_predicate(predicates);
  } else {
      output << "(and ";

      for (auto p: predicates->head) {
        smt_print_head_predicate(&p);
      }
      for (auto p : predicates->unary) {
        smt_print_unary_predicate(&p);
      }
      for (auto p : predicates->binary) {
        smt_print_binary_predicate(&p);
      }
    output << ')';
  }
} 

// Print all variables from implication. All variables are in head predicates.
int smt_quantifiers(Implication *imp, int indent) {
  std::unordered_map<std::string, std::string> vars;
  
  // Variables from head of implication 
  for (auto v : imp->head.vars) {
    auto name = v.second.isPrime ? v.first + PRIME_SIGN : v.first;
    auto search = vars.find(name);
    if (search == vars.end()) {
      vars.insert(std::pair<std::string, std::string>(name, v.second.type));
    }
  }
  
  // Variables from head predicates from predicates
  for (auto h : imp->predicates.head) {
    for (auto v : h.vars) {
      auto name = v.second.isPrime ? v.first + PRIME_SIGN : v.first;
      auto search = vars.find(name);
      if (search == vars.end()) {
        vars.insert(std::pair<std::string, std::string>(name, v.second.type));
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

  output << std::string(indent++, ' ') << "(=>  " << std::endl;

  // Convert predicates
  output << std::string(indent, ' ');
  smt_print_predicates(&implication->predicates);
  output << std::endl;
  
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
  
  output << "(set-logic HORN)" << std::endl;
  output << "(set-info :status sat)"
         << std::endl 
         << std::endl;
  
  smt_declare_functions(implications);
  output << std::endl;

  smt_declare_implications(implications);

  output << std::endl;
  output << "(check-sat)" << std::endl;

}

#pragma endregion

PreservedAnalyses CHCTransformPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {
  
  auto my_blocks = load_basic_block_info(F);

  auto implications = transform_basic_blocks(my_blocks, F);

  //print_info(my_blocks);
    
  print_implications(implications);
 
  //output << "SMT-LIB: " << std::endl;

  smt_print_implications(&implications);

  return PreservedAnalyses::all();
}