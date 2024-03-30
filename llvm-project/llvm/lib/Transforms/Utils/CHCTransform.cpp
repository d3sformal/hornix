#include "llvm/Transforms/Utils/CHCTransform.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "iostream"
#include <map>

using namespace llvm;

int var_index = 0;

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
// Add predicates from vector to MyBasicBlock struct
void add_predicates_to_implication(std::vector<Predicate> *predicates,
                                   Implication *implication) {
  for (auto &p : *predicates) {
    implication->predicates.push_back(p);
  }
}

// Convert Value name to std::string
std::string convert_name_to_string(Value *BB) {
  std::string block_address;
  raw_string_ostream string_stream(block_address);
  BB->printAsOperand(string_stream, false);

  return string_stream.str();
}

// Transform Cmp instruction
Predicate transform_cmp(Instruction *I) { 
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
  std::string exp = convert_name_to_string(I) + " = " +
         convert_name_to_string(I->getOperand(0)) + sign +
         convert_name_to_string(I->getOperand(1));
  return Predicate(exp);
}

// Transform Add instruction
Predicate transform_add(Instruction *I) {
  std::string exp = convert_name_to_string(I) + " = " +
         convert_name_to_string(I->getOperand(0)) + " + " +
         convert_name_to_string(I->getOperand(1));
  return Predicate(exp);
}

// Transform Sub instruction 
Predicate transform_sub(Instruction *I) {
  std::string exp = convert_name_to_string(I) + " = " +
         convert_name_to_string(I->getOperand(0)) + " - " +
         convert_name_to_string(I->getOperand(1));

  return Predicate(exp);
}

// Create predicate for br instruction
Predicate transform_br(Instruction *I, BasicBlock * successor) { 
  // Instruction must have 3 operands to jump
  if (I->getNumOperands() != 3) {
    throw new std::bad_exception(
        "Wrong instruction. Too few function operands");
  }
  
  std::string res = "false";
  if (successor == I->getOperand(2)) {
    res = "true";
  }

  std::string exp = convert_name_to_string(I->getOperand(0)) + " = " + res;

  return Predicate(exp);
}

// Transform instructions to predicates from instructions in basic block
std::vector<Predicate> transform_instructions(MyBasicBlock *BB) {
  
  std::vector<Predicate> result;
  
  for (Instruction &I: BB->BB_link->instructionsWithoutDebug()) {

    Predicate predicate;
    
    switch (I.getOpcode()) { 
    // Instructions with no predicate
    case Instruction::Br:
    case Instruction::PHI:
      break; 
    // Instructions with 1 predicate
    case Instruction::ICmp:
      result.push_back(transform_cmp(&I));
      break;
    case Instruction::Add:
      result.push_back(transform_add(&I));
      break;
    case Instruction::Sub:
      result.push_back(transform_sub(&I));
      break;
    default:
      //throw std::bad_exception("Not implemented instruction");
      break;
    }    
  }
  return result;
}

// Create Predicate for basic : Format {name}({variables}), ex. BB1(%x1,%x2)
Predicate get_head_predicate(MyBasicBlock * BB, bool isEntry) {

  // Failed assert block
  if (BB->isFalseBlock) {
    return Predicate("BB_error()");
  }

  // Normal basic block header
  std::vector<std::string> vars;
  std::string var_name;
  for (auto &v : BB->vars) {
    if (v->getValueID() != Value::ConstantIntVal) {
      var_name = convert_name_to_string(v);
      vars.push_back(var_name);
    }
  }

  std::string suffix = isEntry ? "_entry" : "_exit" ;
    
  return Predicate(BB->name + suffix, vars);

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

  Predicate predicate = get_head_predicate(&BB_entry, true);

  // Create first implication (true -> BBentry(x1,..))
  Implication imp(predicate);
  imp.predicates.push_back(Predicate("true"));
  result.push_back(imp);
  
  // Create transfer to BB1 
  Implication imp1(get_head_predicate(BB1, true));
  imp1.predicates.push_back(predicate);
  result.push_back(imp1);

  return result;
}

// Set variables for phi instruction, depending on label before
std::vector<Predicate> transform_phi_instructions(MyBasicBlock *predecessor,
                                     MyBasicBlock *successor) {

  std::vector<Predicate> result;
  Value *translation;

  for (Instruction &I : successor->BB_link->instructionsWithoutDebug()) {
    if (I.getOpcode() == Instruction::PHI) {
      translation = I.DoPHITranslation(successor->BB_link, predecessor->BB_link);

      std::string exp = convert_name_to_string(&I) + " = " + convert_name_to_string(translation);

      result.push_back(Predicate(exp));
    }    
  }
  return result;
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
    Predicate entry_predicate = get_head_predicate(BB, true);
    Predicate exit_predicate = get_head_predicate(BB, false);
    Implication imp(exit_predicate);
    imp.predicates.push_back(entry_predicate);
    auto predicates = transform_instructions(BB);
    add_predicates_to_implication(&predicates, &imp);
    result.push_back(imp);
    
    // Create implications for transfers to successors
    for (auto &succ : BB->successors) {
      auto successor = &my_blocks[succ];

      // Create implication
      Implication imp(get_head_predicate(successor, true));

      // Current BB exit predicate
      imp.predicates.push_back(exit_predicate);

      // Branch predicate if 2 successors
      if (BB->last_instruction != nullptr && BB->successors.size() == 2) {
         imp.predicates.push_back(
              Predicate(transform_br(BB->last_instruction, successor->BB_link)));
      }

      // Translate phi instructions
      auto predicates = transform_phi_instructions(BB, successor);
      add_predicates_to_implication(&predicates, &imp);
      
      result.push_back(imp); 
    }
  }

  // Add error case implication
  Implication i = Implication(Predicate("BB_error()"));
  i.predicates.push_back(Predicate("false"));
  result.push_back(i);

  return result;
}
#pragma endregion

#pragma region Print basic block
void print_BasicBlockHead(Predicate * p) {
  errs() << p->name << "(";
  auto first = 1;
  for (auto &v : p->vars) {
    if (!first) {
      errs() << ", ";
    } else {
      first = 0;
    }
    errs() << v;
  }
  errs() << ")";
}

void print_BBPredicate(Predicate *p) {
  
  switch (p->type) {
  case MyPredicateType::Expression:
    errs() << p->exp;
    break;
  case MyPredicateType::BasicBlockHead:
    print_BasicBlockHead(p);
    break;
  default:
    throw new std::bad_exception("Not implemented PredicateType");
  }
}

void print_implications(std::vector<Implication> implications) 
{ 
  errs() << "\nImplications:\n";
  for (auto &i : implications) {
    
    // Print predicates
    auto first = 1;
    for (auto &p : i.predicates) {
      if (!first) {
        errs() << " & ";
      } else {
        first = 0;
      }
      
      Predicate * pred = (Predicate *) &p;
      print_BBPredicate(pred);
    }

    errs() << " -> ";

    //Print head
    print_BBPredicate(&i.head);
    errs() << "\n";
  }
}
#pragma endregion

PreservedAnalyses CHCTransformPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {
  
  auto my_blocks = load_basic_block_info(F);

  auto implications = transform_basic_blocks(my_blocks, F);

  //PrintInfo(my_blocks);
  print_implications(implications);
 
  return PreservedAnalyses::all();
}