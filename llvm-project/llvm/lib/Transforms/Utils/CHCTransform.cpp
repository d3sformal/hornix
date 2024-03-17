#include "llvm/Transforms/Utils/CHCTransform.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstrTypes.h"
#include "iostream"
#include <map>

using namespace llvm;

int var_index = 0;

#pragma region Create my basic blocks
void returnVar(llvm::Value* I, const char* text) {
  if (!I->hasName()) {
    I->setName("x" + std::to_string(var_index));
    ++var_index;
  }
  errs() << text << I->getName() << ": ";
  I->printAsOperand(errs(), true);
  errs() << ", ";
}

// Set name for variable and add to basic block info if not presented 
void add_variable(llvm::Value *I, MyBasicBlock* my_block) {
  
  // Skip labels and pointers
  if (I->getType()->isLabelTy() || I->getType()->isPointerTy()) {
    return;
  }

  // Set name
  if (!I->hasName()) {
    I->setName("x" + std::to_string(var_index));
    ++var_index;
  }

  // Find in basic block info
  if (std::find(my_block->vars.begin(), my_block->vars.end(), I) !=
      my_block->vars.end()) {
    return;
  }

  // Add to basic block info
  my_block->vars.push_back(I);
}

// Find id of basic block by reference to llvm class
std::uint8_t get_block_id_by_link(
    BasicBlock *block,
    std::unordered_map<std::uint8_t, MyBasicBlock> my_blocks) {

  for (auto &it : my_blocks) {
    if (it.second.BB_link == block) {
      return it.first;
    }
  }

  return 0;
}

// Name basic blocks and create own structs for basic blocks
std::unordered_map<std::uint8_t, MyBasicBlock> load_basic_block_info(Function &F) {
  std::unordered_map<std::uint8_t, MyBasicBlock> mymap;

  int bb_index = 1;

  // Name all basic blocks and create MyBasicBlock for each
  for (BasicBlock &BB : F) {
    if (!BB.hasName()) {
      auto name = "BB" + std::to_string(bb_index);
      BB.setName(name);

      MyBasicBlock myBB;
      myBB.BB_link = &BB;
      myBB.name = name;
      myBB.id = bb_index;

      mymap.insert(std::pair<std::uint8_t, MyBasicBlock>(bb_index, myBB));

      ++bb_index;
    }
  }

  // Set MyBasicBlock info
  for (auto &it : mymap) {
    MyBasicBlock *BB = &it.second;
    BasicBlock *block_link = BB->BB_link;

    // Set Predecessors of blocks and variables from them
    for (auto pred : predecessors(block_link)) {
      auto predId = get_block_id_by_link(pred, mymap);
        BB->preds.push_back(predId);
      for (auto v : mymap[predId].vars) {
          add_variable(v, BB);
      }
    }

    // Set successors of block
    for (auto succ : successors(block_link)) {
      BB->succs.push_back(get_block_id_by_link(succ, mymap));
    }

    // Find all used variables in instructions
    for (Instruction &I : block_link->instructionsWithoutDebug()) {

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

  return mymap;
}
#pragma endregion

#pragma region Print my basic blocks
void print_info(std::unordered_map<std::uint8_t, MyBasicBlock> my_blocks) {
  
  for (auto &it : my_blocks) {
    MyBasicBlock &BB = it.second;
    errs() << "BB: " << BB.name << " : " << BB.BB_link << "\n";

    errs() << "Preds: "
           << "\n";
    for (auto pred : BB.preds) {
      my_blocks[pred].BB_link->printAsOperand(errs(), true);
      errs() << " -> " << std::to_string(pred) << "\n";
    }
    errs() << "\n";

    errs() << "Succs: "
           << "\n";
    for (auto succ : BB.succs) {
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
// Convert llvm::Value name to std::string
std::string convert_name_to_string(Value *BB) {
  std::string block_address;
  raw_string_ostream string_stream(block_address);
  BB->printAsOperand(string_stream, false);

  return string_stream.str();
}

// Transform Cmp instruction
std::string transform_cmp(Instruction *I) { 
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
    break;
  }
  return convert_name_to_string(I) + " = " +
         convert_name_to_string(I->getOperand(0)) + sign +
         convert_name_to_string(I->getOperand(1));
}

// Transform Add instruction
std::string transform_add(Instruction *I) {
  return convert_name_to_string(I) + " = " +
         convert_name_to_string(I->getOperand(0)) + " + " +
         convert_name_to_string(I->getOperand(1));
}

// Transform Sub instruction 
std::string transform_sub(Instruction *I) {
  return convert_name_to_string(I) + " = " +
         convert_name_to_string(I->getOperand(0)) + " - " +
         convert_name_to_string(I->getOperand(1));
}

// Handle simple instructions with one predicate
BB_Predicate transform_simple_instructions(Instruction * I) { 
  BB_Predicate predicate;
  switch (I->getOpcode()) {
  case Instruction::ICmp:
    predicate.exp = transform_cmp(I);
    break;
  case Instruction::Add:
    predicate.exp = transform_add(I);
    break;
  case Instruction::Sub:
    predicate.exp = transform_sub(I);
    break;
  default:
    break;
  }
  return predicate;
}

// Transform instructions to predicates from instructions in basic block
std::vector<BB_Predicate> transform_instructions(MyBasicBlock *BB) {
  std::vector<BB_Predicate> result;
  
  for (Instruction &I: BB->BB_link->instructionsWithoutDebug()) {

    BB_Predicate predicate;
    
    switch (I.getOpcode()) { 
    case Instruction::ICmp:
    case Instruction::Add:
    case Instruction::Sub:
      result.push_back(transform_simple_instructions(&I)); 
      break;
    case Instruction::Br:
      //Simple Branch instruction -> no predicate
      break;
    case Instruction::CallBr:
      // do nothing
      predicate.exp = "CallBr";
      result.push_back(predicate); 
      break;

    case Instruction::IndirectBr:
      // do nothing
      predicate.exp = "IndirectBr";
      result.push_back(predicate);
      break;
    case Instruction::PHI:
      break;
    default:
      break;
    }    
  }
  return result;
}

// Create Predicate for basic : Format {name}({variables}), ex. BB1(%x1,%x2)
BB_Predicate get_head_predicate(MyBasicBlock * BB) {

  BB_Predicate predicate;
  predicate.name = BB->name;
  for (auto &v : BB->vars) {
    if (v->getValueID() != llvm::Value::ConstantIntVal) {
      std::string a = convert_name_to_string(v);
      predicate.vars.push_back(a);
    }
  }

  return predicate;
}

// Create first implication for function input and transfer to BB1 
std::vector<Implication> get_entry_block_implications(Function &F, MyBasicBlock * BB1) {

  MyBasicBlock BB_entry;
  BB_entry.name = "BBentry";
  for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
    add_variable(arg, &BB_entry);
  }

  BB_Predicate predicate = get_head_predicate(&BB_entry);

  Implication imp;
  imp.head = predicate;
  BB_Predicate pred;
  pred.exp = "true";
  imp.predicates.push_back(pred);
  std::vector<Implication> result;
  result.push_back(imp);
  
  Implication imp1;
  imp1.predicates.push_back(predicate);
  auto preds = transform_instructions(BB1);
  for (auto &p: preds) {
    imp1.predicates.push_back(p);
  }  
  imp1.head = get_head_predicate(BB1);
  result.push_back(imp1);

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
    
    // Load head predicate for current block
    BB_Predicate current_predicate = get_head_predicate(BB);

    for (auto &succ : BB->succs) {
      auto succcesor = &my_blocks[succ];

      // Create implication
      Implication imp;
      imp.head = get_head_predicate(succcesor);

      // Load predicates from instructions
      imp.predicates.push_back(current_predicate);
      auto preds = transform_instructions(succcesor);
      for (auto &p : preds) {
        imp.predicates.push_back(p);
      }

      result.push_back(imp); 
    }

  }
  return result;
}
#pragma endregion

#pragma region Print basic block
void print_BBPredicate(BB_Predicate *p) {
  if (p->name.empty()) {
    errs() << p->exp;
  } else {
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
      
      BB_Predicate * pred = (BB_Predicate *) &p;
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

  //Transform 
  auto implications = transform_basic_blocks(my_blocks, F);



  //Print Result


  // Print info
  //PrintInfo(my_blocks);

  print_implications(implications);
 

  /*
   errs() << "------------------------\n\n";     


    for (BasicBlock &BB : F) {

    errs() << "Basic block (name=" << BB.getName() << ")\n";

    errs() << "Prec= ";
    for (auto pred : predecessors(&BB)) {
      pred->printAsOperand(errs(), true);
      errs() << ", ";
    }
    errs() << "\n";

    errs() << "Succ= ";
    for (auto succ : successors(&BB)) {
      succ->printAsOperand(errs(), true);
      errs() << ", ";
    }
    errs() << "\n";

    errs() << "Vars= \n";
    for (Instruction &I : BB.instructionsWithoutDebug()) {
      errs() << "Instruction: " << I.getOpcode() << " : " << I.getOpcodeName()
             << "\n";

      if (!I.getType()->isVoidTy()) {
        returnVar(&I, "Ret: ");
        errs() << "\n";
      }

      for (auto &o : I.operands()) {
          returnVar(o, "");
      }
      errs() << "\n";
    }
    errs() << "\n\n";
  }

  
    errs() << "Function : " << F.getName() << "\nArgs: ";
   for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
       returnVar(arg, "");
   }
   errs() << "\n\n";


  
  for (BasicBlock &BB : F) {

    errs() << "Basic block (name=" << BB.getName() << ")\n";

    errs() << "Prec= ";
    std::vector<BasicBlock *> preds;
    for (auto pred : predecessors(&BB)) 
    {
      preds.push_back(pred);
      pred->printAsOperand(errs(), true);
      errs() << ", ";
    }
    errs() << "\n";

    errs() << "Succ= ";
    for (auto succ : successors(&BB))
    {
      succ->printAsOperand(errs(), true);
      errs() << ", ";
    }
    errs() << "\n";

    errs() << "Vars= \n";    
    for (Instruction &I : BB.instructionsWithoutDebug()) {
      errs() << "Instruction: " << I.getOpcode() << " : " << I.getOpcodeName()
               << "\n";

      if (!I.getType()->isVoidTy()) {
        returnVar(&I, "Ret: ");
        errs() << "\n";
      }

      if (I.getOpcode() == Instruction::PHI) {
        for (auto p : preds) {
          auto o = I.DoPHITranslation(&BB, p);
          p->printAsOperand(errs(), true);
          errs() << " -> ";
          returnVar(o, "");
        }
      } else {          
          for (auto &o : I.operands()) {
            returnVar(o, "");
          }
        }
      errs() << "\n";
    }    
    errs() << "\n\n";
  }

  */
  return PreservedAnalyses::all();
}