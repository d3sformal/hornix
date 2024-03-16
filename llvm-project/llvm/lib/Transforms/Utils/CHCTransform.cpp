#include "llvm/Transforms/Utils/CHCTransform.h"
#include "llvm/IR/CFG.h"
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

void addVar(llvm::Value *I, MyBasicBlock* my_block) {
  if (I->getType()->isLabelTy()) {
    return;
  }
  if (!I->hasName()) {
    I->setName("x" + std::to_string(var_index));
    ++var_index;
  }
  if (std::find(my_block->vars.begin(), my_block->vars.end(), I) !=
      my_block->vars.end()) {
    return;
  }
  my_block->vars.push_back(I);
}

std::uint8_t GetBlockIdByLink(
    BasicBlock *block,
    std::unordered_map<std::uint8_t, MyBasicBlock> my_blocks) {

  for (auto &it : my_blocks) {
    if (it.second.BB_link == block) {
      return it.first;
    }
  }

  return 0;
}

std::string get_block_reference(Value *BB) {
  std::string block_address;
  raw_string_ostream string_stream(block_address);
  BB->printAsOperand(string_stream, false);

  return string_stream.str();
}


BB_Predicate GetHeadPredicate(MyBasicBlock BB) {

  BB_Predicate predicate;
  predicate.name = BB.name;
  for (auto &v : BB.vars) {
    if (v->getValueID() != llvm::Value::ConstantIntVal) {
      std::string a = get_block_reference(v);
      predicate.vars.push_back(a);
    }
  }

  return predicate;
}

std::unordered_map<std::uint8_t, MyBasicBlock> LoadBasicBlockInfo(Function &F) {
  std::unordered_map<std::uint8_t, MyBasicBlock> mymap;

  int bb_index = 1;
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

  for (auto &it : mymap) {
    MyBasicBlock &BB = it.second;
    BasicBlock *block_link = BB.BB_link;

    for (auto pred : predecessors(block_link)) {
        BB.preds.push_back(GetBlockIdByLink(pred, mymap));
      }

    for (auto succ : successors(block_link)) {
      BB.succs.push_back(GetBlockIdByLink(succ, mymap));
    }

    for (Instruction &I : block_link->instructionsWithoutDebug()) {

      if (!I.getType()->isVoidTy()) {
        addVar(&I, &BB);
      }

      for (auto &o : I.operands()) {
        addVar(o, &BB);
      }
    }

    BB.predicate = GetHeadPredicate(BB);
  }

  return mymap;
}
#pragma endregion

#pragma region Print my basic blocks
void PrintInfo(std::unordered_map<std::uint8_t, MyBasicBlock> my_blocks) {
  
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
Implication GetEntryBlock(Function &F) {

  MyBasicBlock BB_entry;
  BB_entry.name = "BBentry";
  for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
    addVar(arg, &BB_entry);
  }

  BB_Predicate predicate = GetHeadPredicate(BB_entry);

  Implication imp;
  imp.head = predicate;
  return imp;
}

std::vector<Implication>
TransformBB(std::unordered_map<std::uint8_t, MyBasicBlock> my_blocks,
            Function &F) {
  
  std::vector<Implication> result;
  result.push_back(GetEntryBlock(F));

  for (auto &it : my_blocks) {
    MyBasicBlock * BB = &it.second;
    
    BB_Predicate * current_predicate = &BB->predicate;

    for (auto &succ : BB->succs) {
        auto succcesor = my_blocks[succ];
                
        Implication imp;
        imp.head = succcesor.predicate;

        imp.predicates.push_back(BB->predicate);
        result.push_back(imp); 
    }

  }
  return result;
}
#pragma endregion

#pragma region Print basic block
void PrintBBPredicate(BB_Predicate *p) {
  errs() << p->name << "(";
  for (auto &v : p->vars) {
    errs() << v << ", ";
  }
  errs() << ")";
}

void PrintImplications(std::vector<Implication> implications) 
{ 
  errs() << "\nImplications:\n";
  for (auto &i : implications) {
    for (auto &p : i.predicates) {
      //print predicates
       BB_Predicate * pred = (BB_Predicate *) &p;
       PrintBBPredicate(pred);
    }

    errs() << " -> ";
    PrintBBPredicate(&i.head);
    errs() << "\n";
  }
}
#pragma endregion

PreservedAnalyses CHCTransformPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {
  
  auto my_blocks = LoadBasicBlockInfo(F);

  //Transform 
  auto implications = TransformBB(my_blocks, F);



  //Print Result


  // Print info
  PrintInfo(my_blocks);

  PrintImplications(implications);
 

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