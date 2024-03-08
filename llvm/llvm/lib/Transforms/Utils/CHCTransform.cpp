#include "llvm/Transforms/Utils/CHCTransform.h"
#include "llvm/IR/CFG.h"
#include "iostream"
#include <map>

using namespace llvm;

int var_index = 0;

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

std::unordered_map<std::string, MyBasicBlock> LoadBasicBlockInfo(Function &F) {
  std::unordered_map<std::string, MyBasicBlock> mymap;

  int bb_index = 1;
  for (BasicBlock &BB : F) {
    if (!BB.hasName()) {
      auto name = "BB" + std::to_string(bb_index);
      BB.setName(name);

      MyBasicBlock myBB;
      myBB.BB_link = &BB;
      myBB.name = name;

      mymap.insert(std::pair<std::string, MyBasicBlock>(name, myBB));

      ++bb_index;
    }
  }

  for (auto &it : mymap) {
    MyBasicBlock &BB = it.second;
    BasicBlock *block_link = BB.BB_link;

    for (auto pred : predecessors(block_link)) {
      BB.preds.push_back(pred);
    }

    for (auto succ : successors(block_link)) {
      BB.succs.push_back(succ);
    }

    for (Instruction &I : block_link->instructionsWithoutDebug()) {

      if (!I.getType()->isVoidTy()) {
        addVar(&I, &BB);
      }

      for (auto &o : I.operands()) {
        addVar(o, &BB);
      }
    }
  }

  return mymap;
}

void PrintInfo(std::unordered_map<std::string, MyBasicBlock> my_blocks) {
  
  for (auto &it : my_blocks) {
    MyBasicBlock &BB = it.second;
    errs() << "BB: " << BB.name << " : " << BB.BB_link << "\n";

    errs() << "Preds: "
           << "\n";
    for (auto pred : BB.preds) {
      pred->printAsOperand(errs(), true);
      errs() << "\n";
    }
    errs() << "\n";

    errs() << "Succs: "
           << "\n";
    for (auto succ : BB.succs) {
      succ->printAsOperand(errs(), true);
      errs() << "\n";
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

PreservedAnalyses CHCTransform::run(Function &F,
                                      FunctionAnalysisManager &AM) {
  
  auto my_blocks = LoadBasicBlockInfo(F);

  //TODO: Create git repo - change name of pass

  //Transform 



  //Print Result


  // Print info
  PrintInfo(my_blocks);
 

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