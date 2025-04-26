/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "Preprocessing.hpp"

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/InstructionNamer.h"

using namespace llvm;

namespace hornix {

std::unique_ptr<Module> transform(std::unique_ptr<Module> module) {
    PassBuilder PB;

    // Set up analysis managers
    LoopAnalysisManager     LAM;
    FunctionAnalysisManager FAM;
    CGSCCAnalysisManager    CGAM;
    ModuleAnalysisManager   MAM;

    // Register all the basic analyses
    PB.registerModuleAnalyses(MAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    // Build a function pass manager that runs mem2reg
    FunctionPassManager FPM;
    FPM.addPass(PromotePass()); // mem2reg
    FPM.addPass(InstructionNamerPass()); // instnamer, should always be last

    // Run the function pass manager over each function
    for (Function & f : *module) {
        if (!f.isDeclaration())
            FPM.run(f, FAM);
    }
    return module;
}

} // namespace hornix