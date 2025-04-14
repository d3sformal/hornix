/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "Preprocessing.hpp"
#include "chc/Backend.hpp"
#include "chc/ChcTransform.hpp"
#include "chc/SMTOut.hpp"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IRReader/IRReader.h"

#include <iostream>

using namespace hornix;

int main(int argc, char * argv[]) {
    if (argc <= 1)
    {
        std::cerr << "Provide an input file!" << std::endl;
        exit(1);
    }
    llvm::StringRef filename = argv[1];

    llvm::LLVMContext context;
    llvm::SMDiagnostic err;
    std::unique_ptr<llvm::Module> module = llvm::parseIRFile(filename, err, context);

    if (not module) {
        err.print("hornix", llvm::errs());
        return 1;
    }

    // module->print(llvm::outs(), nullptr);

    module = transform(std::move(module));

    // module->print(llvm::outs(), nullptr);

    auto chcs = toChc(*module);

    std::stringstream query_stream;
    SMTOutput{query_stream}.smt_print_implications(chcs);

    // SolverContext solver_context {
    // .solver = "golem",
    // .solver_dir = "/Users/blishko/projects/golem/build",
    // .args = {}
    // };
    // auto res = solve(query_stream.str(), std::move(solver_context));
    auto res = solve(query_stream.str());
    std::cout << res << std::endl;

    return 0;
}
