/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "CLI.hpp"
#include "Exceptions.hpp"
#include "Preprocessing.hpp"
#include "chc/Backend.hpp"
#include "chc/ChcTransform.hpp"
#include "chc/SMTOut.hpp"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IRReader/IRReader.h"

#include <iostream>
#include <filesystem>

using namespace hornix;
namespace fs = std::filesystem;

int main(int argc, char * argv[]) {

    Options options = parse(argc, argv);
    assert(options.hasOption(Options::INPUT_FILE));
    std::string path = fs::absolute(options.getOption(Options::INPUT_FILE).value()).lexically_normal().string();
    llvm::StringRef filename = path;

    llvm::LLVMContext context;
    llvm::SMDiagnostic err;
    std::unique_ptr<llvm::Module> module = llvm::parseIRFile(filename, err, context);

    if (not module) {
        err.print("hornix", llvm::errs());
        return 1;
    }

    // module->print(llvm::outs(), nullptr);

    module = transform(std::move(module));

    if (options.getOrDefault(Options::PRINT_IR, "false") == "true") {
        module->print(llvm::outs(), nullptr);
        return 0;
    }

    try {
        auto chcs = toChc(*module);
        std::stringstream query_stream;
        SMTOutput{query_stream}.smt_print_implications(chcs);
        if (options.getOrDefault(Options::PRINT_CHC, "false") == "true") {
            std::cout << query_stream.str() << std::endl;
            return 0;
        }

        auto res = solve(query_stream.str(),
            SolverContext::context_for_solver(
                options.getOrDefault(Options::SOLVER, std::string("z3")),
                options.getOption(Options::SOLVER_ARGS),
                options.getOption(Options::SOLVER_DIR)
            )
        );
        std::cout << res << std::endl;
        return 0;
    } catch (UnsupportedFeature const & problem) {
        std::cerr << problem.what() << std::endl;
        return 1;
    }
}
