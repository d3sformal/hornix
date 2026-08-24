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
#include "utils/ScopeGuard.hpp"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IRReader/IRReader.h"

#include <iostream>
#include <filesystem>

using namespace hornix;
namespace fs = std::filesystem;

namespace {
std::optional<fs::path> createUniqueTemporaryFile(std::string const & model) {
    std::error_code ec;
    auto temporaryDirectory = fs::temp_directory_path(ec);
    if (ec || temporaryDirectory.empty()) { return std::nullopt; }

    llvm::SmallString<256> uniquePath;
    ec = llvm::sys::fs::createUniqueFile((temporaryDirectory / model).string(), uniquePath);
    if (ec) { return std::nullopt; }
    return fs::path(std::string(uniquePath.begin(), uniquePath.end()));
}
} // namespace

struct Context {
    llvm::LLVMContext context;
    llvm::SMDiagnostic err;

    std::unique_ptr<llvm::Module> module_from_ir_file(fs::path const & path) {
        std::string path_as_string = path.string();
        llvm::StringRef filename = path_as_string;
        return llvm::parseIRFile(filename, err, context);
    }

    std::unique_ptr<llvm::Module> module_from_c_file(fs::path const & path, std::optional<fs::path> const & compiler_hint);
};

void fatalError(std::string const & message) {
    llvm::errs().changeColor(llvm::raw_ostream::RED, true);
    llvm::errs() << "[ERROR] ";
    llvm::errs().resetColor();
    llvm::errs() << message << '\n';
    exit(1);
}


int main(int argc, char * argv[]) {
    Options options = parse(argc, argv);
    if (not options.hasOption(Options::INPUT_FILE)) {
        fatalError("No input file specified!");
    }
    auto path = fs::absolute(options.getOption(Options::INPUT_FILE).value()).lexically_normal();
    if (not fs::exists(path)) {
        fatalError("Input file does not exist: " + path.string());
    }
    Context context;
    auto module = [&]() -> std::unique_ptr<llvm::Module> {
        auto extension = path.extension().string();
        if (extension == ".ll")
            return context.module_from_ir_file(path);
        if (extension == ".c" or extension == ".i") {
            return context.module_from_c_file(path, options.getOption(Options::CLANG_DIR));
        }
        fatalError("Unrecognized extension: " + extension);
        llvm_unreachable("Fatal error must exit!");
    }();

    if (not module) {
        context.err.print("hornix", llvm::errs());
        return 1;
    }

    // module->print(llvm::outs(), nullptr);

    module = transform(std::move(module));

    if (options.getOrDefault(Options::PRINT_IR, "false") == "true") {
        module->print(llvm::outs(), nullptr);
        return 0;
    }

    auto const integerTheoryOption = options.getOrDefault(Options::INTEGER_THEORY, "int");
    IntegerTheory const integerTheory = [&] {
        if (integerTheoryOption == "int") { return IntegerTheory::Int; }
        if (integerTheoryOption == "bitvectors") { return IntegerTheory::Bitvectors; }
        fatalError("Unknown integer theory: " + integerTheoryOption + ". Use 'int' or 'bitvectors'.");
        return IntegerTheory::Int;
    }();

    try {
        auto chcs = toChc(*module, integerTheory);
        std::stringstream query_stream;
        SMTOutput{query_stream, integerTheory}.smt_print_implications(chcs);
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
    } catch (std::exception const & problem) {
        std::cerr << "Internal error: " << problem.what() << std::endl;
        return 1;
    }
}

std::unique_ptr<llvm::Module> Context::module_from_c_file(fs::path const & path, std::optional<fs::path> const & compiler_hint) {
    auto clang_executable = [&]() -> fs::path {
        if (compiler_hint.has_value()) {
            auto clang_path = compiler_hint.value();
            clang_path.append(std::string("clang"));
            if (fs::exists(clang_path)) { return clang_path; }
        }
        // Hint did not work, try to locate on PATH
        return "clang";
    }();
    auto maybeIRFile = createUniqueTemporaryFile("hornix-ir-%%%%%%.ll");
    if (not maybeIRFile.has_value()) {
        llvm::errs() << "Error creating a temporary LLVM IR file when attempting to compile the source file!\n";
        return nullptr;
    }
    auto const ir_file = std::move(maybeIRFile.value());
    std::string const command = clang_executable.string() + " -Xclang -disable-O0-optnone -S -emit-llvm -o " + ir_file.string() + " " + path.string() + " 2> /dev/null";
    ScopeGuard guard([ir_file] {
        std::error_code ec;
        fs::remove(ir_file, ec);
    });
    int status = std::system(command.c_str());
    if (WIFEXITED(status)) {
        int const exitCode = WEXITSTATUS(status);
        if (exitCode == 0) {
            return module_from_ir_file(ir_file);
        }
        llvm::errs() << "Clang invocation did not succeed! Exit code: " << exitCode << '\n';
        return nullptr;
    }
    llvm::errs() << "Error when trying to call clang!\n";
    return nullptr;
}
