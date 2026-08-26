/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "CLI.hpp"
#include "Exceptions.hpp"
#include "Preprocessing.hpp"
#include "Witness.hpp"
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
#include <sstream>

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

    std::unique_ptr<llvm::Module> module_from_c_file(fs::path const & path, std::optional<fs::path> const & compiler_hint,
                                                     std::optional<std::string> const & data_model, bool with_debug_info);
};

void fatalError(std::string const & message) {
    llvm::errs().changeColor(llvm::raw_ostream::RED, true);
    llvm::errs() << "[ERROR] ";
    llvm::errs().resetColor();
    llvm::errs() << message << '\n';
    exit(1);
}

std::string commandLine(int argc, char * argv[]) {
    std::ostringstream result;
    for (int index = 0; index < argc; ++index) {
        if (index != 0) { result << ' '; }
        result << argv[index];
    }
    return result.str();
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
    auto const witness_output = options.getOption(Options::WITNESS_OUTPUT);
    auto const witness_format = options.getOption(Options::WITNESS_FORMAT);
    auto const data_model = options.getOption(Options::DATA_MODEL);
    std::optional<ViolationWitnessConfiguration> witness_configuration;
    if (witness_output.has_value()) {
        if (path.extension() != ".c") {
            fatalError("Violation witnesses currently require a single C source input.");
        }
        if (!data_model.has_value() || (data_model.value() != "ILP32" && data_model.value() != "LP64")) {
            fatalError("Violation witnesses require --data-model ILP32 or --data-model LP64.");
        }
        auto const format_version = witness_format.value_or("2.2");
        if (format_version != "2.0" && format_version != "2.1" && format_version != "2.2") {
            fatalError("Unknown witness format: " + format_version + ". Use 2.0, 2.1, or 2.2.");
        }
        auto const property_option = options.getOption(Options::PROPERTY);
        if (!property_option.has_value()) {
            fatalError("Violation witnesses require an SV-COMP unreach-call property via --property.");
        }
        auto const property_path = fs::absolute(property_option.value()).lexically_normal();
        if (!fs::exists(property_path)) {
            fatalError("Property file does not exist: " + property_path.string());
        }
        try {
            unreachCallTarget(property_path);
        } catch (std::exception const & error) {
            fatalError(error.what());
        }
        witness_configuration = ViolationWitnessConfiguration{
            .output_file = fs::absolute(witness_output.value()).lexically_normal(),
            .input_file = path,
            .property_file = property_path,
            .data_model = data_model.value(),
            .command_line = commandLine(argc, argv),
            .format_version = format_version,
        };
    } else if (witness_format.has_value()) {
        fatalError("--witness-format requires --witness-output.");
    } else if (data_model.has_value() && data_model.value() != "ILP32" && data_model.value() != "LP64") {
        fatalError("Unknown data model: " + data_model.value() + ". Use ILP32 or LP64.");
    }
    if (witness_configuration.has_value() &&
        (options.getOrDefault(Options::PRINT_IR, "false") == "true" || options.getOrDefault(Options::PRINT_CHC, "false") == "true")) {
        fatalError("--witness-output cannot be combined with --print-ir or --print-chc.");
    }
    Context context;
    auto module = [&]() -> std::unique_ptr<llvm::Module> {
        auto extension = path.extension().string();
        if (extension == ".ll")
            return context.module_from_ir_file(path);
        if (extension == ".c" or extension == ".i") {
            return context.module_from_c_file(path, options.getOption(Options::CLANG_DIR), data_model,
                                              witness_configuration.has_value());
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
    if (witness_configuration.has_value() && integerTheory != IntegerTheory::Bitvectors) {
        fatalError("Violation witnesses currently require --integer-theory bitvectors.");
    }
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
        if (witness_configuration.has_value() && res.rfind("unsat", 0) == 0) {
            writeViolationWitness(witness_configuration.value());
        }
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

std::unique_ptr<llvm::Module> Context::module_from_c_file(fs::path const & path, std::optional<fs::path> const & compiler_hint,
                                                           std::optional<std::string> const & data_model, bool with_debug_info) {
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
    std::string const data_model_flag = data_model.has_value() ? (data_model.value() == "ILP32" ? " -m32" : " -m64") : "";
    std::string const debug_flag = with_debug_info ? " -g" : "";
    std::string const command = clang_executable.string() + data_model_flag + debug_flag +
                                " -Xclang -disable-O0-optnone -S -emit-llvm -o " + ir_file.string() + " " + path.string() + " 2> /dev/null";
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
