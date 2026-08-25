/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "Backend.hpp"
#include "utils/ScopeGuard.hpp"

#include <llvm/ADT/SmallString.h>
#include <llvm/Support/FileSystem.h>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <fstream>
#include <sstream>
#include <sys/wait.h>

namespace fs = std::filesystem;

namespace hornix {
namespace {
fs::path createUniqueTemporaryFile(std::string const & model) {
    std::error_code ec;
    auto temporaryDirectory = fs::temp_directory_path(ec);
    if (ec || temporaryDirectory.empty()) {
        throw std::logic_error("Could not locate temporary directory");
    }

    llvm::SmallString<256> uniquePath;
    ec = llvm::sys::fs::createUniqueFile((temporaryDirectory / model).string(), uniquePath);
    if (ec) { throw std::logic_error("Could not create a temporary query file"); }
    return fs::path(std::string(uniquePath.begin(), uniquePath.end()));
}
} // namespace

SolverContext SolverContext::z3_default() {
    return {
    .solver = "z3",
    .solver_dir = std::nullopt,
    .args = {},
    };
}

SolverContext SolverContext::context_for_solver(std::string solver_name, std::optional<std::string> solver_args, std::optional<std::string> solver_dir) {
    return {
        .solver = std::move(solver_name),
        .solver_dir = std::move(solver_dir),
        .args = std::move(solver_args).value_or("")
    };
}



Result solve(std::string query) {
    return solve(std::move(query), SolverContext::z3_default());
}


Result solve(std::string query, SolverContext context) {
    auto const smtfile = createUniqueTemporaryFile("hornix-query-%%%%%%.smt2");
    fs::path response_path = smtfile;
    response_path.replace_extension(".out");
    ScopeGuard cleanup([&] {
        std::error_code ec;
        fs::remove(smtfile, ec);
        fs::remove(response_path, ec);
    });

    // Write the query to a temporary file
    std::ofstream tempFile(smtfile);
    if (!tempFile) {
        throw std::logic_error("Could not create a temporary file");
    }

    tempFile << query;
    tempFile.close();

    std::optional<std::string> solver_dir = context.solver_dir.has_value() ? context.solver_dir.value() + fs::path::preferred_separator : std::optional<std::string>{};
    std::string command = solver_dir.value_or("") + context.solver + " " + context.args + " " + smtfile.string() + " >" + response_path.string();
    int const solver_status = std::system(command.c_str());
    if (solver_status == -1) {
        throw std::runtime_error("Could not start solver '" + context.solver + "'");
    }
    if (WIFSIGNALED(solver_status)) {
        throw std::runtime_error("Solver '" + context.solver + "' was terminated by signal " +
                                 std::to_string(WTERMSIG(solver_status)));
    }
    if (!WIFEXITED(solver_status) || WEXITSTATUS(solver_status) != 0) {
        throw std::runtime_error("Solver '" + context.solver + "' exited with status " +
                                 std::to_string(WIFEXITED(solver_status) ? WEXITSTATUS(solver_status) : solver_status));
    }

    std::ifstream file(response_path); // opens in text mode by default
    if (!file) {
        throw std::runtime_error("Solver '" + context.solver + "' produced no result file");
    }
    std::stringstream buffer;
    buffer << file.rdbuf(); // read entire file into buffer
    std::string response = buffer.str();
    file.close();
    return response;
}
} // namespace hornix
