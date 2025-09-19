/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "Backend.hpp"

#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <fstream>
#include <sstream>

namespace fs = std::filesystem;

namespace hornix {

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
    std::error_code ec;
    auto tmp_dir = fs::temp_directory_path(ec);
    if (tmp_dir.empty()) {
        throw std::logic_error("Could not locate temporary directory");
    }
    auto const smtfile = tmp_dir / "hornix_query.smt2";
    // Write the query to a temporary file
    std::ofstream tempFile(smtfile);
    if (!tempFile) {
        throw std::logic_error("Could not create a temporary file");
    }

    tempFile << query;
    tempFile.close();

    fs::path response_path = smtfile;
    response_path.replace_extension("out");
    std::optional<std::string> solver_dir = context.solver_dir.has_value() ? context.solver_dir.value() + fs::path::preferred_separator : std::optional<std::string>{};
    std::string command = solver_dir.value_or("") + context.solver + " " + context.args + " " + smtfile.string() + " >" + response_path.string();
    std::system(command.c_str());

    fs::remove(smtfile, ec);

    std::ifstream file(response_path); // opens in text mode by default
    std::stringstream buffer;
    buffer << file.rdbuf(); // read entire file into buffer
    std::string response = buffer.str();
    file.close();
    fs::remove(response_path);
    return response;
}
} // namespace hornix