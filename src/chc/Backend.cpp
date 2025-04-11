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

SolverContext SolverContext::z3_default() {
    return {
    .solver = "z3",
    .solver_dir = std::nullopt,
    .args = {}
    };
}
Result solve(std::string query) {
    return solve(std::move(query), SolverContext::z3_default());
}


Result solve(std::string query, SolverContext context) {
    // Write the query to a temporary file
    std::string smtfile = std::tmpnam(nullptr);
    smtfile += ".smt2";
    std::ofstream tempFile(smtfile);
    if (!tempFile) {
        throw std::logic_error("Could not create a temporary file");
    }

    tempFile << query;
    tempFile.close();

    std::string response_path = smtfile + ".out";
    std::optional<std::string> solver_dir = context.solver_dir.has_value() ? context.solver_dir.value() + fs::path::preferred_separator : std::optional<std::string>{};
    std::string command = solver_dir.value_or("") + context.solver + " " + context.args + " " + smtfile + " >" + response_path;
    std::system(command.c_str());

    std::remove(smtfile.c_str());

    std::ifstream file(response_path); // opens in text mode by default
    std::stringstream buffer;
    buffer << file.rdbuf(); // read entire file into buffer
    std::string response = buffer.str();
    return response;
}