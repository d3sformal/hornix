/*
 *  Copyright (c) 2026, Hornix contributors
 *
 *  SPDX-License-Identifier: MIT
 */

#ifndef WITNESS_HPP
#define WITNESS_HPP

#include <filesystem>
#include <optional>
#include <string>

namespace hornix {

struct ViolationWitnessLocation {
    std::string file_name;
    unsigned line;
    unsigned column;
};

struct ViolationWitnessConfiguration {
    std::filesystem::path output_file;
    std::filesystem::path input_file;
    std::filesystem::path property_file;
    std::string data_model;
    std::string command_line;
    std::string format_version;
    // Set after selecting one reachable call when the program contains
    // multiple direct calls to the unreach-call target.
    std::optional<ViolationWitnessLocation> target_location;
};

// Validates the currently supported witness subset and writes a YAML 2.2
// unreach-call violation witness.  The caller invokes it only after Z3 has
// established that the error predicate is reachable.
void writeViolationWitness(ViolationWitnessConfiguration const & configuration);

// Reads an SV-COMP unreach-call property and returns the called error function.
std::string unreachCallTarget(std::filesystem::path const & property_file);

} // namespace hornix

#endif // WITNESS_HPP
