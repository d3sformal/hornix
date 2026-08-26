/*
 *  Copyright (c) 2026, Hornix contributors
 *
 *  SPDX-License-Identifier: MIT
 */

#ifndef WITNESS_HPP
#define WITNESS_HPP

#include <filesystem>
#include <string>

namespace hornix {

struct ViolationWitnessConfiguration {
    std::filesystem::path output_file;
    std::filesystem::path input_file;
    std::filesystem::path property_file;
    std::string data_model;
    std::string command_line;
    std::string format_version;
};

// Validates the currently supported witness subset and writes a YAML 2.2
// unreach-call violation witness.  The caller invokes it only after Z3 has
// established that the error predicate is reachable.
void writeViolationWitness(ViolationWitnessConfiguration const & configuration);

// Reads an SV-COMP unreach-call property and returns the called error function.
std::string unreachCallTarget(std::filesystem::path const & property_file);

} // namespace hornix

#endif // WITNESS_HPP
