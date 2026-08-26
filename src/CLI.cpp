/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "CLI.hpp"

#include "getopt.h"

#include <iostream>
#include <cstring>
#include <cassert>

namespace{
void printUsage() {
    std::cout <<
        "Usage: hornix [options] [-i] file\n"
        "\n"
        "-h,--help                  Print this help message\n"
        "--version                  Print version number of Hornix\n"
        "-i,--input <file>          Input file (option not required)\n"
        "--print-chc                Dump CHC to standard output and exit\n"
        "--print-ir                 Dump IR being translated to standard output and exit\n"
        "--solver <solver>          Horn solver to run (default: z3)\n"
        "--solver-dir='<dir>'       Directory with the chosen solver's executable\n"
        "--solver-args='<args>'     Arguments to pass to the chosen solver\n"
        "--clang-dir='<dir>'        Directory with the clang executable\n"
        "--integer-theory <theory>  Integer encoding: int (default) or bitvectors\n"
        "--data-model <model>       C data model: ILP32 or LP64\n"
        "--property <file>          SV-COMP property file (required for witnesses)\n"
        "--witness-output <file>    Write a YAML 2.2 violation witness for an unsafe result\n"
        "--witness-format <version> YAML witness format: 2.0, 2.1, or 2.2 (default: 2.2)\n"
        ;
    std::cout << std::flush;
}

bool isDisableKeyword(const char* word) {
    return strcmp(word, "no") == 0 or strcmp(word, "false") == 0 or strcmp(word, "disable") == 0;
}
}

namespace hornix {

const std::string Options::INPUT_FILE = "input";
const std::string Options::PRINT_CHC = "print-chc";
const std::string Options::PRINT_IR = "print-ir";
const std::string Options::SOLVER = "solver";
const std::string Options::SOLVER_ARGS = "solver-args";
const std::string Options::SOLVER_DIR = "solver-dir";
const std::string Options::CLANG_DIR = "clang-dir";
const std::string Options::INTEGER_THEORY = "integer-theory";
const std::string Options::DATA_MODEL = "data-model";
const std::string Options::PROPERTY = "property";
const std::string Options::WITNESS_OUTPUT = "witness-output";
const std::string Options::WITNESS_FORMAT = "witness-format";

Options parse(int argc, char ** argv) {

    Options res;
    int printVersion = 0;
    int printChc = 0;
    int printIR = 0;

    struct option long_options[] =
        {
            {"help", no_argument, nullptr, 'h'},
            {Options::INPUT_FILE.c_str(), required_argument, nullptr, 'i'},
            {Options::PRINT_CHC.c_str(), no_argument, &printChc, 1},
            {Options::PRINT_IR.c_str(), no_argument, &printIR, 1},
            {Options::SOLVER.c_str(), required_argument, nullptr, 0},
            {Options::SOLVER_DIR.c_str(), required_argument, nullptr, 0},
            {Options::SOLVER_ARGS.c_str(), required_argument, nullptr, 0},
            {Options::CLANG_DIR.c_str(), required_argument, nullptr, 0},
            {Options::INTEGER_THEORY.c_str(), required_argument, nullptr, 0},
            {Options::DATA_MODEL.c_str(), required_argument, nullptr, 0},
            {Options::PROPERTY.c_str(), required_argument, nullptr, 0},
            {Options::WITNESS_OUTPUT.c_str(), required_argument, nullptr, 0},
            {Options::WITNESS_FORMAT.c_str(), required_argument, nullptr, 0},
            {"version", no_argument, &printVersion, 1},
            {0, 0, 0, 0}
        };

    while (true) {
        int option_index = 0;

        int c = getopt_long(argc, argv, "i:h", long_options, &option_index);
        if (c == -1) { break; }

        switch (c) {
            case 0:
                if (long_options[option_index].flag == &printVersion) {
                    std::cout << "Hornix " << "0.2.0" << std::endl;
                    exit(0);
                }
                if (strcmp(long_options[option_index].name, Options::SOLVER.c_str()) == 0) {
                    res.addOption(Options::SOLVER, optarg);
                }
                if (strcmp(long_options[option_index].name, Options::SOLVER_DIR.c_str()) == 0) {
                    res.addOption(Options::SOLVER_DIR, optarg);
                }
                if (strcmp(long_options[option_index].name, Options::SOLVER_ARGS.c_str()) == 0) {
                    res.addOption(Options::SOLVER_ARGS, optarg);
                }
                if (strcmp(long_options[option_index].name, Options::CLANG_DIR.c_str()) == 0) {
                    res.addOption(Options::CLANG_DIR, optarg);
                }
                if (strcmp(long_options[option_index].name, Options::INTEGER_THEORY.c_str()) == 0) {
                    res.addOption(Options::INTEGER_THEORY, optarg);
                }
                if (strcmp(long_options[option_index].name, Options::DATA_MODEL.c_str()) == 0) {
                    res.addOption(Options::DATA_MODEL, optarg);
                }
                if (strcmp(long_options[option_index].name, Options::PROPERTY.c_str()) == 0) {
                    res.addOption(Options::PROPERTY, optarg);
                }
                if (strcmp(long_options[option_index].name, Options::WITNESS_OUTPUT.c_str()) == 0) {
                    res.addOption(Options::WITNESS_OUTPUT, optarg);
                }
                if (strcmp(long_options[option_index].name, Options::WITNESS_FORMAT.c_str()) == 0) {
                    res.addOption(Options::WITNESS_FORMAT, optarg);
                }
                break;
            case 'h':
                printUsage();
                exit(0);
            case 'i':
                res.addOption(Options::INPUT_FILE, optarg);
                break;
            default:
                exit(1);
        }
    }
    if (optind < argc) {
        if (optind < argc - 1) {
            std::cerr << "Error in parsing the command line argument" << '\n';
            printUsage();
            exit(1);
        }
        // Assume the last argument not assigned to any option is input file
        res.addOption(Options::INPUT_FILE, argv[optind]);
    }
    if (printChc) {
        res.addOption(Options::PRINT_CHC, "true");
    }
    if (printIR) {
        res.addOption(Options::PRINT_IR, "true");
    }
    return res;
}

} // namespace hornix
