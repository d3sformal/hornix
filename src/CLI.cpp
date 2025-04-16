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
        "--solver <solver>          Horn solver to run: z3, golem, eldarica (default: z3)\n"
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
const std::string Options::SOLVER = "solver";

Options parse(int argc, char ** argv) {

    Options res;
    int printVersion = 0;
    int printChc = 0;
    std::string solver = "z3";

    struct option long_options[] =
        {
            {"help", no_argument, nullptr, 'h'},
            {Options::INPUT_FILE.c_str(), required_argument, nullptr, 'i'},
            {Options::PRINT_CHC.c_str(), no_argument, &printChc, 1},
            {Options::SOLVER.c_str(), required_argument, nullptr, 0},
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
                    std::cout << "Hornix " << "0.1.0" << std::endl;
                    exit(0);
                }
                if (strcmp(long_options[option_index].name, Options::SOLVER.c_str()) == 0) {
                    res.addOption(Options::SOLVER, optarg);
                }
                break;
            case 'h':
                printUsage();
                exit(0);
            case 'i':
                res.addOption(Options::INPUT_FILE, optarg);
                break;
            default:
                abort();
        }
    }
    if (optind < argc) {
        if (optind < argc - 1) {
            std::cerr << "Error in parsing the command line argument" << '\n';
            printUsage();
            exit(1);
        }
        // Assume the last argument not assigned to any option is input file
        res.addOption("input", argv[optind]);
    }
    if (printChc) {
        res.addOption("print-chc", "true");
    }
    return res;
}

} // namespace hornix