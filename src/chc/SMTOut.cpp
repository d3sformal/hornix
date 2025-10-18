/*
 *  Copyright (c) 2024, Oliver Glitta <glittaoliver@gmail.com>
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "SMTOut.hpp"

namespace hornix {
void SMTOutput::smt_declare_function(MyConstraint const & predicate) {
    if (predicate.GetType() == PREDICATE || predicate.GetType() == FUNCTION) {
        if (auto const * pred = dynamic_cast<MyPredicate const *>(&predicate)) {
            if (declared_functions.find(pred->name) == declared_functions.end() && pred->name != "true" &&
                pred->name != "false") {

                output << "(declare-fun |" << pred->name << "| (";

                for (auto v : pred->vars) {
                    if (v.isConstant) {
                        if (v.name != "false" && v.name != "true") {
                            output << " "
                                   << "Int";
                        } else {
                            output << " "
                                   << "Bool";
                        }
                    } else {
                        output << " " << toSMTLibType(v.type);
                    }
                }

                output << ") Bool )" << std::endl;

                declared_functions.insert(pred->name);
                }
        }
    }
}

// Declare predicates as functions
void SMTOutput::smt_declare_functions(std::vector<Implication> const & implications) {
    for (auto const & implication : implications) {
        smt_declare_function(implication.head);
        for (auto const & constraint : implication.constraints) {
            smt_declare_function(*constraint);
        }
    }
}

// Print all constraints from implication
void SMTOutput::smt_print_constraints(Implication::Constraints const & constraints) {
    auto count = constraints.size();

    if (count == 1) {
        output << constraints[0]->GetSMT();
    } else {
        output << "(and ";

        for (auto const & p : constraints) {
            output << p->GetSMT();
            output << " ";
        }

        output << ')';
    }
}

// Print all variables from predicates in implication
int SMTOutput::smt_quantifiers(Implication const & implication, int indent) {
    auto vars = all_vars(implication);
    if (vars.empty()) { vars.insert(MyVariable::variable("HORNIX_UNUSED", BitvectorType::make(1))); }
    // Print variables
        output << std::string(indent++, ' ') << "(forall ( ";
        for (auto v : vars) {
            output << "( " << v.name << " " << toSMTLibType(v.type) << " )";
        }
        output << " )" << std::endl;
    return indent;
}

// Create assert for implication
void SMTOutput::smt_declare_implication(Implication const & implication) {
    int indent = 0;
    output << std::string(indent++, ' ') << "(assert " << std::endl;

    // Write all variables used in implication
    indent = smt_quantifiers(implication, indent);

    if (!implication.constraints.empty()) {
        output << std::string(indent++, ' ') << "(=>  " << std::endl;

        // Convert predicates
        output << std::string(indent, ' ');
        smt_print_constraints(implication.constraints);
        output << std::endl;
    }
    // Convert head of implication
    output << std::string(indent, ' ');

    output << implication.head.GetSMT();
    output << std::endl;
    indent--;

    // Add ending parentheses
    while (indent >= 0) {
        output << std::string(indent--, ' ') << ")" << std::endl;
    }
}

std::string SMTOutput::toSMTLibType(BitvectorType const & bvtype) {
    if (bvtype.size() == 1) { return "Bool"; }
    return "Int";
}


void SMTOutput::print_header() const {
    output << "(set-logic HORN)\n";
}

void SMTOutput::print_footer() const {
    output << "(check-sat)\n";
}

// Convert my chc representation to SMT-LIB format
void SMTOutput::smt_print_implications(std::vector<Implication> const & implications) {
    print_header();
    smt_declare_functions(implications);
    output << '\n';
    smt_declare_implications(implications);
    output << '\n';
    print_footer();
    output << std::flush;
}
} // namespace hornix
