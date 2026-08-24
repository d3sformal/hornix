#include "Helpers.hpp"

#include <stdexcept>

namespace hornix {
namespace {
std::string decimalPowerOfTwo(unsigned exponent) {
    std::string value = "1";
    for (unsigned i = 0; i < exponent; ++i) {
        unsigned carry = 0;
        for (auto it = value.rbegin(); it != value.rend(); ++it) {
            unsigned digit = static_cast<unsigned>(*it - '0') * 2 + carry;
            *it = static_cast<char>('0' + digit % 10);
            carry = digit / 10;
        }
        if (carry != 0) { value.insert(value.begin(), static_cast<char>('0' + carry)); }
    }
    return value;
}
} // namespace

std::string smtTerm(MyVariable const & variable, IntegerTheory theory) {
    if (not variable.isConstant) { return variable.name; }
    if (not variable.isIntegerConstant) { return variable.name; }
    if (theory == IntegerTheory::Int) { return variable.name; }
    return "(_ bv" + variable.bitvectorValue + " " + std::to_string(variable.type.size()) + ")";
}

std::string smtOperator(std::string const & op, IntegerTheory theory) {
    if (theory == IntegerTheory::Int) {
        if (op == "slt" || op == "ult") { return "<"; }
        if (op == "sle" || op == "ule") { return "<="; }
        if (op == "sgt" || op == "ugt") { return ">"; }
        if (op == "sge" || op == "uge") { return ">="; }
        if (op == "eq") { return "="; }
        if (op == "sdiv" || op == "udiv") { return "div"; }
        if (op == "srem" || op == "urem") { return "mod"; }
        return op;
    }

    if (op == "+") { return "bvadd"; }
    if (op == "-") { return "bvsub"; }
    if (op == "*") { return "bvmul"; }
    if (op == "sdiv") { return "bvsdiv"; }
    if (op == "udiv") { return "bvudiv"; }
    if (op == "srem") { return "bvsrem"; }
    if (op == "urem") { return "bvurem"; }
    if (op == "and") { return "bvand"; }
    if (op == "or") { return "bvor"; }
    if (op == "xor") { return "bvxor"; }
    if (op == "shl") { return "bvshl"; }
    if (op == "lshr") { return "bvlshr"; }
    if (op == "ashr") { return "bvashr"; }
    if (op == "slt") { return "bvslt"; }
    if (op == "sle") { return "bvsle"; }
    if (op == "sgt") { return "bvsgt"; }
    if (op == "sge") { return "bvsge"; }
    if (op == "ult") { return "bvult"; }
    if (op == "ule") { return "bvule"; }
    if (op == "ugt") { return "bvugt"; }
    if (op == "uge") { return "bvuge"; }
    if (op == "eq") { return "="; }
    throw std::logic_error("Unsupported SMT operator: " + op);
}

std::string CastConstraint::GetSMT(IntegerTheory theory) const {
    auto const resultTerm = smtTerm(result, theory);
    auto const inputTerm = smtTerm(input, theory);
    if (theory == IntegerTheory::Int) {
        switch (kind) {
            case CastKind::ZExt:
                if (input.type.size() == 1 && result.type.size() != 1) {
                    return "(= " + resultTerm + " (ite " + inputTerm + " 1 0))";
                }
                return "(= " + resultTerm + " " + inputTerm + " )";
            case CastKind::SExt:
                return "(= " + resultTerm + " " + inputTerm + " )";
            case CastKind::Trunc:
                if (input.type.size() != 1 && result.type.size() == 1) {
                    return "(= " + resultTerm + " (not (= " + inputTerm + " 0)))";
                }
                if (result.type.size() < input.type.size()) {
                    return "(= " + resultTerm + " (mod " + inputTerm + " " +
                           decimalPowerOfTwo(result.type.size()) + " ))";
                }
                return "(= " + resultTerm + " " + inputTerm + " )";
        }
    }

    switch (kind) {
        case CastKind::ZExt:
            if (result.type.size() == input.type.size()) { return "(= " + resultTerm + " " + inputTerm + " )"; }
            if (input.type.size() == 1) {
                return "(= " + resultTerm + " (ite " + inputTerm + " (_ bv1 " +
                       std::to_string(result.type.size()) + ") (_ bv0 " + std::to_string(result.type.size()) + ")))";
            }
            return "(= " + resultTerm + " ((_ zero_extend " +
                   std::to_string(result.type.size() - input.type.size()) + ") " + inputTerm + "))";
        case CastKind::SExt:
            if (result.type.size() == input.type.size()) { return "(= " + resultTerm + " " + inputTerm + " )"; }
            if (input.type.size() == 1) {
                return "(= " + resultTerm + " (ite " + inputTerm + " ((_ repeat " +
                       std::to_string(result.type.size()) + ") (_ bv1 1)) (_ bv0 " +
                       std::to_string(result.type.size()) + ")))";
            }
            return "(= " + resultTerm + " ((_ sign_extend " +
                   std::to_string(result.type.size() - input.type.size()) + ") " + inputTerm + "))";
        case CastKind::Trunc:
            if (result.type.size() == input.type.size()) { return "(= " + resultTerm + " " + inputTerm + " )"; }
            if (result.type.size() == 1) {
                return "(= " + resultTerm + " (= ((_ extract 0 0) " + inputTerm + ") (_ bv1 1)))";
            }
            return "(= " + resultTerm + " ((_ extract " + std::to_string(result.type.size() - 1) +
                   " 0) " + inputTerm + "))";
    }
    throw std::logic_error("Unknown integer cast kind");
}

// TODO: Implement this as a visitor

using vars_t = std::set<MyVariable>;
void collect_vars(MyConstraint const * constraint, vars_t & vars) {
    auto process = [&](MyVariable const & var) {
        if (not var.isConstant) {
            vars.insert(var);
        }
    };
    if (MyPredicate const * pred = dynamic_cast<MyPredicate const *>(constraint)) {
        for (auto const & var : pred->vars) {
            process(var);
        }
    } else if (auto * equality = dynamic_cast<Equality const *>(constraint)) {
        process(equality->lhs);
        process(equality->rhs);
    } else if (auto * unary = dynamic_cast<UnaryConstraint const *>(constraint)) {
        process(unary->result);
        process(unary->value);
    } else if (auto * binary = dynamic_cast<BinaryConstraint const *>(constraint)) {
        process(binary->result);
        process(binary->operand1);
        process(binary->operand2);
    } else if (auto * cmp = dynamic_cast<ComparisonConstraint const *>(constraint)) {
        process(cmp->operand1);
        process(cmp->operand2);
    } else if (auto * ite = dynamic_cast<ITEConstraint const *>(constraint)) {
        process(ite->result);
        process(ite->condition);
        process(ite->operand1);
        process(ite->operand2);
    } else if (auto * cast = dynamic_cast<CastConstraint const *>(constraint)) {
        process(cast->result);
        process(cast->input);
    } else if (auto * neg = dynamic_cast<Not const *>(constraint)) {
        collect_vars(neg->inner.get(), vars);
    } else if (auto * conj = dynamic_cast<And const *>(constraint)) {
        for (auto const & arg : conj->args) {
            collect_vars(arg.get(), vars);
        }
    } else {
        throw std::logic_error("Unhandled constraint type!");
    }
}

std::set<MyVariable> all_vars(Implication const & implication) {
    std::set<MyVariable> vars;
    collect_vars(&implication.head, vars);
    for (auto const & constraint : implication.constraints) {
        collect_vars(constraint.get(), vars);
    }
    return vars;
}

BitvectorType BitvectorType::make(bvsize_t size) {
    return BitvectorType(size);
}

} // namespace hornix
