/*
 *  Copyright (c) 2024, Oliver Glitta <glittaoliver@gmail.com>
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef HELPERS_HPP
#define HELPERS_HPP

#include "utils/Liveness.hpp"

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>

#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_set>

namespace hornix {
const std::unordered_set<std::string> MAIN_FUNCTIONS = {"main"};

const std::unordered_set<std::string> ASSERT_FUNCTIONS = {
    "__assert", "__assert2", "__assert_fail", "__assert_perror_fail", "__assert_rtn", "_assert", "_wassert"
};

const std::string UNSIGNED_UINT_FUNCTION = "__VERIFIER_nondet_uint";
const std::string UNSIGNED_USHORT_FUNCTION = "__VERIFIER_nondet_ushort";
const std::string UNSIGNED_SHORT_FUNCTION = "__VERIFIER_nondet_short";
const std::string UNSIGNED_UCHAR_FUNCTION = "__VERIFIER_nondet_uchar";
const std::string UNSIGNED_CHAR_FUNCTION = "__VERIFIER_nondet_char";

enum MyPredicateType { BINARY, UNARY, COMPARISON, ITE, LOAD, EQUALITY, PREDICATE, FUNCTION, NOT, AND };


class BitvectorType {
public:
    using bvsize_t = unsigned;
    static BitvectorType make(bvsize_t size);

    bvsize_t size() const { return size_; }
private:
    BitvectorType(bvsize_t const size) : size_(size) {}
    bvsize_t size_ = 32u;
};

struct MyVariable {
    std::string name{};
    BitvectorType type;
    bool isConstant{};

    static MyVariable constant(std::string val) {
        return MyVariable{.name = std::move(val), .type = BitvectorType::make(32), .isConstant = true};
    }

    static MyVariable variable(std::string name, BitvectorType type) {
        return MyVariable{.name = std::move(name), .type = std::move(type), .isConstant = false};
    }
};

// TODO: This is probably not entirely correct
inline bool operator<(MyVariable const & first, MyVariable const & second) { return first.name < second.name; }

struct MyConstraint {
    virtual ~MyConstraint() {}
    virtual std::string Print() const { throw std::logic_error("Missing implementation of Print!"); }
    virtual MyPredicateType GetType() const = 0;
    virtual std::string GetSMT() const = 0;
};

struct MyPredicate : MyConstraint {
    std::string name;
    std::vector<MyVariable> vars;
    virtual ~MyPredicate() {}
    MyPredicate() {}
    MyPredicate(std::string name_) { name = name_; }
    MyPredicate(std::string name_, std::vector<MyVariable> vars_) {
        name = name_;
        vars = vars_;
    }

    std::string Print() const override {
        auto res = name;
        if (vars.size() > 0) {
            res += "( ";
            auto first = 1;
            for (auto & v : vars) {
                if (!first) {
                    res += ", ";
                } else {
                    first = 0;
                }
                res += v.name;
            }
            res += " )";
        }
        return res;
    }

    std::string GetSMT() const override {
        std::ostringstream res;
        auto var_size = vars.size();
        if (var_size > 0) { res << "("; }

        res << name;
        for (auto v : vars) {
            auto name = v.name;
            res << " " << name;
        }
        if (var_size > 0) { res << " )"; }

        return res.str();
    }

    MyPredicateType GetType() const override { return PREDICATE; }
};


struct ITEConstraint : MyConstraint {
    MyVariable result;
    MyVariable condition;
    MyVariable operand1;
    MyVariable operand2;
    ~ITEConstraint() override = default;
    ITEConstraint(MyVariable result_, MyVariable condition_, MyVariable operand1_, MyVariable operand2_)
        : result(std::move(result_)), condition(std::move(condition_)), operand1(std::move(operand1_)), operand2(std::move(operand2_)) {}

    std::string Print() const override { return result.name + "=ite(" + condition.name + "," + operand1.name + "," + operand2.name + ")"; }

    std::string GetSMT() const override {
        return +"(= " + result.name + " (ite " + condition.name + " " + operand1.name + " " + operand2.name + " ))";
    }

    MyPredicateType GetType() const override { return ITE; }
};
struct BinaryConstraint : MyConstraint {
    MyVariable result;
    MyVariable operand1;
    std::string sign;
    MyVariable operand2;
    ~BinaryConstraint() override = default;
    BinaryConstraint(MyVariable result, MyVariable operand1, std::string sign, MyVariable operand2)
        : result(std::move(result)), operand1(std::move(operand1)), sign(std::move(sign)), operand2(std::move(operand2))
    { }
    std::string Print() const override { return result.name + " = " + operand1.name + " " + sign + " " + operand2.name; }

    std::string GetSMT() const override {
        if (sign == "!=") {
            return "(= " + result.name + " (not (= " + operand1.name + " " + operand2.name + " )))";
        } else {
            return "(= " + result.name + " (" + sign + " " + operand1.name + " " + operand2.name + " ))";
        }
    }

    MyPredicateType GetType() const override { return BINARY; }
};
struct UnaryConstraint : MyConstraint {
    MyVariable result;
    MyVariable value;
    ~UnaryConstraint() override = default;
    UnaryConstraint(MyVariable result, MyVariable value) : result(std::move(result)), value(std::move(value)) {}
    std::string Print() const override { return result.name + " = " + value.name; }

    std::string GetSMT() const override { return "(= " + result.name + " " + value.name + " )"; }

    MyPredicateType GetType() const override { return UNARY; }
};
struct ComparisonConstraint : MyConstraint {
    MyVariable operand1;
    MyVariable operand2;
    std::string sign;
    ~ComparisonConstraint() override = default;
    ComparisonConstraint(MyVariable operand1, std::string sign, MyVariable operand2)
        : operand1(std::move(operand1)), sign(std::move(sign)), operand2(std::move(operand2)) {}
    std::string Print() const override { return operand1.name + sign + operand2.name; }
    std::string GetSMT() const override { return "(" + sign + " " + operand1.name + " " + operand2.name + " )"; }
    MyPredicateType GetType() const override { return COMPARISON; }
};
struct Equality : MyConstraint {
    MyVariable lhs;
    MyVariable rhs;
    ~Equality() override = default;
    Equality(MyVariable lhs, MyVariable rhs) : lhs(std::move(lhs)), rhs(std::move(rhs)) {}
    [[nodiscard]] std::string Print() const override { return lhs.name + " = " + rhs.name; }

    [[nodiscard]] std::string GetSMT() const override { return "(= " + lhs.name + " " + rhs.name + " )"; }

    [[nodiscard]] MyPredicateType GetType() const override { return EQUALITY; }
};

struct Not : MyConstraint {
    std::unique_ptr<MyConstraint> inner;
    ~Not() override = default;
    explicit Not(std::unique_ptr<MyConstraint> inner) : inner(std::move(inner)) {}

    [[nodiscard]] std::string Print() const override { return "not(" + inner->Print() + ")"; }

    [[nodiscard]] std::string GetSMT() const override { return "(not " + inner->GetSMT() + ")"; }

    [[nodiscard]] MyPredicateType GetType() const override { return NOT; }
};

struct And : MyConstraint {
    std::vector<std::unique_ptr<MyConstraint>> args;
    ~And() override = default;
    explicit And(std::vector<std::unique_ptr<MyConstraint>> args) : args(std::move(args)) {}

    [[nodiscard]] std::string GetSMT() const override {
        std::stringstream ss;
        ss << "(and ";
        for (auto const & arg : args) {
            ss << arg->GetSMT();
        }
        ss << ')';
        return ss.str();
    }

    [[nodiscard]] MyPredicateType GetType() const override { return AND; }
};

struct Implication {
    using Constraints = std::vector<std::unique_ptr<MyConstraint>>;
    // Implications structured as "predicates -> head"
    Constraints constraints;
    MyPredicate head;

    explicit Implication(MyPredicate head_) : head(std::move(head_)) {}
    Implication(MyPredicate head_, Constraints constraints_)
        : head(std::move(head_)), constraints(std::move(constraints_)) {}

    Implication(Implication && other) = default;
    Implication(Implication const & other) = delete;
    Implication & operator=(Implication const & other) = delete;
};

std::set<MyVariable> all_vars(Implication const & implication);

enum class BasicBlockPredicateType {ENTRY, EXIT};

inline std::string to_string(BasicBlockPredicateType type) {
    switch (type) {
        case BasicBlockPredicateType::ENTRY:
            return "entry";
        case BasicBlockPredicateType::EXIT:
            return "exit";
    }
    assert(false);
    return "";
}

struct MyBasicBlock {
    using ID_t = std::uint32_t;
    // Reference to basic block
    llvm::BasicBlock const * BB_link;
    // Name of basic block
    std::string name;
    // Id of basic block
    ID_t id;
    // List of ids of predecessors of basic block
    std::vector<ID_t> predecessors;
    // List of ids of successors of basic block
    std::vector<ID_t> successors;
    // True if block calls assert function and fails
    bool isFalseBlock;
    // True if it contains return instruction
    bool isLastBlock;
    // True if there is call instruction in basic block
    bool isFunctionCalled;

    MyBasicBlock(llvm::BasicBlock const * BB_link_, std::string name_, ID_t const id_)
        : BB_link(BB_link_),
          name(std::move(name_)),
          id(id_),
          isFalseBlock(false),
          isLastBlock(false),
          isFunctionCalled(false) {}
};

struct MyFunctionInfo {
    using BasicBlocks = std::map<MyBasicBlock::ID_t, MyBasicBlock>;
    // Indexed map of basic blocks
    BasicBlocks basic_blocks;
    // Function name
    std::string name;
    // True if function name is from MAIN_FUNCTIONS list
    bool is_main_function;
    // Type of variable to return from function
    std::optional<MyVariable> return_value = std::nullopt;
    // Pointer to llvm function struct
    llvm::Function const & llvm_function;
    // Error index
    int e_index;
    // Liveness information
    LivenessInfo liveness_info;

    MyFunctionInfo(llvm::Function const & function, std::string name, bool is_main)
        : name(std::move(name)), is_main_function(is_main), llvm_function(function), e_index(0) {}
};

inline bool isMainFunction(std::string const & function_name) {
    return MAIN_FUNCTIONS.find(function_name) != MAIN_FUNCTIONS.end();
}

inline bool isFailedAssertCall(llvm::Instruction const & I) {

    if (llvm::CallInst const * call_inst = llvm::dyn_cast<llvm::CallInst>(&I)) {

        llvm::Function * fn = call_inst->getCalledFunction();
        if (fn) {
            auto function_name = fn->getName().str();
            for (auto const & assert : ASSERT_FUNCTIONS) {
                // Platforms transforms function name differently,
                // check function name also as substring or added
                // '?' at the beginning
                if (assert == function_name) {
                    return true;
                } else if (function_name.find('?' + assert) == 0) {
                    return true;
                } else if (function_name.find(assert) == 0) {
                    return true;
                }
            }
        }
    }
    return false;
}
} // namespace hornix

#endif //HELPERS_HPP
