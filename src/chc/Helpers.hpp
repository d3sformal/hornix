/*
 *  Copyright (c) 2024, Oliver Glitta <glittaoliver@gmail.com>
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef HELPERS_HPP
#define HELPERS_HPP

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>

#include <map>
#include <sstream>
#include <string>
#include <unordered_set>

namespace hornix {
const std::unordered_set<std::string> MAIN_FUNCTIONS = {"main"};

const std::unordered_set<std::string> ASSERT_FUNCTIONS = {
    "__assert", "__assert2", "__assert_fail", "__assert_perror_fail", "__assert_rtn", "_assert", "_wassert"
};

constexpr char PRIME_SIGN = 'p';

const std::string UNSIGNED_UINT_FUNCTION = "__VERIFIER_nondet_uint";
const std::string UNSIGNED_USHORT_FUNCTION = "__VERIFIER_nondet_ushort";
const std::string UNSIGNED_SHORT_FUNCTION = "__VERIFIER_nondet_short";
const std::string UNSIGNED_UCHAR_FUNCTION = "__VERIFIER_nondet_uchar";
const std::string UNSIGNED_CHAR_FUNCTION = "__VERIFIER_nondet_char";

enum MyPredicateType { BINARY, UNARY, COMPARISON, ITE, LOAD, STORE, PREDICATE, FUNCTION };

struct MyVariable {
    std::string name{};
    std::string type{};
    bool isPrime{};
    bool isConstant{};

    static MyVariable constant(std::string val) {
        return MyVariable{.name = std::move(val), .type = {}, .isPrime = false, .isConstant = true};
    }

    static MyVariable variable(std::string name, std::string type) {
        return MyVariable{.name = std::move(name), .type = std::move(type), .isPrime = false, .isConstant = false};
    }

    static MyVariable prime_variable(std::string name, std::string type) {
        return MyVariable{.name = std::move(name), .type = std::move(type), .isPrime = true, .isConstant = false};
    }
};

struct MyConstraint {
    virtual ~MyConstraint() {}
    virtual std::string Print() const = 0;
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
                res += v.isPrime ? v.name + PRIME_SIGN : v.name;
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
            auto name = v.isPrime ? v.name + PRIME_SIGN : v.name;
            res << " " << name;
        }
        if (var_size > 0) { res << " )"; }

        return res.str();
    }

    MyPredicateType GetType() const override { return PREDICATE; }
};

struct FunctionPredicate : MyPredicate {
    std::string changed_var;
    virtual ~FunctionPredicate() {}
    FunctionPredicate() {}
    FunctionPredicate(std::string name_) { name = name_; }
    FunctionPredicate(std::string name_, std::vector<MyVariable> vars_) {
        name = name_;
        vars = vars_;
    }

    MyPredicateType GetType() const override { return FUNCTION; }
};
struct ITEConstraint : MyConstraint {
    std::string result;
    std::string operand1;
    std::string operand2;
    std::string condition;
    virtual ~ITEConstraint() {}
    ITEConstraint(std::string result_, std::string operand1_, std::string condition_, std::string operand2_) {
        result = result_;
        operand1 = operand1_;
        condition = condition_;
        operand2 = operand2_;
    }
    std::string Print() const override { return result + "=ite(" + condition + "," + operand1 + "," + operand2 + ")"; }

    std::string GetSMT() const override {
        return +"(= " + result + " (ite " + condition + " " + operand1 + " " + operand2 + " ))";
    }

    MyPredicateType GetType() const override { return ITE; }
};
struct BinaryConstraint : MyConstraint {
    std::string result;
    std::string operand1;
    std::string sign;
    std::string operand2;
    virtual ~BinaryConstraint() {}
    BinaryConstraint(std::string result_, std::string operand1_, std::string sign_, std::string operand2_) {
        result = result_;
        operand1 = operand1_;
        sign = sign_;
        operand2 = operand2_;
    }
    std::string Print() const override { return result + " = " + operand1 + " " + sign + " " + operand2; }

    std::string GetSMT() const override {
        if (sign == "!=") {
            return "(= " + result + " (not (= " + operand1 + " " + operand2 + " )))";
        } else {
            return "(= " + result + " (" + sign + " " + operand1 + " " + operand2 + " ))";
        }
    }

    MyPredicateType GetType() const override { return BINARY; }
};
struct UnaryConstraint : MyConstraint {
    std::string result;
    std::string value;
    virtual ~UnaryConstraint() {}
    UnaryConstraint(std::string result_, std::string value_) {
        result = result_;
        value = value_;
    }
    std::string Print() const override { return result + " = " + value; }

    std::string GetSMT() const override { return "(= " + result + " " + value + " )"; }

    MyPredicateType GetType() const override { return UNARY; }
};
struct ComparisonConstraint : MyConstraint {
    std::string operand1;
    std::string operand2;
    std::string sign;
    virtual ~ComparisonConstraint() {}
    ComparisonConstraint(std::string operand1_, std::string sign_, std::string operand2_) {
        operand1 = operand1_;
        operand2 = operand2_;
        sign = sign_;
    }
    std::string Print() const override { return operand1 + sign + operand2; }
    std::string GetSMT() const override { return "(" + sign + " " + operand1 + " " + operand2 + " )"; }
    MyPredicateType GetType() const override { return COMPARISON; }
};
struct LoadConstraint : MyConstraint {
    std::string result;
    std::string value;
    virtual ~LoadConstraint() {}
    LoadConstraint(std::string name_, std::string value_) {
        result = name_;
        value = value_;
    }
    std::string Print() const override { return result + " = " + value; }

    std::string GetSMT() const override { return "(= " + result + " " + value + " )"; }

    MyPredicateType GetType() const override { return LOAD; }
};
struct StoreConstraint : MyConstraint {
    std::string result;
    std::string value;
    virtual ~StoreConstraint() = default;
    StoreConstraint(std::string result_, std::string value_) {
        result = std::move(result_);
        value = std::move(value_);
    }
    std::string Print() const override { return result + " = " + value; }

    std::string GetSMT() const override { return "(= " + result + " " + value + " )"; }

    MyPredicateType GetType() const override { return STORE; }
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

struct MyBasicBlock {
    // Reference to basic block
    llvm::BasicBlock const * BB_link;
    // Name of basic block
    std::string name;
    // Id of basic block
    std::uint8_t id;
    // List of references to variables used in instructions of basic block and its predecessors
    std::unordered_set<llvm::Value const *> vars;
    // List of ids of predecessors of basic block
    std::vector<std::uint8_t> predecessors;
    // List of ids of successors of basic block
    std::vector<std::uint8_t> successors;
    // Reference to last br instruction of basic block
    llvm::Instruction const * last_instruction;
    // True if block calls assert function and fails
    bool isFalseBlock;
    // True if it contains return instruction
    bool isLastBlock;
    // True if there is call instruction in basic block
    bool isFunctionCalled;

    MyBasicBlock(llvm::BasicBlock const * BB_link_, std::string name_, std::uint8_t const id_)
        : BB_link(BB_link_),
          name(std::move(name_)),
          id(id_),
          last_instruction(nullptr),
          isFalseBlock(false),
          isLastBlock(false),
          isFunctionCalled(false) {}
};

struct MyFunctionInfo {
    using BasicBlocks = std::map<unsigned, MyBasicBlock>;
    // Indexed map of basic blocks
    BasicBlocks basic_blocks;
    // Function name
    std::string name;
    // True if function name is from MAIN_FUNCTIONS list
    bool is_main_function;
    // Type of variable to return from function
    MyVariable return_value;
    // Pointer to llvm function struct
    llvm::Function & llvm_function;
    // Error index
    int e_index;

    MyFunctionInfo(llvm::Function & function, std::string name, bool is_main)
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
