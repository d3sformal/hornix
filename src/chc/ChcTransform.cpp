/*
 *  Copyright (c) 2024, Oliver Glitta <glittaoliver@gmail.com>
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "ChcTransform.hpp"

#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Value.h>

using namespace llvm;

class Context {
public:
    static Context create(Module & module);

    void analyze(Function & F /*, FunctionAnalysisManager & AM*/);

    Implications finish();

private:
    void set_global_variables(Module & module);

    void add_global_variables(MyPredicate & predicate, MyFunctionInfo const & function_info);

    void initialize_global_variables(Implication & implication, MyFunctionInfo const & function_info);

    void add_variable(Value * var, MyBasicBlock * my_block);

    void set_basic_block_info(MyFunctionInfo * function_info);

    MyFunctionInfo load_my_function_info(Function & F);

    Implication::Constraints transform_function_call(Instruction * I, MyFunctionInfo & function_info);

    std::vector<Implication> transform_basic_blocks(MyFunctionInfo & function_info);

    Implication::Constraints transform_instructions(MyBasicBlock const & BB, MyFunctionInfo & function_info);

    std::unique_ptr<LoadConstraint> transform_load_operand(Instruction * I);

    std::unique_ptr<StoreConstraint> transform_store_operand(Instruction * I);

    std::vector<std::unique_ptr<UnaryConstraint>> transform_phi_instructions(MyBasicBlock const & predecessor,
                                                                             MyBasicBlock const & successor);

    std::vector<Implication> get_entry_block_implications(MyFunctionInfo const & function_info,
                                                          MyBasicBlock const & BB1);

    MyPredicate create_basic_block_predicate(MyBasicBlock const & BB, bool isEntry,
                                             MyFunctionInfo const & function_info);

    Implication create_entry_to_exit(MyBasicBlock const & BB, MyFunctionInfo & function_info);

    MyPredicate get_function_predicate(MyFunctionInfo const & function_info, MyVariable e_in, MyVariable e_out);

    MyPredicate get_fail_block_predicate(MyFunctionInfo const & function_info);

    std::unordered_map<std::string, int> global_vars;
    unsigned int var_index = 0;
    Implications implications;
};

// FIXME: Module should be const&
Context Context::create(Module & module) {
    Context context;
    context.set_global_variables(module);
    return context;
}

// FIXME: Do not rename variables of the module!
void Context::set_global_variables(Module & module) {
    auto globals = module.globals();
    unsigned j = 0u;
    for (GlobalValue & var : globals) {
        if (var.getValueType()->isIntegerTy()) {
            auto name = "g" + std::to_string(j);
            var.setName(name);
            global_vars[name] = 0;
            j++;
        }
    }
}

Implications Context::finish() {
    return std::move(implications);
}

void Context::analyze(Function & F) {
    auto function_info = load_my_function_info(F);
    auto implications = transform_basic_blocks(function_info);
    std::move(implications.begin(), implications.end(), std::back_inserter(this->implications));
}

namespace {
MyFunctionInfo load_basic_info(Function & F) {
    auto function_name = F.getName().str();
    bool is_main_function = isMainFunction(function_name);
    MyFunctionInfo function_info(F, function_name, is_main_function);

    return function_info;
}

// FIXME: Do not change names of the basic block
MyFunctionInfo::BasicBlocks load_basic_blocks(Function & F) {
    MyFunctionInfo::BasicBlocks basic_blocks;
    unsigned bb_index = 1;
    std::string const function_name = F.getName().str();

    for (BasicBlock & BB : F) {
        auto name = function_name + std::to_string(bb_index);
        BB.setName(name);

        MyBasicBlock myBB(&BB, name, bb_index);
        basic_blocks.insert(std::make_pair(bb_index, myBB));
        ++bb_index;
    }

    return basic_blocks;
}

// Return variable to for end of the predicate if function is called in basic block
MyVariable get_function_call_var(MyBasicBlock const & BB, int e_index, MyBasicBlock const & successor) {
    if (BB.last_instruction != nullptr && BB.successors.size() > 0) {
        if (BB.successors.size() != 2 || successor.BB_link == BB.last_instruction->getOperand(2)) {
            return MyVariable("false");
        } else {
            return MyVariable("e" + std::to_string(e_index), "Bool");
        }
    } else {
        return MyVariable("false");
    }
}

// Set variable in head predicate as prime when assigned new value in constraint
void set_prime_var_in_head(MyPredicate & head_predicate, std::string const & var_name) {
    for (auto & var : head_predicate.vars) {
        if (var.name == var_name) {
            var.isPrime = true;
            break;
        }
    }
}

// Get type of variable
std::string get_type(Type * type) {
    if (type->isIntegerTy()) {
        auto w = cast<IntegerType>(type)->getBitWidth();
        return w == 1 ? "Bool" : "Int";
    }
    throw std::logic_error("Unknown type of variable.");
}

std::string convert_name_to_string(Value const * const value) {
    std::string block_address;
    raw_string_ostream string_stream(block_address);

    value->printAsOperand(string_stream, false);

    return block_address;
}

// Convert operand to std::string, if negative string,
// return as function (-) with positive value (e.g. -100 => (- 100))
std::string convert_operand_to_string(Value const * value) {
    if (get_type(value->getType()) == "Int") {
        if (ConstantInt const * asConstant = dyn_cast<ConstantInt>(value)) {
            auto num = asConstant->getSExtValue();
            if (num < 0) { return "(- " + std::to_string(num * -1) + ')'; }
            return std::to_string(num);
        }
    }

    return convert_name_to_string(value);
}

// Create constraint for br instruction
std::unique_ptr<UnaryConstraint> transform_br(Instruction * I, BasicBlock * successor) {
    // Instruction must have 3 operands to jump
    if (I->getNumOperands() != 3) { throw std::logic_error("Wrong instruction. Too few function operands."); }

    std::string res = successor == I->getOperand(2) ? "true" : "false";

    return std::make_unique<UnaryConstraint>(convert_name_to_string(I->getOperand(0)), res);
}

std::optional<std::int8_t> get_block_id_by_link(BasicBlock const * block,
                                                MyFunctionInfo::BasicBlocks const & my_blocks) {
    for (auto const & [id, my_block] : my_blocks) {
        if (my_block.BB_link == block) { return id; }
    }
    return std::nullopt;
}

} // namespace

MyFunctionInfo Context::load_my_function_info(Function & F) {
    MyFunctionInfo function_info = load_basic_info(F);
    function_info.basic_blocks = load_basic_blocks(F);
    set_basic_block_info(&function_info);
    return function_info;
}

std::vector<Implication> Context::transform_basic_blocks(MyFunctionInfo & function_info) {

    std::vector<Implication> result;
    result = get_entry_block_implications(function_info, function_info.basic_blocks.at(1));

    for (auto const & entry : function_info.basic_blocks) {
        MyBasicBlock const & BB = entry.second;

        // Skip failed assert basic blocks
        if (BB.isFalseBlock) { continue; }

        // Create implication of current basic block (entry -> exit)
        result.push_back(create_entry_to_exit(BB, function_info));

        // Create implications for transfers to successors
        for (auto & succ : BB.successors) {
            auto current_exit_predicate = create_basic_block_predicate(BB, false, function_info);
            add_global_variables(current_exit_predicate, function_info);

            auto const & successor = function_info.basic_blocks.at(succ);
            auto succ_predicate = create_basic_block_predicate(successor, true, function_info);

            // Create implication
            Implication implication(succ_predicate);

            if (BB.isFunctionCalled) {
                current_exit_predicate.vars.push_back(get_function_call_var(BB, function_info.e_index, successor));
            }

            // Add current BB exit predicate
            implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

            // Translate phi instructions
            for (auto && constraint : transform_phi_instructions(BB, successor)) {
                // Set prime variables
                set_prime_var_in_head(succ_predicate, constraint->result);
                constraint->result = constraint->result + PRIME_SIGN;
                implication.constraints.push_back(std::move(constraint));
            }

            // Branch predicate if 2 successors
            if (BB.last_instruction != nullptr && BB.successors.size() > 0) {
                if (BB.successors.size() == 2) {
                    auto br = transform_br(BB.last_instruction, successor.BB_link);
                    if ((br->result == "true" && br->value == "false") ||
                        (br->result == "false" && br->value == "true")) {
                        continue;
                    }
                    implication.constraints.push_back(std::move(br));
                }
            }

            if (not successor.isFalseBlock) { add_global_variables(succ_predicate, function_info); }
            implication.head = succ_predicate;
            result.push_back(std::move(implication));
        }

        // Add predicate if error in called function
        if (BB.isFunctionCalled) {
            auto fail = get_fail_block_predicate(function_info);
            Implication implication(fail);

            MyPredicate current_exit_predicate = create_basic_block_predicate(BB, false, function_info);
            add_global_variables(current_exit_predicate, function_info);
            current_exit_predicate.vars.push_back(MyVariable("true"));
            implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

            result.push_back(std::move(implication));
        }

        // From return instruction to function predicate implication
        if (BB.isLastBlock) {
            auto fun_predicate = get_function_predicate(function_info, MyVariable("false"), MyVariable("false"));

            auto implication = Implication(fun_predicate);

            MyPredicate current_exit_predicate = create_basic_block_predicate(BB, false, function_info);
            add_global_variables(current_exit_predicate, function_info);
            if (BB.isFunctionCalled) { current_exit_predicate.vars.push_back(MyVariable("false")); }
            implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

            result.push_back(std::move(implication));
        }
    }

    // Add error case implication
    if (function_info.is_main_function) {
        Implication implication = Implication(MyPredicate("false"));
        MyPredicate fail_predicate = get_fail_block_predicate(function_info);
        implication.constraints.push_back(std::make_unique<MyPredicate>(fail_predicate));
        result.push_back(std::move(implication));
    } else {
        auto function_predicate = get_function_predicate(function_info, MyVariable("true"), MyVariable("true"));
        result.emplace_back(function_predicate);
    }

    return result;
}

// Add global variables to basic block predicate
void Context::add_global_variables(MyPredicate & predicate, MyFunctionInfo const & function_info) {
    for (auto const & [name, index] : global_vars) {
        if (not function_info.is_main_function) {
            // No main function needs input value of global variable
            predicate.vars.push_back(MyVariable(name, "Int"));
        }
        predicate.vars.push_back(MyVariable(name + "_" + std::to_string(index), "Int"));
    }
}

// Add constraints for global variables initialized values
void Context::initialize_global_variables(Implication & implication, MyFunctionInfo const & function_info) {
    if (function_info.is_main_function) {
        // Main function takes initial values of variable
        auto globals = function_info.llvm_function.getParent()->globals();

        for (auto & var : globals) {
            if (var.getValueType()->isIntegerTy()) {
                auto name = var.getName().str();
                ++global_vars[name];

                auto result = name + "_" + std::to_string(global_vars[name]);
                auto value = convert_operand_to_string(var.getInitializer());
                implication.constraints.push_back(std::make_unique<StoreConstraint>(result, value));
            }
        }
    } else {
        // No main function takes values of global variable
        // from input global variable in predicate
        for (auto & var : global_vars) {
            ++var.second;

            auto result = var.first + "_" + std::to_string(var.second);
            auto value = var.first;

            implication.constraints.push_back(std::make_unique<StoreConstraint>(result, value));
        }
    }
}

// Create implication from entry to exit point in basic block
Implication Context::create_entry_to_exit(MyBasicBlock const & BB, MyFunctionInfo & function_info) {

    MyPredicate entry_predicate = create_basic_block_predicate(BB, true, function_info);
    add_global_variables(entry_predicate, function_info);

    Implication::Constraints constraints = transform_instructions(BB, function_info);

    auto exit_predicate = create_basic_block_predicate(BB, false, function_info);
    add_global_variables(exit_predicate, function_info);

    // Add last output error variable if some function called in BB
    if (BB.isFunctionCalled) {
        exit_predicate.vars.push_back(MyVariable("e" + std::to_string(function_info.e_index), "Bool"));
    }

    std::unordered_set<std::string> prime_vars;

    // Create prime variables in predicates when new assignment
    for (auto & constraint : constraints) {

        if (FunctionPredicate * fp = dynamic_cast<FunctionPredicate *>(constraint.get())) {

            set_prime_var_in_head(exit_predicate, fp->changed_var);
            prime_vars.insert(fp->changed_var);

            // Set variables when assigned
            for (unsigned int i = 0; i < fp->vars.size(); i++) {
                if (prime_vars.find(fp->vars[i].name) != prime_vars.end()) { fp->vars[i].isPrime = true; }
            }
        } else if (BinaryConstraint * bc = dynamic_cast<BinaryConstraint *>(constraint.get())) {

            // Set operands when assigned before
            if (prime_vars.find(bc->operand1) != prime_vars.end()) { bc->operand1 = bc->operand1 + PRIME_SIGN; }
            if (prime_vars.find(bc->operand2) != prime_vars.end()) { bc->operand2 = bc->operand2 + PRIME_SIGN; }

            // Set assigned variable as prime in current constraint and head predicate
            set_prime_var_in_head(exit_predicate, bc->result);
            prime_vars.insert(bc->result);
            bc->result = bc->result + PRIME_SIGN;
        }

        else if (UnaryConstraint * uc = dynamic_cast<UnaryConstraint *>(constraint.get())) {

            // Set operands when assigned before
            if (prime_vars.find(uc->value) != prime_vars.end()) { uc->value = uc->value + PRIME_SIGN; }

            // Set assigned variable as prime in current constraint and head predicate
            set_prime_var_in_head(exit_predicate, uc->result);
            prime_vars.insert(uc->result);
            uc->result = uc->result + PRIME_SIGN;
        }

        else if (ITEConstraint * ite = dynamic_cast<ITEConstraint *>(constraint.get())) {

            // Set condition operand as prime when assigned before
            if (prime_vars.find(ite->condition) != prime_vars.end()) { ite->condition = ite->condition + PRIME_SIGN; }

            // Set assigned variable as prime in current constraint and head predicate
            set_prime_var_in_head(exit_predicate, ite->result);
            prime_vars.insert(ite->result);
            ite->result = ite->result + PRIME_SIGN;
        }

        else if (LoadConstraint * lc = dynamic_cast<LoadConstraint *>(constraint.get())) {

            // Set assigned variable as prime in current constraint and head predicate
            set_prime_var_in_head(exit_predicate, lc->result);
            prime_vars.insert(lc->result);
            lc->result = lc->result + PRIME_SIGN;
        }

        else if (StoreConstraint * sc = dynamic_cast<StoreConstraint *>(constraint.get())) {

            // Set operand as prime when assigned before
            if (prime_vars.find(sc->value) != prime_vars.end()) { sc->value = sc->value + PRIME_SIGN; }
        }
    }
    constraints.push_back(std::make_unique<MyPredicate>(entry_predicate));
    Implication implication(exit_predicate);
    implication.constraints = std::move(constraints);
    return implication;
}

void Context::set_basic_block_info(MyFunctionInfo * function_info) {
    for (auto & it : function_info->basic_blocks) {
        MyBasicBlock * BB = &it.second;
        BasicBlock * block_link = BB->BB_link;

        // Set Predecessors of blocks and variables from them
        for (auto pred : predecessors(block_link)) {
            // Find predecessor id
            auto maybe_pred_id = get_block_id_by_link(pred, function_info->basic_blocks);
            if (maybe_pred_id.has_value()) {
                auto pred_id = maybe_pred_id.value();
                // Add predecessor
                BB->predecessors.push_back(pred_id);

                // Add new variables from predecessor
                for (auto v : function_info->basic_blocks[pred_id].vars) {
                    add_variable(v, BB);
                }
            }
        }

        // First basic block without predecessors load function arguments
        if (predecessors(block_link).empty()) {
            Function & F = function_info->llvm_function;
            // Load arguments as variables
            for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
                add_variable(arg, BB);
            }
        }

        // Set successors of block
        for (auto succ : successors(block_link)) {
            auto maybe_succ_id = get_block_id_by_link(succ, function_info->basic_blocks);
            assert(maybe_succ_id.has_value());
            BB->successors.push_back(maybe_succ_id.value());
        }

        // Find all used variables in instructions
        for (Instruction & I : block_link->instructionsWithoutDebug()) {

            // See if basic block handles failed assertion
            if (isFailedAssertCall(&I)) {
                BB->isFalseBlock = true;
                break;
            }

            // Remember function called in basic block (no assert)
            if (I.getOpcode() == Instruction::Call) {
                auto fn = dyn_cast<CallInst>(&I)->getCalledFunction();
                if (fn && !fn->isDeclaration()) { BB->isFunctionCalled = true; }
            }

            // Remember last br instruction (should be only one)
            if (I.getOpcode() == Instruction::Br) { BB->last_instruction = &I; }

            // Remember return value of function
            if (I.getOpcode() == Instruction::Ret) {
                if (!function_info->llvm_function.getReturnType()->isVoidTy()) {
                    auto o = I.getOperand(0);
                    if (o->getValueID() != Value::ConstantIntVal) {
                        function_info->return_value = MyVariable(convert_name_to_string(o), get_type(o->getType()));
                    } else {
                        function_info->return_value = MyVariable(convert_operand_to_string(o));
                    }
                }
                BB->isLastBlock = true;
            }

            // Add instructions returning void
            if (!I.getType()->isVoidTy()) { add_variable(&I, BB); }

            // Add all variables from instruction
            for (auto & o : I.operands()) {
                add_variable(o, BB);
            }
        }
    }
}

// Set name for variable and add to basic block info if not presented
void Context::add_variable(Value * var, MyBasicBlock * my_block) {
    // Skip labels and pointers
    if (var->getType()->isLabelTy() or var->getType()->isPointerTy()) { return; }

    if (!var->hasName()) {
        var->setName("x" + std::to_string(var_index));
        ++var_index;
    }

    my_block->vars.insert(var);
}

// Create constraints for function call
Implication::Constraints Context::transform_function_call(Instruction * I, MyFunctionInfo & function_info) {
    Implication::Constraints result;
    CallInst * call_inst = cast<CallInst>(I);

    // Get function from instruction
    Function * fn = call_inst->getCalledFunction();
    std::string function_name;

    // If no function, name can be taken from instruction operand
    if (fn) {
        function_name = fn->getName().str();
    } else {
        function_name = convert_name_to_string(I->getOperand(0));
    }

    // If function not declared, check name for predefined non-deterministic functions
    if (!fn || fn->isDeclaration()) {
        if (function_name.find(UNSIGNED_UINT_FUNCTION, 0) != std::string::npos) {

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "4294967295"));
        } else if (function_name.find(UNSIGNED_SHORT_FUNCTION, 0) != std::string::npos) {
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "(- 32768)"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "32767"));
        } else if (function_name.find(UNSIGNED_USHORT_FUNCTION, 0) != std::string::npos) {
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "65535"));

        } else if (function_name.find(UNSIGNED_UCHAR_FUNCTION, 0) != std::string::npos) {

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "255"));

        } else if (function_name.find(UNSIGNED_CHAR_FUNCTION, 0) != std::string::npos) {

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "(- 128)"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "127"));

        } else {
            // If no predefined function, ignore call and add true constraint
            result.push_back(std::make_unique<MyPredicate>("true"));
        }
        return result;
    }

    auto predicate = std::make_unique<FunctionPredicate>(function_name);
    std::string var_name;
    std::string var_type;

    // Add parameters
    for (auto arg = call_inst->arg_begin(); arg != call_inst->arg_end(); ++arg) {
        if (arg->get()->getValueID() != Value::ConstantIntVal) {
            var_name = convert_name_to_string(arg->get());
            var_type = get_type(arg->get()->getType());

            predicate->vars.push_back(MyVariable(var_name, var_type));
        } else {
            var_name = convert_operand_to_string(arg->get());

            predicate->vars.push_back(MyVariable(var_name));
        }
    }

    // Add return variable
    if (!fn->getReturnType()->isVoidTy()) {
        var_name = convert_name_to_string(I);

        predicate->vars.push_back(MyVariable(var_name, get_type(fn->getReturnType()), true));
        predicate->changed_var = var_name;
    }

    // Add variables for input error variable
    if (function_info.e_index == 0) {
        predicate->vars.push_back(MyVariable("false"));
    } else {
        predicate->vars.push_back(MyVariable("e" + std::to_string(function_info.e_index), "Bool"));
    }

    // Add variables for output error variable
    ++function_info.e_index;
    predicate->vars.push_back(MyVariable("e" + std::to_string(function_info.e_index), "Bool"));

    // Add global variables input and output values
    for (auto & var : global_vars) {
        predicate->vars.push_back(MyVariable(var.first + "_" + std::to_string(var.second), "Int"));
        var.second++;
        predicate->vars.push_back(MyVariable(var.first + "_" + std::to_string(var.second), "Int"));
    }

    result.push_back(std::move(predicate));
    return result;
}

namespace {

// Transform Cmp instruction
std::string cmp_sign(Instruction * I) {
    CmpInst * CmpI = cast<CmpInst>(I);
    switch (CmpI->getPredicate()) {
        case CmpInst::ICMP_EQ:
            return "=";
        case CmpInst::ICMP_NE:
            return "!=";
        case CmpInst::ICMP_UGT:
        case CmpInst::ICMP_SGT:
            return ">";
        case CmpInst::ICMP_UGE:
        case CmpInst::ICMP_SGE:
            return ">=";
        case CmpInst::ICMP_ULT:
        case CmpInst::ICMP_SLT:
            return "<";
        case CmpInst::ICMP_ULE:
        case CmpInst::ICMP_SLE:
            return "<=";
        default:
            throw std::logic_error("Unknown comparison symbol.");
            break;
    }
}

// Create binary constraint for comparison instruction
std::unique_ptr<BinaryConstraint> transform_comparison(Instruction * I) {
    CmpInst * comparison = cast<CmpInst>(I);
    auto sign = cmp_sign(comparison);
    auto * lhs = comparison->getOperand(0);
    auto * rhs = comparison->getOperand(1);

    // Get constant value as signed or unsigned based on type of comparison
    auto asString = [&](Value * val) -> std::string {
        if (auto asConstant = dyn_cast<ConstantInt>(val)) {
            if (comparison->isSigned()) {
                auto value = asConstant->getSExtValue();
                if (value < 0) { return "(- " + std::to_string(value * -1) + ')'; }
                return std::to_string(value);
            } else {
                auto value = asConstant->getZExtValue();
                return std::to_string(value);
            }
        }
        return convert_name_to_string(val);
    };

    return std::make_unique<BinaryConstraint>(convert_name_to_string(comparison), asString(lhs), sign, asString(rhs));
}

// Create binary constraint from binary instructions
std::unique_ptr<BinaryConstraint> transform_binary_inst(Instruction * I) {
    std::string sign;
    switch (I->getOpcode()) {
        case Instruction::ICmp:
            return transform_comparison(I);
        case Instruction::Add:
            sign = "+";
            break;
        case Instruction::Sub:
            sign = "-";
            break;
        case Instruction::Mul:
            sign = "*";
            break;
        case Instruction::UDiv:
        case Instruction::SDiv:
            sign = "div";
            break;
        case Instruction::URem:
        case Instruction::SRem:
            sign = "mod";
            break;
        case Instruction::Xor:
            sign = "xor";
            break;
        case Instruction::And:
            sign = "and";
            break;
        case Instruction::Or:
            sign = "or";
            break;
        default:
            throw std::logic_error("Wrong binary instruction.");
    }

    return std::make_unique<BinaryConstraint>(convert_name_to_string(I), convert_operand_to_string(I->getOperand(0)),
                                              sign, convert_operand_to_string(I->getOperand(1)));
}

// Create constraint for zext instruction
std::unique_ptr<MyConstraint> transform_zext(Instruction * I) {
    MyVariable input(convert_name_to_string(I->getOperand(0)), get_type(I->getOperand(0)->getType()));
    MyVariable output(convert_name_to_string(I), get_type(I->getType()));

    if (input.type == "Bool" && output.type == "Int") {
        return std::make_unique<ITEConstraint>(output.name, "1", input.name, "0");
    } else {
        return std::make_unique<UnaryConstraint>(output.name, input.name);
    }
}

// Create constraint for trunc instruction
std::unique_ptr<MyConstraint> transform_trunc(Instruction * I) {
    MyVariable input(convert_name_to_string(I->getOperand(0)), get_type(I->getOperand(0)->getType()));
    MyVariable output(convert_name_to_string(I), get_type(I->getType()));

    if (input.type == "Int" && output.type == "Bool") {
        return std::make_unique<BinaryConstraint>(output.name, input.name, "!=", "0");
    } else {
        return std::make_unique<UnaryConstraint>(output.name, input.name);
    }
}

// Create equality constraint for sext instruction
std::unique_ptr<UnaryConstraint> transform_sext(Instruction * I) {
    return std::make_unique<UnaryConstraint>(convert_name_to_string(I), convert_name_to_string(I->getOperand(0)));
}

// Create constraint for logic instruction with boolean variables
std::unique_ptr<BinaryConstraint> transform_logic_operand(Instruction * I) {
    auto op1_type = get_type(I->getOperand(0)->getType());
    auto op2_type = get_type(I->getOperand(1)->getType());

    if (op1_type == "Bool" && op2_type == "Bool") {
        return transform_binary_inst(I);
    } else {
        throw std::logic_error("Logic operation not on Bool");
    }
}

} // namespace

// Create constraint for load instruction with global variable
std::unique_ptr<LoadConstraint> Context::transform_load_operand(Instruction * I) {

    std::string global_var_name = I->getOperand(0)->getName().str();
    int index = global_vars[global_var_name];

    auto result = convert_name_to_string(I);
    auto value = global_var_name + "_" + std::to_string(index);

    return std::make_unique<LoadConstraint>(std::move(result), std::move(value));
}

// Create constraint for store instruction with global variable
std::unique_ptr<StoreConstraint> Context::transform_store_operand(Instruction * I) {

    std::string global_var_name = I->getOperand(1)->getName().str();
    global_vars[global_var_name]++;
    int index = global_vars[global_var_name];

    return std::make_unique<StoreConstraint>(global_var_name + "_" + std::to_string(index),
                                             convert_operand_to_string(I->getOperand(0)));
}

// Set variables for phi instruction, depending on label before
std::vector<std::unique_ptr<UnaryConstraint>> Context::transform_phi_instructions(MyBasicBlock const & predecessor,
                                                                                  MyBasicBlock const & successor) {

    std::vector<std::unique_ptr<UnaryConstraint>> result;

    for (Instruction & I : successor.BB_link->instructionsWithoutDebug()) {
        if (I.getOpcode() == Instruction::PHI) {
            Value * translation = I.DoPHITranslation(successor.BB_link, predecessor.BB_link);

            result.push_back(
                std::make_unique<UnaryConstraint>(convert_name_to_string(&I), convert_operand_to_string(translation)));
        }
    }
    return result;
}

// Transform instructions to constraints from instructions in basic block
Implication::Constraints Context::transform_instructions(MyBasicBlock const & BB, MyFunctionInfo & function_info) {

    Implication::Constraints result;
    function_info.e_index = 0;

    for (Instruction & I : BB.BB_link->instructionsWithoutDebug()) {
        switch (I.getOpcode()) {
            // Instructions with no constraint
            case Instruction::Br:
            case Instruction::CallBr:
            case Instruction::IndirectBr:
            case Instruction::PHI:
            case Instruction::Ret:
            case Instruction::Unreachable:
                break;
            // Instructions with 1 constraint
            case Instruction::ICmp:
            case Instruction::Add:
            case Instruction::Sub:
            case Instruction::Mul:
            case Instruction::UDiv:
            case Instruction::SDiv:
            case Instruction::URem:
            case Instruction::SRem:
                result.push_back(transform_binary_inst(&I));
                break;
            case Instruction::ZExt:
                result.push_back(transform_zext(&I));
                break;
            case Instruction::Trunc:
                result.push_back(transform_trunc(&I));
                break;
            case Instruction::SExt:
                result.push_back(transform_sext(&I));
                break;
            case Instruction::Load:
                result.push_back(transform_load_operand(&I));
                break;
            case Instruction::Store:
                result.push_back(transform_store_operand(&I));
                break;
            // Transform logic instruction on booleans
            case Instruction::Xor:
            case Instruction::And:
            case Instruction::Or:
                result.push_back(transform_logic_operand(&I));
                break;
            case Instruction::Call: {
                auto predicates = transform_function_call(&I, function_info);
                std::move(predicates.begin(), predicates.end(), std::back_inserter(result));
                break;
            }
            default:
                throw std::logic_error("Not implemented instruction");
        }
    }
    return result;
}

// Create first implication for function input and transfer to BB1
std::vector<Implication> Context::get_entry_block_implications(MyFunctionInfo const & function_info,
                                                               MyBasicBlock const & BB1) {
    std::vector<Implication> result;

    // Create predicate for entry basic block with function arguments
    MyBasicBlock BB_entry(nullptr, function_info.name + "0", 0);
    Function & F = function_info.llvm_function;
    for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
        add_variable(arg, &BB_entry);
    }
    auto predicate = create_basic_block_predicate(BB_entry, true, function_info);
    add_global_variables(predicate, function_info);

    // Create first implication (true -> BBentry(x1,..))
    result.emplace_back(predicate);

    // Create implication for transfer to first basic block
    // with initialized global variables
    auto BB1_predicate = create_basic_block_predicate(BB1, true, function_info);
    Implication imp1(BB1_predicate);
    imp1.constraints.push_back(std::make_unique<MyPredicate>(predicate));

    initialize_global_variables(imp1, function_info);

    if (!BB1.isFalseBlock) { add_global_variables(BB1_predicate, function_info); }
    imp1.head = BB1_predicate;

    result.push_back(std::move(imp1));

    return result;
}

// Create predicate for basic block: Format {name}({variables}), ex. BB1(%x1,%x2)
MyPredicate Context::create_basic_block_predicate(MyBasicBlock const & BB, bool isEntry,
                                                  MyFunctionInfo const & function_info) {

    // Failed assert block
    if (BB.isFalseBlock) { return get_fail_block_predicate(function_info); }

    // Convert variables
    std::vector<MyVariable> vars;
    std::string var_name;
    std::string var_type;
    for (auto & v : BB.vars) {
        if (v->getValueID() != Value::ConstantIntVal) {
            var_name = convert_name_to_string(v);
            var_type = get_type(v->getType());

            vars.push_back(MyVariable(var_name, var_type));
        }
    }

    std::string suffix = isEntry ? "_entry" : "_exit";
    return MyPredicate(BB.name + suffix, vars);
}

// Create current function predicate not for call instruction
MyPredicate Context::get_function_predicate(MyFunctionInfo const & function_info, MyVariable e_in, MyVariable e_out) {

    // Create predicate
    std::string var_name;
    std::string var_type;
    Function & F = function_info.llvm_function;
    MyPredicate predicate{F.getName().str()};

    // Add parameters
    for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
        if (arg->getValueID() != Value::ConstantIntVal) {
            var_name = convert_name_to_string(arg);
            var_type = get_type(arg->getType());

            predicate.vars.push_back(MyVariable(var_name, var_type));
        }
    }

    // Add return value
    if (!F.getReturnType()->isVoidTy()) { predicate.vars.push_back(function_info.return_value); }

    if (!function_info.is_main_function) {
        // Add input and output errors
        predicate.vars.push_back(e_in);
        predicate.vars.push_back(e_out);
    }

    add_global_variables(predicate, function_info);

    return predicate;
}

// Return fail block predicate
MyPredicate Context::get_fail_block_predicate(MyFunctionInfo const & function_info) {
    if (function_info.is_main_function) {
        // Return new predicate if main function
        return MyPredicate(function_info.name + "_error");
    } else {
        // Return function predicate with output error
        return get_function_predicate(function_info, MyVariable("false"), MyVariable("true"));
    }
}

Implications toChc(Module & module) {
    return ChcTransform{}.run(module);
}

Implications ChcTransform::run(Module & module) {
    auto context = Context::create(module);
    for (Function & f : module) {
        if (not f.isDeclaration()) { context.analyze(f); }
    }
    return context.finish();
}
