# Hornix

## **Getting started**

#### Download LLVM

1. Clone LLVM repository:

    `git clone https://github.com/llvm/llvm-project.git`


#### Add new pass into LLVM

1. Add file `CHCTransform.h` into `llvm-project/llvm/include/llvm/Transforms/Utils/` repository
2. Add file `CHCTransform.cpp` into `llvm-project/llvm/lib/Transforms/Utils/` repository
3. Into file`llvm-project/llvm/lib/Passes/PassBuilder.cpp` add new line `#include "llvm/Transforms/Utils/CHCTransform.h"`
4. Into file `llvm-project/llvm/lib/Passes/PassRegistry.def` add new line `FUNCTION_PASS("chc-transform", CHCTransformPass())`
5. Into file `llvm-project/llvm/lib/Transforms/Utils/CMakeLists.txt` add `CHCTransform.cpp`


 #### Configure LLVM using CMake

```
1. cmake -S llvm-project\llvm -B build -DLLVM_ENABLE_PROJECTS=clang -DLLVM_TARGETS_TO_BUILD=X86 -Thost=x64 -DLLVM_ENABLE_EH=true -DLLVM_ENABLE_RTTI=true -G "Ninja"

2. cmake --build build --target clang

3. cmake --build build --target opt
```

### Official documentation for LLVM start

https://llvm.org/docs/GettingStarted.html#getting-the-source-code-and-building-llvm


## **Using pass**

1. Compile using clang with minimal number of passes: ` clang++ -Xclang -disable-O0-optnone -S -emit-llvm {source code} -o {output file}`
2. Use pass mem2reg, to move memory allocations to registers.: `opt -S {output file from previous command} -passes=mem2reg -o {output file}`
3. Use chc-transform pass: `opt -disable-output {output file from previous command} -passes=chc-transform`


For example, source code file *example.cpp* :

```
clang++ -Xclang -disable-O0-optnone -S -emit-llvm example.cpp -o example.ll

opt -passes=mem2reg -S example.ll -o example.ll

opt -disable-output example.ll -passes=chc-transform >> example.smt
```

## **Bash scripts**

### **Running verification using bash script**

- *chc-transform.sh* 
    * to run program, creates and delete directory for temporary files, errors are silenced (returns only string error)
    * arguments: 
        1. cpp or c source file 
        2. name of dir where should save temporary files. If already exists it is used. 
    * results: *sat/unsat/error* as text
    * example `./chc-transform.sh example.cpp tmp`

- *tool.sh*
    * to run program, tmp files saved to dirs smt and LLVMIRs, errors not silenced
    * arguments: 
        1. cpp or c source file  
    * results: *sat/unsat* as text and ll + smt file
    * example `./tool.sh example.cpp`

- *test-bench.sh*
    * to run benchmark, uses chc-transform.sh
    * takes directory with files or single yaml file expecting c/cpp/i file in same directory
    * used to run benchmarks and test unreach-call.prp property in yaml file  
    * arguments: 
        1. regex with yaml files (dir/*.yml) or yaml file
        2. timeout for each test in seconds  
    * results: *{file_name}; ERROR - no unreach/no .c or .i file/TOO LONG/OK-sat/BAD-sat/OK-unsat/BAD-unsat/ERROR/unknown*
    * example `./test-bench.sh sv-benchmarks/c/loops/*.yml 100`


- *test-set.sh*
    * to run set of tests, uses test-bench
    * takes file with specified yaml files (for example sv-benchmarks/c/ReachSafety-Loops.set)
    * arguments: 
        1. file with names of yaml files on lines
        2. timeout for each test
    * results: same as test-bench.sh
    * example `./test-set.sh sv-benchmarks/c/ReachSafety-Loops.set 100`

### **Requirements**

To properly run the script you to build or download software

1. clang version 18.1.8
2. opt from LLVM with chc-transform pass built
3. z3 solver
