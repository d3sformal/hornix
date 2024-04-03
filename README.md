# CHC-LLVM-pass



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

1. ```
   cmake -S llvm\llvm -B build -DLLVM_ENABLE_PROJECTS=clang -DLLVM_TARGETS_TO_BUILD=X86 -Thost=x64
   ```



### Official documentation for LLVM start 

https://llvm.org/docs/GettingStarted.html#getting-the-source-code-and-building-llvm



## **Using pass**

1. Compile using clang with minimal number of passes: ` clang++ -Xclang -disable-O0-optnone -S -emit-llvm {source code} -o {output file}`
2. Use passes. First, pass to move memory allocation to registers (mem2reg) and then my pass(chc-transform): `opt -S {input file} -passes=mem2reg,chc-transform -o {output file}` 



For example, source code file *example.cpp* :

```
clang++ -Xclang -disable-O0-optnone -S -emit-llvm example.cpp -o example.ll
opt -disable-output -S example.ll -passes=mem2reg,chc-transform > example.ll
```





