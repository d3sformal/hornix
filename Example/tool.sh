#!/bin/bash

if [ "$#" -ne 1 ]; then
    echo "Should be specified cpp file name"
fi

filename="$1"

# Extracting the file extension
extension="${filename##*.}"

# Checking if the extension is "cpp" or "c"
if [ "$extension" = "cpp" ]; then
  file_name=$(basename $1 .cpp)

elif [ "$extension" = "c" ]; then
  file_name=$(basename $1 .c)
else
  echo "$filename is neither a C++ nor a C file."
  exit
fi

echo "(set-logic HORN)" > smt/$file_name.smt2

clang -Xclang -disable-O0-optnone -fdiscard-value-names -S -emit-llvm $1 -o LLVMIRs/$file_name.ll
opt -passes=mem2reg,instsimplify -S LLVMIRs/$file_name.ll -o LLVMIRs/$file_name.ll
opt -disable-output LLVMIRs/$file_name.ll -passes=chc-transform >> smt/$file_name.smt2

echo "(check-sat)" >> smt/$file_name.smt2

z3 -smt2 smt/$file_name.smt2
