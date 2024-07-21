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

echo "(set-logic HORN)" > smt/$1.smt2

clang -Xclang -disable-O0-optnone -S -emit-llvm $1 -o LLVMIRs/$1.ll
opt -disable-output LLVMIRs/$1.ll -passes=mem2reg,chc-transform >> smt/$1.smt2

echo "(check-sat)" >> smt/$1.smt2
z3 -smt2 smt/$1.smt2