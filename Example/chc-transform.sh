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

clang -Xclang -disable-O0-optnone -S -emit-llvm $1 -o $file_name.ll
opt -passes=mem2reg -S $file_name.ll -o $file_name.ll
opt -disable-output $file_name.ll -passes=chc-transform > $file_name.smt2
z3 -model -smt2 $file_name.smt2

rm $file_name.ll $file_name.smt2