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


echo "(set-logic HORN)" > $file_name.smt2

clang -Xclang -disable-O0-optnone -S -emit-llvm $1 -o $file_name.ll
opt -disable-output $file_name.ll -passes=mem2reg,chc-transform >> $file_name.smt2

echo "(check-sat)" >> $file_name.smt2

z3 -smt2 $file_name.smt2

rm $file_name.ll $file_name.smt2