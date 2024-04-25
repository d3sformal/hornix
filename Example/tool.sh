#!/bin/bash

echo "(set-logic HORN)" > smt/$1.smt2
echo "(set-info :status sat)" >> smt/$1.smt2

clang++ -Xclang -disable-O0-optnone -S -emit-llvm $1.cpp -o LLVMIRs/$1.ll
opt -passes=mem2reg -S LLVMIRs/$1.ll -o LLVMIRs/$1.ll
opt -disable-output LLVMIRs/$1.ll -passes=chc-transform >> smt/$1.smt2

echo "(check-sat)" >> smt/$1.smt2
z3 -smt2 smt/$1.smt2