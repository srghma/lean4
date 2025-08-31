#!/usr/bin/env bash
source ../common.sh

if true; then
    echo "Testing Node backend"
    # First check the C version actually works...
    echo "running Node program..."
    rm "./$f.js" || true
    compile_lean_node_backend
    exec_check__using_node "./$f.js"
    diff_produced
    exit 0
fi

# First check the C version actually works...
echo "running C program..."
rm "./$f.out" || true
compile_lean_c_backend
exec_check "./$f.out"
diff_produced

# Then check the LLVM version
if lean_has_llvm_support; then
    echo "running LLVM program..."
    rm "./$f.out" || true
    compile_lean_llvm_backend
    exec_check "./$f.out"
    diff_produced
fi
