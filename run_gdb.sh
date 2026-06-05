gdb -q --batch \
  -ex "set breakpoint pending on" \
  -ex "b lean_dec_ref if \$rdi == 1" \
  -ex "run test_match.lean -c test_match.c" \
  -ex "bt" \
  build/release/stage1/bin/lean
