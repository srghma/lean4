> regenerate_gen.ts should only call stage1 Lean, rustfmt, prune stale files, and regenerate module trees.

yes, cmake should cache it, e.g. we have A.lean -> B.lean -> C.lean
if B.lean has changed , then A.lean should not be changed, but C.lean should
if EmitRust have changed -> then stage1 will be changed too -> then all A,B,C will be regenerated automatically too by cmake
