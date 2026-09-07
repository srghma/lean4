import LakeJs.Js

open Lean.Compiler.JS

def lean_bitvec_and := [JS|BigInt.asUintN(#2, #0 & #1)]
def lean_bitvec_or := [JS|BigInt.asUintN(#2, #0 | #1)]
def lean_bitvec_xor := [JS|BigInt.asUintN(#2, #0 ^ #1)]
def lean_bitvec_not := [JS|BigInt.asUintN(#1, ~#0)]
def lean_bitvec_shift_left := [JS|BigInt.asUintN(#2, #0 << #1)]
def lean_bitvec_ushift_right := [JS|BigInt.asUintN(#2, #0 >> #1)]
def lean_bitvec_sshift_right := [JS|BigInt.asUintN(#2, BigInt.asIntN(#2, #0) >> #1)]
def lean_bitvec_rotate_left := [JS|((x, s, n) => {
  const width = BigInt(n);
  const shift = BigInt(s) % width;
  return BigInt.asUintN(n, (x << shift) | (x >> (width - shift)));
})(#0, #1, #2)]
def lean_bitvec_rotate_right := [JS|((x, s, n) => {
  const width = BigInt(n);
  const shift = BigInt(s) % width;
  return BigInt.asUintN(n, (x >> shift) | (x << (width - shift)));
})(#0, #1, #2)]
def lean_bitvec_append := [JS|BigInt.asUintN(#2 + #3, (#0 << BigInt(#3)) | #1)]
def lean_bitvec_concat := [JS|BigInt.asUintN(#2 + 1, (#0 << 1) | (#1 ? 1 : 0))]
def lean_bitvec_cons := [JS|BigInt.asUintN(#2 + 1, (#0 ? (1 << BigInt(#2)) : 0) | #1)]
