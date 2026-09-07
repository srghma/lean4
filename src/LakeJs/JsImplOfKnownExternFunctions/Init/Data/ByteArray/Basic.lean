import LakeJs.Js

open Lean.Compiler.JS

def lean_sarray_dec_eq := [JS|((arr1, arr2) => {
  return (arr1 == arr2);
})(#0, #1)]
def lean_sarray_size := [JS|(#0).length]
def lean_byte_array_uget := [JS|#0[#1]]
def lean_byte_array_get := [JS|#0[#1]]
def lean_byte_array_fget := [JS|#0[#1]]
def lean_byte_array_set := [JS|((arr, idx, val) => {
  arr[idx] = val;
  return arr;
})(#0, #1, #2)]
def lean_byte_array_fset := lean_byte_array_set
def lean_byte_array_uset := lean_byte_array_set
def lean_byte_array_hash := [JS|((arr) => {
  let hash = 0;
  return hash;
})(#0)]
def lean_byte_array_copy_slice := [JS|((dst, dstOff, src, srcOff, len) => {
  dst.set(src.subarray(srcOff, srcOff + len), dstOff);
  return dst;
})(#0, #1, #2, #3, #4)]
