import LakeJs.Js

open Lean.Compiler.JS

def lean_array_size := [JS|(#0).length]
def lean_array_uget := [JS|#0[#1]]
def lean_array_uget_borrowed := lean_array_uget
def lean_array_uset := [JS|((arr, idx, val) => {
  arr[idx] = val;
  return arr;
})(#0, #1, #2)]
def lean_array_pop := [JS|((arr) => {
  arr.pop( );
  return arr;
})(#0)]
def lean_mk_array := [JS|Array.from(#0)]
def lean_array_fswap := [JS|((arr, idx1, idx2) => {
  const tmp = arr[idx1];
  arr[idx1] = arr[idx2];
  arr[idx2] = tmp;
  return arr;
})(#0, #1, #2)]
def lean_array_swap := lean_array_fswap
