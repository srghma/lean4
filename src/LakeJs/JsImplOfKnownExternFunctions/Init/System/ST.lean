import LakeJs.Js

open Lean.Compiler.JS

def lean_void_mk := [JS|#0]
def lean_st_mk_ref := [JS|({ value: #0 })]
def lean_st_ref_get := [JS|(#0).value]
def lean_st_ref_set := [JS|((ref, a) => {
  ref.value = a;
  return null;
})(#0, #1)]
def lean_st_ref_swap := [JS|((ref, a) => {
  const old = ref.value;
  ref.value = a;
  return old;
})(#0, #1)]
def lean_st_ref_take := [JS|((ref) => {
  const old = ref.value;
  ref.value = undefined;
  return old;
})(#0)]
def lean_st_ref_ptr_eq := [JS|#0 === #1]
