import LakeJs.Js

open Lean.Compiler.JS

def lean_array_fset := [JS_FUNC|inputs(arr, idx, val)|returns=arr|
  arr[idx] = val;
]

def lean_array_set := lean_array_fset
