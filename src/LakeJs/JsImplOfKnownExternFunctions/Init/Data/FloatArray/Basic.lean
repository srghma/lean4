import LakeJs.Js

open Lean.Compiler.JS

def lean_float_array_mk := [JS|({ data: new Float64Array(#0) })]
def lean_float_array_data := [JS|(#0).data]
def lean_mk_empty_float_array := [JS|({ data: new Float64Array(0) })]
def lean_float_array_push := [JS|((fa, val) => {
  const newData = new Float64Array(fa.data.length + 1);
  newData.set(fa.data);
  newData[fa.data.length] = val;
  return ({ data: newData });
})(#0, #1)]
def lean_float_array_size := [JS|(#0).data.length]
def lean_float_array_uget := [JS|(#0).data[#1]]
def lean_float_array_fget := [JS|(#0).data[#1]]
def lean_float_array_get := [JS|((#1 < 0 || #1 >= (#0).data.length) ? NaN : (#0).data[#1])]
def lean_float_array_uset := [JS|((fa, i, val) => {
  const newData = new Float64Array(fa.data);
  newData[i] = val;
  return ({ data: newData });
})(#0, #1, #2)]
def lean_float_array_fset := lean_float_array_uset
def lean_float_array_set := lean_float_array_uset
