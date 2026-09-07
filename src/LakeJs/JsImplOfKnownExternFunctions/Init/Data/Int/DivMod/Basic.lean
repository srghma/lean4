import LakeJs.Js

open Lean.Compiler.JS

def lean_int_emod := [JS|((a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return (b == 0) ? a : (a % b);
})(#0, #1)]

def lean_int_ediv := [JS|((a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return (b == 0) ? 0 : (a / b);
})(#0, #1)]

def lean_int_div_exact := [JS|((a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return (b == 0) ? false : (a % b == 0);
})(#0, #1)]

def lean_int_div := [JS|((a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return (b == 0) ? 0 : (a / b);
})(#0, #1)]

def lean_int_mod := [JS|((a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return (b == 0) ? a : (a % b);
})(#0, #1)]
