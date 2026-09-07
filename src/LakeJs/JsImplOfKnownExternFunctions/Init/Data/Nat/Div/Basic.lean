import LakeJs.Js

open Lean.Compiler.JS

def lean_nat_div_exact := [JS|(#1 === 0) ? false : (#0 % #1 === 0)]
