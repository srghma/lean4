import LakeJs.Js

open Lean.Compiler.JS

def lean_nat_land := [JS|#0 & #1]
def lean_nat_lor := [JS|#0 | #1]
def lean_nat_lxor := [JS|#0 ^ #1]
def lean_nat_shiftl := [JS|#0 << #1]
def lean_nat_shiftr := [JS|#0 >> #1]
