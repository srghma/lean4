import LakeJs.Js

open Lean.Compiler.JS

def lean_nat_to_int := [JS|#0]
def lean_int_neg_succ_of_nat := [JS|-#0 - 1]
def lean_int_neg := [JS|-#0]
def lean_int_add := [JS|#0 + #1]
def lean_int_mul := [JS|#0 * #1]
def lean_int_sub := [JS|#0 - #1]
def lean_int_dec_eq := [JS|#0 == #1]
def lean_int_dec_nonneg := [JS|#0 >= 0]
def lean_int_dec_le := [JS|#0 <= #1]
def lean_int_dec_lt := [JS|#0 < #1]
def lean_nat_abs := [JS|(#0 < 0) ? -#0 : #0]
