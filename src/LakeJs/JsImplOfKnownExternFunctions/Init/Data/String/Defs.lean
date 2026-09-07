import LakeJs.Js

open Lean.Compiler.JS

def lean_string_to_utf8 := [JS|encoder.encode(#0)]
def lean_string_append := [JS|#0 + #1]
