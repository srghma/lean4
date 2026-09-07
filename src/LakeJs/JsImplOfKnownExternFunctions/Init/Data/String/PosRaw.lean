import LakeJs.Js

open Lean.Compiler.JS

def lean_string_get_byte_fast := [JS|new TextEncoder( ).encode(#0)[#1]]
