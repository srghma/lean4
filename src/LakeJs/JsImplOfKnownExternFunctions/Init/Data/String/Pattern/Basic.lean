import LakeJs.Js

open Lean.Compiler.JS

def lean_string_memcmp := [JS_FUNC|inputs(s1, s2, start1, start2, len)|
  return (s1.slice(start1, start1 + len) == s2.slice(start2, start2 + len));
]
