import LakeJs.Js

open Lean.Compiler.JS

def lean_slice_hash := [JS_FUNC|inputs(str, start, len)|returns=hash|
  const s = str.substring(start, start + len);
  let hash = 0;
  for (let i = 0; i < s.length; i++) {
    hash = (hash << 5) - hash + s.charCodeAt(i);
    hash |= 0;
  }
]


def lean_slice_dec_lt := [JS|((#0).substring(#1, #1 + #2) < (#3).substring(#4, #4 + #5))]
