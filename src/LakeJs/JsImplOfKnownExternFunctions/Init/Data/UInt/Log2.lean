import LakeJs.Js

open Lean.Compiler.JS

def lean_uint8_log2 := [JS|Math.clz32(1) - Math.clz32(#0)]
def lean_uint16_log2 := [JS|Math.clz32(1) - Math.clz32(#0)]
def lean_uint32_log2 := [JS|Math.clz32(1) - Math.clz32(#0)]
def lean_uint64_log2 := [JS|Math.clz32(1) - Math.clz32(#0)]
def lean_usize_log2 := [JS|Math.clz32(1) - Math.clz32(#0)]
