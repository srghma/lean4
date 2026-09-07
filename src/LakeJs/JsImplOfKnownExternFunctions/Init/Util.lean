import LakeJs.Js

open Lean.Compiler.JS

def lean_dbg_trace := [JS|((s, f) => {
  console.log(s);
  return f( );
})(#0, #1)]

def lean_dbg_trace_if_shared := [JS|#1]
def lean_dbg_stack_trace := [JS|((f) => f( ))(#0)]
def lean_dbg_stack_trace_if := [JS|((cond, f) => f( ))(#0, #1)]
def lean_dbg_sleep := [JS|throw new Error("not implemented")]
def lean_ptr_addr := [JS|throw new Error("not implemented")]
def lean_is_exclusive_obj := [JS|throw new Error("not implemented")]

namespace LakeJs
def mkPanicMessageWithDecl := [JS|((modName, declName, line, col, msg) => msg)(#0, #1, #2, #3, #4)]
