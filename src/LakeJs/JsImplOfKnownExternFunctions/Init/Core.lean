import LakeJs.Js

open Lean.Compiler.JS

def lean_mk_thunk := [JS_FUNC|inputs(fn)|
  let cached = null;
  let evaluated = false;
  return ({
    get: ( ) => {
      if (!evaluated) {
        cached = fn( );
        evaluated = true;
      }
      return cached;
    }
  });
]
def lean_thunk_pure := [JS|({ get: ( ) => #0 })]
def lean_thunk_get_own := [JS|(#0).get( )]

def lean_task_pure := [JS|Promise.resolve(#0)]
def lean_task_get_own := [JS|#0]
def lean_task_spawn := [JS|Promise.resolve( ).«then»(#0)]
def lean_task_map := [JS|(#1).«then»(#0)]
def lean_task_bind := [JS|(#0).«then»(#1)]

def lean_strict_or := [JS|#0 || #1]
def lean_strict_and := [JS|#0 && #1]
