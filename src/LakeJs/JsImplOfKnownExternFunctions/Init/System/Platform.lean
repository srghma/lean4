import LakeJs.Js

open Lean.Compiler.JS

def lean_system_platform_windows := [JS|false]
def lean_system_platform_osx := [JS|false]
def lean_system_platform_emscripten := [JS|false]
def lean_system_platform_javascript := [JS|true]
def lean_system_platform_target := [JS|"javascript-unknown-unknown"]
