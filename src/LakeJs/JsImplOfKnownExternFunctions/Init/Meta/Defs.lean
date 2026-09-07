import LakeJs.Js

open Lean.Compiler.JS

def lean_version_get_major := [JS|4]
def lean_version_get_minor := [JS|32]
def lean_version_get_patch := [JS|0]
def lean_get_githash := [JS|"" ]
def lean_version_get_is_release := [JS|false]
def lean_version_get_special_desc := [JS|"" ]
def lean_internal_is_stage0 := [JS|false]
def lean_internal_has_llvm_backend := [JS|false]
