import LakeJs.Js

open Lean.Compiler.JS

def lean_string_validate_utf8 := [JS|throw new Error("lean_string_validate_utf8 not implemented")]
def lean_string_data := [JS|new TextEncoder( ).encode(#0)]
def lean_string_length := [JS|(#0).length]
def lean_string_utf8_byte_size := [JS|new TextEncoder( ).encode(#0).length]
def lean_string_dec_lt := [JS|#0 < #1]
def lean_string_is_valid_pos := [JS|throw new Error("lean_string_is_valid_pos not implemented")]
def lean_string_utf8_extract := [JS|throw new Error("lean_string_utf8_extract not implemented")]
def lean_string_utf8_get_fast := [JS|throw new Error("lean_string_utf8_get_fast not implemented")]
def lean_string_utf8_next_fast := [JS|throw new Error("lean_string_utf8_next_fast not implemented")]
def lean_string_utf8_get := [JS|throw new Error("lean_string_utf8_get not implemented")]
def lean_string_utf8_get_opt := [JS|throw new Error("lean_string_utf8_get_opt not implemented")]
def lean_string_utf8_get_bang := [JS|throw new Error("lean_string_utf8_get_bang not implemented")]
def lean_string_utf8_next := [JS|throw new Error("lean_string_utf8_next not implemented")]
def lean_string_utf8_prev := [JS|throw new Error("lean_string_utf8_prev not implemented")]
def lean_string_utf8_at_end := [JS|throw new Error("lean_string_utf8_at_end not implemented")]
