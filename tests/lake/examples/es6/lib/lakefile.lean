import Lake
open System Lake DSL

package ffi where
  backend := .es6

@[default_target]
lean_exe test where
  root := `Main
  backend := .es6

lean_lib FFI

lean_exe standalone where
  root := `Standalone
  backend := .es6
