import Lake
open System Lake DSL

package app where
  backend := .es6

require ffi from ".."/"lib"

@[default_target]
lean_exe app where
  root := `Main
  backend := .es6

lean_lib Test
