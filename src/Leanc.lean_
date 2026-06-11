/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Compiler.FFI

open Lean.Compiler.FFI

def main (args : List String) : IO UInt32 := do
  let mut args := args.toArray
  let root ← match (← IO.getEnv "LEAN_SYSROOT") with
    | some root => pure <| System.FilePath.mk root
    | none      => pure <| (← IO.appDir).parent.get!
  let hasRs := args.any (·.endsWith ".rs")
  if hasRs then
    let mut outfile? := none
    let mut sourcefile? := none
    let mut optLevel := "0"
    let mut debug := #[]
    let mut iter := args.toList
    while !iter.isEmpty do
      match iter with
      | "-o" :: out :: rest =>
        outfile? := some out
        iter := rest
      | arg :: rest =>
        if arg.endsWith ".rs" then
          sourcefile? := some arg
        else if arg == "-g" then
          debug := #["-g"]
        else if arg == "-O3" || arg == "-O2" || arg == "-O" then
          optLevel := "3"
        iter := rest
      | [] => break

    if let some sourcefile := sourcefile? then
      let outfile := match outfile? with
        | some out => out
        | none => (System.FilePath.mk sourcefile).withExtension "o" |>.toString
      let sysroot := root.toString
      let libDir := s!"{sysroot}/lib/lean"
      -- Prefer the cargo-built lean_runtime (same hash that lean_init etc. were compiled against).
      -- Fall back to the CMake ABI stub (liblean_runtime.rlib) when running without setup.ts.
      let cargoRlib := s!"{libDir}/liblean_runtime_from_cargo.rlib"
      let rlib ← if ← (System.FilePath.mk cargoRlib).pathExists then
                   pure cargoRlib
                 else
                   pure s!"{libDir}/liblean_runtime.rlib"
      -- Derive a valid crate name from the filename stem: replace non-identifier chars with `_`,
      -- drop leading digits. This avoids rustc errors like "invalid character '.' in crate name".
      let rawStem := (System.FilePath.mk sourcefile).fileStem.getD "module"
      let sanitized := rawStem.map fun c => if c.isAlphanum || c == '_' then c else '_'
      let crateName := if sanitized.isEmpty then "module"
                       else if sanitized.front.isDigit then "_" ++ sanitized
                       else sanitized
      -- Add --extern flags for lean_* package rlibs when present (generated .rs files use them).
      let mut pkgExterns : Array String := #[]
      for pkg in #["lean_init", "lean_std", "lean_lean", "lean_lake"] do
        let pkgRlib := s!"{libDir}/lib{pkg}.rlib"
        if ← (System.FilePath.mk pkgRlib).pathExists then
          pkgExterns := pkgExterns ++ #["--extern", s!"{pkg}={pkgRlib}"]
      -- lean_runtime and lean_* rlibs were compiled against specific versions of libc etc.
      -- that live in the cargo deps directory.  Without that -L path rustc reports
      -- "found possibly newer version of crate `libc`" and refuses to link.
      let depsDir := s!"{sysroot}/lean_stdlib/target/release/deps"
      let depsDirArg : Array String :=
        if ← (System.FilePath.mk depsDir).pathExists then #["-L", depsDir] else #[]
      let rustcArgs := #["--crate-type=staticlib", "--emit=obj", "--edition=2021", s!"--crate-name={crateName}", "-C", s!"opt-level={optLevel}", "-C", "debug-assertions=no"] ++ debug ++ #["--extern", s!"lean_runtime={rlib}", "-L", libDir] ++ pkgExterns ++ depsDirArg ++ #["-o", outfile, sourcefile]
      if args.contains "-v" then
        IO.eprintln s!"rustc {" ".intercalate rustcArgs.toList}"
      let child ← IO.Process.spawn { cmd := "rustc", args := rustcArgs }
      let exitCode ← child.wait
      if exitCode != 0 then return exitCode
      if args.contains "-c" then return 0
      -- Continue to link with clang
      let mut newArgs := #[]
      for arg in args do
        if arg == sourcefile then
          newArgs := newArgs.push outfile
        else
          newArgs := newArgs.push arg
      args := newArgs
    else
      IO.eprintln "leanc: no input rust files"
      return 1

  let mut cc := "@LEANC_CC@".replace "ROOT" root.toString

  if args.isEmpty then
    IO.println s!"Lean compiler wrapper

A simple wrapper around a compiler (rustc or linker). Defaults to `{cc}`,
which can be overridden with the environment variable `LEAN_CC`. All parameters are passed
as-is to the wrapped compiler.

Interesting options:
* `--print-cflags`: print compiler flags necessary for building against the Lean runtime and exit
* `--print-ldflags`: print compiler flags necessary for statically linking against the Lean library and exit"
    return 1

  -- It is difficult to identify the correct minor version here, leading to linking warnings like:
  -- `ld64.lld: warning: /usr/lib/system/libsystem_kernel.dylib has version 13.5.0, which is newer than target minimum of 13.0.0`
  -- In order to suppress these we set the MACOSX_DEPLOYMENT_TARGET variable into the far future.
  let env := match (← IO.getEnv "MACOSX_DEPLOYMENT_TARGET") with
    | some _ => #[]
    | none   => #[("MACOSX_DEPLOYMENT_TARGET", "99.0")]

  -- let compileOnly := args.contains "-c"
  let linkStatic := !(args.contains "-shared" || args.contains "-leanshared")
  args := args.erase "-leanshared"

  -- We assume that the CMake variables do not contain escaped spaces
  let cflags := getCFlags root
  let mut cflagsInternal := getInternalCFlags root
  let mut ldflagsInternal := getInternalLinkerFlags root
  let mut ldflags := getLinkerFlags root linkStatic
  if System.Platform.isWindows && !args.contains "-shared" then
    ldflags := ldflags ++ #["-Wl,--whole-archive", "-lleanmanifest", "-Wl,--no-whole-archive"]

  for arg in args do
    match arg with
    | "--print-cflags" =>
      IO.println <| " ".intercalate cflags.toList
      return 0
    | "--print-ldflags" =>
      IO.println <| " ".intercalate (cflags ++ ldflags).toList
      return 0
    | _ => pure ()

  if let some cc' ← IO.getEnv "LEAN_CC" then
    cc := cc'
    -- these are intended for the bundled compiler only
    cflagsInternal := #[]
    ldflagsInternal := #[]
  args := cflags ++ cflagsInternal ++ args ++ ldflagsInternal ++ ldflags ++ ["-Wno-unused-command-line-argument"]
  args := args.filter (!·.isEmpty)
  if args.contains "-v" then
    IO.eprintln s!"{cc} {" ".intercalate args.toList}"
  let child ← IO.Process.spawn { cmd := cc, args, env }
  child.wait
