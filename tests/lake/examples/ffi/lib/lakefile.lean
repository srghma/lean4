import Lake
open System Lake DSL

package ffi where
  srcDir := "lean"

@[default_target]
lean_exe test where
  root := `Main

lean_lib FFI

/-! ## Static C FFI Library -/

input_file ffi_static.c where
  path := "c" / "ffi_static.c"
  text := true

target ffi_static.o pkg : FilePath := do
  let srcJob ← ffi_static.c.fetch
  let oFile := pkg.buildDir / "c" / "ffi_static.o"
  buildO oFile srcJob #[] #["-fPIC"] "cc"

target libleanffi_static pkg : FilePath := do
  let ffiO ← ffi_static.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib FFI.Static where
  moreLinkObjs := #[libleanffi_static]

/-! ## Shared Rust FFI Library -/

input_file ffi_shared_cargo where
  path := "c" / "ffi_shared" / "Cargo.toml"
  text := true

input_file ffi_shared.rs where
  path := "c" / "ffi_shared" / "src" / "lib.rs"
  text := true

target ffi_shared.a pkg : FilePath := do
  let cargoJob ← ffi_shared_cargo.fetch
  let srcJob ← ffi_shared.rs.fetch
  (Job.collectArray #[cargoJob, srcJob] "ffi_shared Rust sources").mapM fun _ => do
    addLeanTrace
    addPlatformTrace
    let aFile := pkg.buildDir / "c" / "libffi_shared.a"
    let cargoTargetDir := pkg.buildDir / "rust"
    let cargoOut := cargoTargetDir / "release" / "libffi_shared.a"
    let art ← buildArtifactUnlessUpToDate aFile (ext := "a") do
      createParentDirs aFile
      proc {
        cmd := "cargo"
        args := #[
          "build",
          "--release",
          "--manifest-path", (pkg.dir / "c" / "ffi_shared" / "Cargo.toml").toString,
          "--target-dir", cargoTargetDir.toString
        ]
      }
      copyFile cargoOut aFile
    return art.path

target libleanffi_shared pkg : Dynlib := do
  let libName := "leanffi"
  let ffiAJob ← ffi_shared.a.fetch
  -- Use --whole-archive so all symbols from the Rust static archive are exported.
  ffiAJob.mapM fun aPath => do
    addLeanTrace
    addPlatformTrace
    let leanArgs ← getLeanLinkSharedFlags
    let libFile := pkg.sharedLibDir / nameToSharedLib libName
    let linkArgs := #["-Wl,--whole-archive", aPath.toString, "-Wl,--no-whole-archive",
                      "-L", (← getLeanLibDir).toString] ++ leanArgs
    let art ← buildArtifactUnlessUpToDate libFile (ext := sharedLibExt) (restore := true) do
      compileSharedLib libFile linkArgs "cc"
    return {name := libName, path := art.path, deps := #[], plugin := false}

lean_lib FFI.Shared where
  moreLinkLibs := #[libleanffi_shared]

/-! ## Executable-only FFI -/

@[default_target]
lean_exe standalone where
  root := `Standalone
  moreLinkObjs := #[libleanffi_static]
  moreLinkLibs := #[libleanffi_shared]
