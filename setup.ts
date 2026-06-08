#!/usr/bin/env bun
// Setup script for lean4 rust-rewrite3 (NixOS).
// Works on a completely clean project.
//
// Architecture:
//   stage0 — original C++ lean (from stage0/), built by cmake.
//             Uses EmitC backend: lean files → C files.
//   stage1 — C++ runtime (same as stage0) + EmitRust backend compiled in.
//             cmake builds the C++ runtime (kernel/util/shell/runtime/library) and
//             the Rust lean_runtime (src/rust/lean_runtime) into libleanshell.a.
//             Then stdlib.make (bash/make) drives stage0's lean binary to compile
//             the lean stdlib → C files → shared libs, and links the lean binary.
//             When stage1's lean binary runs on user code, it uses EmitRust → .rs files.
//   stage2 — Rust runtime + EmitRust.
//             stage1's lean binary compiles all lean stdlib .lean → .rs files.
//             lean_lean (~503 MB of .rs source) is topo-sorted and split into N
//             sub-crates (~130 MB each) so each rustc invocation fits in RAM.
//             cargo builds lean_init → lean_std → lean_lean_0..N → lean_lean
//             (umbrella) → lean_lake → lean_binary.

import { $, Glob } from "bun";
import { parseArgs } from "util";
import * as path from "path";
import * as fs from "fs/promises";
import * as os from "os";
import { processReports } from "./parse_errors_lib";

// ============================================================================
// Initialization & Argument Parsing
// ============================================================================

for (const cmd of ["cmake", "cargo", "rustc", "make"]) {
  if (!Bun.which(cmd)) {
    console.error(`ERROR: '${cmd}' is not installed or not in PATH. Are you inside the Nix shell?`);
    process.exit(1);
  }
}

const PROJECT = process.cwd();
const BUILD = path.join(PROJECT, "build/release");
const NPROC = os.cpus().length;

const { values: args } = parseArgs({
  args: Bun.argv.slice(2),
  options: {
    "run-tests": { type: "boolean", default: false },
    from: { type: "string", default: "clean" },
  },
});

const RUN_TESTS = args["run-tests"] ?? false;
const FROM_STAGE = args.from ?? "clean";

const stages = ["clean", "stage0", "stage1", "rs", "cargo", "setup"];
const startIdx = stages.indexOf(FROM_STAGE);
if (startIdx === -1) {
  console.error(`Unknown stage '${FROM_STAGE}'; valid: clean stage0 stage1 rs cargo setup`);
  console.error(`
Usage: setup.ts [--from=STAGE] [--run-tests]

  --from=clean   (default) full rebuild from scratch
  --from=stage0  skip clean
  --from=stage1  skip clean + stage0
  --from=rs      skip clean + stage0 + stage1  (reuse stage1 binary, regen .rs)
  --from=cargo   skip clean + stage0 + stage1 + .rs gen  (reuse .rs, rebuild cargo)
  --from=setup   skip all builds, just cmake-configure stage2 + optional tests

  --run-tests    run ctest against stage2 after setup
`);
  process.exit(1);
}

const shouldRun = (stage: string) => stages.indexOf(stage) >= startIdx;

// ============================================================================
// 1. Clean
// ============================================================================
if (!shouldRun("clean")) {
  console.log(`=== Skipping clean (--from=${FROM_STAGE}) ===`);
  if (shouldRun("rs")) await $`rm -rf ${PROJECT}/build/release/stage2/src/generated/`;
  if (shouldRun("cargo")) await $`rm -rf ${PROJECT}/build/release/stage2/lean_stdlib/`;
} else {
  console.log("=== Cleaning build ===");
  await $`rm -rdf ${PROJECT}/build`;
  await $`git clean -d --force -x -e .direnv/ -e .envrc -e .gemini/`;
}

// ============================================================================
// 2. Check / update stage0 against upstream/master
// ============================================================================
if (!shouldRun("stage0")) {
  console.log(`=== Skipping stage0 check (--from=${FROM_STAGE}) ===`);
} else {
  console.log("=== Checking stage0 against origin/master ===");
  const { exitCode: hasOrigin } = await $`git remote get-url origin`.cwd(PROJECT).quiet().nothrow();
  if (hasOrigin !== 0) {
    console.error("ERROR: remote 'origin' not found; skipping stage0 check.");
    console.error("  Add it: git remote add origin https://github.com/leanprover/lean4.git");
    process.exit(1);
  } else {
    const { stdout: stage0Diff } = await $`git diff origin/master -- stage0/`.cwd(PROJECT).quiet();
    if (stage0Diff.length > 0) {
      console.log("  stage0/ differs from origin/master — updating...");
      await $`git checkout origin/master -- stage0/`.cwd(PROJECT);
      console.log("  stage0/ updated.");
    } else {
      console.log("  stage0/ matches origin/master. OK.");
    }
  }

  // ── 3. Build stage0 via cmake ──
  console.log("=== Configuring cmake ===");
  await $`cmake -S ${PROJECT} -B ${BUILD} -DCMAKE_BUILD_TYPE=Release`;

  console.log("=== Building stage0 (cmake) ===");
  await $`make -C ${BUILD} -j${NPROC} stage0`;

  // Check if stage0/ has dirty files or untracked changes
  const { exitCode: dirtyState } = await $`git -C ${PROJECT} diff --quiet -- stage0/`.quiet().nothrow();
  const { stdout: untrackedFiles } = await $`git -C ${PROJECT} status --porcelain stage0/`.quiet();

  if (dirtyState !== 0 || untrackedFiles.toString().trim().length > 0) {
    console.log("\n\x1b[1;31m⚠️  WARNING: Local modifications or untracked files detected in stage0/ !\x1b[0m");
    console.log("\x1b[31mThese files will be permanently reset/overwritten to match the clean upstream stage0 state.\x1b[0m");
    console.log("\x1b[31mPress Ctrl+C within 3 seconds to abort this script...\x1b[0m");
    await Bun.sleep(3000);
    console.log("  Resetting stage0/...");
    await $`git -C ${PROJECT} checkout -- stage0/`;
    await $`git -C ${PROJECT} clean -fd -- stage0/`;
  } else {
    console.log("  stage0/ is clean. No reset necessary.");
  }
}

// ============================================================================
// 4. Build stage1
// ============================================================================
// cmake configure generates the stage1 build environment:
//   - leanc.sh      (compiler/linker wrapper with correct NIX store paths)
//   - lakefile.toml (lake project descriptor)
//   - stdlib.make   (make-based lean stdlib builder)
// cmake build compiles:
//   - C++ objects (kernel, util, shell, runtime, library → object files)
//   - Rust lean_runtime (src/rust/lean_runtime → libleanshell.a)
//
// stdlib.make then drives:
//   - stage0's lean binary compiles lean stdlib → C files (EmitC, since stage0 has EmitC)
//     NOTE: the lean SOURCES we're compiling include EmitRust.lean, so stage1's lean
//     binary will contain the EmitRust backend and generate .rs files when run.
//   - C files → shared libs (libInit_shared.so, libleanshared.so, etc.)
//   - lean binary linked: libleanshell.a (Rust runtime) + shared libs
if (!shouldRun("stage1")) {
  console.log(`=== Skipping stage1 build (--from=${FROM_STAGE}) ===`);
} else {
  console.log("=== Building stage1 ===");
  await $`make -C ${BUILD} -j${NPROC} stage1`;
}

// ============================================================================
// 5. Build stage2
// ============================================================================
// Uses stage1's lean binary (with EmitRust) to compile all lean stdlib .lean files
// to .rs files, then builds a pure-Rust lean binary with cargo.
//
// Generated .rs files go into build/release/stage2/src/generated/.
// lean_lean (~503 MB) is topologically split into N sub-crates (~130 MB each)
// so each rustc invocation fits within 15 GB RAM.
// lean_shell_main depends on lean_binary → lean_shell → all stdlib packages.
const STAGE1_LEAN = `${BUILD}/stage1/bin/lean`;
const STAGE1_OLEAN = `${BUILD}/stage1/lib/lean`;
const STAGE2_DIR = `${BUILD}/stage2`;
const STAGE2_RS = `${STAGE2_DIR}/src/generated`;
const STAGE2_OLEAN = `${STAGE2_DIR}/olean`;
const LEAN_STDLIB_DIR = `${STAGE2_DIR}/lean_stdlib`;

if (shouldRun("rs")) {
  console.log("\n=== Stage2: generating .rs files from lean stdlib ===");
  await fs.mkdir(STAGE2_RS, { recursive: true });
  await fs.mkdir(STAGE2_OLEAN, { recursive: true });

  // Build a list of (src_file, rs_out, olean_out) for every module that has both
  // a stage1 olean and a source file in src/.
  const oleans = new Glob("**/*.olean").scanSync({ cwd: STAGE1_OLEAN });
  const compileList: { src: string, rsOut: string, oleanOut: string, root: string }[] = [];

  for (const file of oleans) {
    const modulePath = file.replace(/\.olean$/, "");
    let srcFile = path.join(PROJECT, "src", `${modulePath}.lean`);
    let root = `${PROJECT}/src`;

    // Lake sources live under src/lake/, not src/
    if (!(await fs.exists(srcFile)) && (modulePath.startsWith("Lake/") || modulePath === "Lake")) {
      srcFile = path.join(PROJECT, "src/lake", `${modulePath}.lean`);
      root = `${PROJECT}/src/lake`;
    }

    if (await fs.exists(srcFile)) {
      const rsOut = path.join(STAGE2_RS, `${modulePath}.rs`);
      const oleanOut = path.join(STAGE2_OLEAN, `${modulePath}.olean`);
      compileList.push({ src: srcFile, rsOut, oleanOut, root });
    }
  }

  console.log(`  Found ${compileList.length} modules to compile to Rust`);

  // Compile each module in parallel
  const tasks = Array.from(compileList);
  await Promise.all(Array.from({ length: NPROC }, async () => {
    while (tasks.length > 0) {
      const task = tasks.pop()!;
      await fs.mkdir(path.dirname(task.rsOut), { recursive: true });
      await fs.mkdir(path.dirname(task.oleanOut), { recursive: true });
      try {
        await $`${STAGE1_LEAN} --c=${task.rsOut} --o=${task.oleanOut} --root=${task.root} ${task.src}`
          .env({ ...process.env, LEAN_PATH: STAGE1_OLEAN })
          .quiet();
      } catch (err) {
        console.error(`WARN: failed to compile ${task.src}`);
      }
    }
  }));

  const genCount = Array.from(new Glob("**/*.rs").scanSync({ cwd: STAGE2_RS })).length;
  console.log(`  Generated ${genCount} .rs files`);
}

// ============================================================================
// Tree Generators & Utilities
// ============================================================================

class ModNode {
  hasFile = false;
  grp: number | null = null;
  children = new Map<string, ModNode>();
}

// Emit pub mod tree for packages without split
function emitSimpleTree(node: ModNode, prefix: string, indent: number): string {
  let out = "";
  const pad = "    ".repeat(indent);
  const keys = Array.from(node.children.keys()).sort();

  for (const name of keys) {
    const child = node.children.get(name)!;
    out += `${pad}pub mod ${name} {\n`;
    if (child.hasFile) {
      out += `${pad}    include!("../../../src/generated/${prefix}${name}.rs");\n`;
    }
    if (child.children.size > 0) {
      out += emitSimpleTree(child, `${prefix}${name}/`, indent + 1);
    }
    out += `${pad}}\n`;
  }
  return out;
}

// Check if subtree has files in [lo, hi]
function hasInRange(node: ModNode, lo: number, hi: number): boolean {
  if (node.grp !== null && node.grp >= lo && node.grp <= hi) return true;
  for (const child of node.children.values()) {
    if (hasInRange(child, lo, hi)) return true;
  }
  return false;
}

// Emit pub mod tree for lean_lean split packages (Perfect cascade superset logic)
function emitLeanTree(node: ModNode, currentPath: string, curGrp: number, indent: number): string {
  let out = "";
  const pad = "    ".repeat(indent);
  const keys = Array.from(node.children.keys()).sort();

  for (const name of keys) {
    const child = node.children.get(name)!;
    const cp = currentPath ? `${currentPath}/${name}` : name;

    // Only process this child if it or its descendants have files in curGrp
    const hasC = hasInRange(child, curGrp, curGrp);
    if (!hasC) continue;

    out += `${pad}pub mod ${name} {\n`;

    // Inherit from the previous group if this subtree existed ANYWHERE before curGrp
    // Because lean_lean_{G} is a superset of {G-1}, importing from {curGrp - 1} recursively grabs the history.
    if (curGrp > 0 && hasInRange(child, 0, curGrp - 1)) {
      const rp = cp.replace(/\//g, "::");
      out += `${pad}    pub use lean_lean_${curGrp - 1}::${rp}::*;\n`;
    }

    // Include file if it belongs to curGrp
    if (child.grp === curGrp) {
      out += `${pad}    include!("../../../src/generated/${cp}.rs");\n`;
    }

    // Recurse for children
    if (child.children.size > 0) {
      out += emitLeanTree(child, cp, curGrp, indent + 1);
    }

    out += `${pad}}\n`;
  }
  return out;
}

// Gather all files for a given package prefix
async function getPkgFiles(prefix: string): Promise<string[]> {
  const localPrefix = prefix.replace(/\/$/, "");
  const files: string[] = [];
  if (await Bun.file(path.join(STAGE2_RS, `${localPrefix}.rs`)).exists()) {
    files.push(`${localPrefix}.rs`);
  }
  const dirPath = path.join(STAGE2_RS, prefix);
  const stat = await fs.stat(dirPath).catch(() => null);
  if (stat && stat.isDirectory()) {
    for (const file of new Glob("**/*.rs").scanSync({ cwd: dirPath })) {
      files.push(`${prefix}${file}`);
    }
  }
  return files.sort();
}

// ============================================================================
// 5b. Generate lean_stdlib workspace
// ============================================================================
if (shouldRun("cargo")) {
  console.log("=== Stage2: generating lean_stdlib workspace ===");
  await fs.mkdir(LEAN_STDLIB_DIR, { recursive: true });

  // ── Topo sort & Split Logic for lean_lean
  console.log("  Topo-sorting lean_lean modules (target 130 MB per group)...");
  const leanFiles = await getPkgFiles("Lean/");
  const modules = new Map<string, number>();

  for (const file of leanFiles) {
    const fullPath = path.join(STAGE2_RS, file);
    const size = (await fs.stat(fullPath)).size;
    modules.set(file.replace(/\.rs$/, ""), size);
  }

  const deps = new Map<string, Set<string>>();
  const rdeps = new Map<string, Set<string>>();
  for (const k of modules.keys()) {
    deps.set(k, new Set());
    rdeps.set(k, new Set());
  }

  const useRe = /\buse crate::(Lean(?:::[A-Za-z_][A-Za-z0-9_]*)+)/g;
  for (const modKey of modules.keys()) {
    const filePath = path.join(STAGE2_RS, `${modKey}.rs`);
    try {
      const content = await Bun.file(filePath).text();
      for (const match of content.matchAll(useRe)) {
        const parts = match[1].split("::");
        let dep: string | null = null;
        for (let i = parts.length; i > 0; i--) {
          const k = parts.slice(0, i).join("/");
          if (modules.has(k) && k !== modKey) {
            dep = k;
            break;
          }
        }
        if (dep) {
          deps.get(modKey)!.add(dep);
          rdeps.get(dep)!.add(modKey);
        }
      }
    } catch (e) { }
  }

  const inDeg = new Map<string, number>();
  for (const k of modules.keys()) inDeg.set(k, deps.get(k)!.size);

  const q = Array.from(modules.keys()).filter(k => inDeg.get(k) === 0).sort();
  const order: string[] = [];
  while (q.length > 0) {
    q.sort(); // Min-priority queue to maintain determinism
    const k = q.shift()!;
    order.push(k);
    const dependents = Array.from(rdeps.get(k) || []).sort();
    for (const d of dependents) {
      const newDeg = inDeg.get(d)! - 1;
      inDeg.set(d, newDeg);
      if (newDeg === 0) q.push(d);
    }
  }

  const orderedSet = new Set(order);
  for (const k of Array.from(modules.keys()).sort()) {
    if (!orderedSet.has(k)) order.push(k);
  }

  const groups: string[][] = [[]];
  let curSz = 0;
  const TARGET_SIZE = 130_000_000;
  for (const k of order) {
    const sz = modules.get(k)!;
    if (curSz + sz > TARGET_SIZE && groups[groups.length - 1].length > 0) {
      groups.push([]);
      curSz = 0;
    }
    groups[groups.length - 1].push(k);
    curSz += sz;
  }

  const assignments = new Map<string, number>();
  groups.forEach((grp, i) => grp.forEach(k => assignments.set(k, i)));

  const NUM_LEAN_GROUPS = groups.length;
  console.log(`  lean_lean split into ${NUM_LEAN_GROUPS} groups:`);
  groups.forEach((grp, i) => {
    const szBytes = grp.reduce((acc, k) => acc + modules.get(k)!, 0);
    console.log(`    lean_lean_${i}: ${grp.length} modules (~${(szBytes / 1_000_000).toFixed(1)} MB)`);
  });

  const PACKAGES: string[] = [];
  const LEAN_SUB_PKGS: string[] = [];

  const PKG_DEPS_lean_init = `lean_runtime = { path = "../../../../../src/rust/lean_runtime" }`;
  const PKG_DEPS_lean_std = `lean_runtime = { path = "../../../../../src/rust/lean_runtime" }\nlean_init = { path = "../lean_init" }`;
  const PKG_DEPS_lean_lake = `lean_runtime = { path = "../../../../../src/rust/lean_runtime" }
lean_init = { path = "../lean_init" }
lean_std = { path = "../lean_std" }
lean_lean = { path = "../lean_lean" }`;

  const buildTree = (files: string[], useAssignments: boolean): ModNode => {
    const root = new ModNode();
    for (const p of files) {
      const parts = p.replace(/\.rs$/, "").split("/");
      let node = root;
      for (let i = 0; i < parts.length; i++) {
        const part = parts[i];
        if (!node.children.has(part)) node.children.set(part, new ModNode());
        node = node.children.get(part)!;
        if (i === parts.length - 1) {
          node.hasFile = true;
          if (useAssignments) {
            node.grp = assignments.get(p.replace(/\.rs$/, "")) ?? null;
          }
        }
      }
    }
    return root;
  };

  // ── Generate lean_init and lean_std
  for (const pkg of ["lean_init", "lean_std"]) {
    const prefix = pkg === "lean_init" ? "Init/" : "Std/";
    const pkgDeps = pkg === "lean_init" ? PKG_DEPS_lean_init : PKG_DEPS_lean_std;

    PACKAGES.push(pkg);
    const pkgDir = path.join(LEAN_STDLIB_DIR, pkg);
    await fs.mkdir(path.join(pkgDir, "src"), { recursive: true });

    await Bun.write(path.join(pkgDir, "Cargo.toml"), `[package]
name = "${pkg}"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["rlib"]

[dependencies]
${pkgDeps}
`);

    const files = await getPkgFiles(prefix);
    const rootNode = buildTree(files, false);
    const codeTree = files.length > 0 ? emitSimpleTree(rootNode, "", 0) : "";

    await Bun.write(path.join(pkgDir, "src/lib.rs"), `#![allow(warnings, non_upper_case_globals, non_snake_case, non_camel_case_types, dead_code, unused_imports, clashing_extern_declarations)]\n${codeTree}`);
    console.log(`  Package ${pkg}: ${files.length} modules`);
  }

  // ── Generate lean_lean_0..N-1
  const leanRootNode = buildTree(leanFiles, true);
  for (let G = 0; G < NUM_LEAN_GROUPS; G++) {
    const pkg = `lean_lean_${G}`;
    LEAN_SUB_PKGS.push(pkg);
    PACKAGES.push(pkg);

    const pkgDir = path.join(LEAN_STDLIB_DIR, pkg);
    await fs.mkdir(path.join(pkgDir, "src"), { recursive: true });

    let depLines = `lean_runtime = { path = "../../../../../src/rust/lean_runtime" }
lean_init = { path = "../lean_init" }
lean_std = { path = "../lean_std" }`;
    for (let H = 0; H < G; H++) {
      depLines += `\nlean_lean_${H} = { path = "../lean_lean_${H}" }`;
    }

    await Bun.write(path.join(pkgDir, "Cargo.toml"), `[package]
name = "${pkg}"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["rlib"]

[dependencies]
${depLines}
`);

    const codeTree = emitLeanTree(leanRootNode, "", G, 0);
    // Cascade root items from the prior group ensuring a perfectly chained tree
    const rootExports = G > 0 ? `pub use lean_lean_${G - 1}::*;\n` : "";

    await Bun.write(path.join(pkgDir, "src/lib.rs"), `#![allow(warnings, non_upper_case_globals, non_snake_case, non_camel_case_types, dead_code, unused_imports, clashing_extern_declarations)]\n${rootExports}${codeTree}`);
    console.log(`  Package ${pkg}: ${groups[G].length} modules`);
  }

  // ── Generate lean_lean umbrella
  const LAST_G = NUM_LEAN_GROUPS - 1;
  const umbrellaPkg = "lean_lean";
  PACKAGES.push(umbrellaPkg);
  const umbrellaDir = path.join(LEAN_STDLIB_DIR, umbrellaPkg);
  await fs.mkdir(path.join(umbrellaDir, "src"), { recursive: true });

  await Bun.write(path.join(umbrellaDir, "Cargo.toml"), `[package]
name = "lean_lean"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["rlib"]

[dependencies]
lean_lean_${LAST_G} = { path = "../lean_lean_${LAST_G}" }
`);
  await Bun.write(path.join(umbrellaDir, "src/lib.rs"), `#![allow(warnings)]\npub use lean_lean_${LAST_G}::*;`);
  console.log(`  Package lean_lean: umbrella → lean_lean_${LAST_G}`);

  // ── Generate lean_lake
  const lakePkg = "lean_lake";
  PACKAGES.push(lakePkg);
  const lakeDir = path.join(LEAN_STDLIB_DIR, lakePkg);
  await fs.mkdir(path.join(lakeDir, "src"), { recursive: true });

  await Bun.write(path.join(lakeDir, "Cargo.toml"), `[package]
name = "lean_lake"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["rlib"]

[dependencies]
${PKG_DEPS_lean_lake}
`);

  const lakeFiles = await getPkgFiles("Lake/");
  const lakeRootNode = buildTree(lakeFiles, false);
  const lakeTree = lakeFiles.length > 0 ? emitSimpleTree(lakeRootNode, "", 0) : "";

  await Bun.write(path.join(lakeDir, "src/lib.rs"), `#![allow(warnings, non_upper_case_globals, non_snake_case, non_camel_case_types, dead_code, unused_imports, clashing_extern_declarations)]\nextern crate self as lean_lake;\n${lakeTree}`);
  console.log(`  Package lean_lake: ${lakeFiles.length} modules`);

  // ── Root workspace Cargo.toml + lean_stdlib staticlib + lean_binary
  await fs.mkdir(path.join(LEAN_STDLIB_DIR, "src"), { recursive: true });
  await fs.mkdir(path.join(LEAN_STDLIB_DIR, "lean_binary/src"), { recursive: true });

  const workspaceMembers = PACKAGES.map(p => `  "${p}",`).join("\n") + '\n  "lean_binary",';
  const profileOverrides = LEAN_SUB_PKGS.map(pkg => `
[profile.release.package.${pkg}]
opt-level = 0
codegen-units = 1
`).join("");

  await Bun.write(path.join(LEAN_STDLIB_DIR, "lean_binary/Cargo.toml"), `[package]
name = "lean_binary"
version = "0.1.0"
edition = "2021"
publish = false

[[bin]]
name = "lean"
path = "src/main.rs"

[dependencies]
lean_shell = { path = "../../../../../src/rust/lean_shell" }
lean_init  = { path = "../lean_init" }
lean_std   = { path = "../lean_std" }
lean_lean  = { path = "../lean_lean" }
lean_lake  = { path = "../lean_lake" }
`);

  await Bun.write(path.join(LEAN_STDLIB_DIR, "lean_binary/src/main.rs"), `// Force-link all stdlib rlibs so their #[no_mangle] C symbols are available.
extern crate lean_init;
extern crate lean_std;
extern crate lean_lean;
extern crate lean_lake;

fn main() {
    let args: Vec<std::ffi::CString> = std::env::args()
        .map(|a| std::ffi::CString::new(a).unwrap_or_default())
        .collect();
    let mut cargs: Vec<*mut core::ffi::c_char> =
        args.iter().map(|a| a.as_ptr() as *mut _).collect();
    cargs.push(core::ptr::null_mut());
    let exit_code = unsafe {
        lean_shell::lean_main(args.len() as core::ffi::c_int, cargs.as_mut_ptr())
    };
    std::process::exit(exit_code);
}
`);

  await Bun.write(path.join(LEAN_STDLIB_DIR, "Cargo.toml"), `[workspace]
members = [
${workspaceMembers}
]

[package]
name = "lean_stdlib"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["staticlib"]

[dependencies]
lean_runtime = { path = "../../../../src/rust/lean_runtime", features = ["export-runtime-ffi"] }
lean_init  = { path = "lean_init" }
lean_std   = { path = "lean_std" }
lean_lean  = { path = "lean_lean" }
lean_lake  = { path = "lean_lake" }

[profile.release]
opt-level = 1
codegen-units = 1
lto = false
${profileOverrides}
`);

  await Bun.write(path.join(LEAN_STDLIB_DIR, "src/lib.rs"), `#![allow(warnings)]
extern crate lean_runtime;
extern crate lean_init;
extern crate lean_std;
extern crate lean_lean;
extern crate lean_lake;
`);

  console.log(`  Generated lean_stdlib workspace (${PACKAGES.length} packages)`);

  // ── Setup future-incompatibilities collector ──
  const collectedReportIds = new Set<string>();

  async function runCargoWithCapture(cargoArgs: string[]): Promise<void> {
    const proc = Bun.spawn(["cargo", ...cargoArgs], {
      stdout: "inherit", // stdout goes directly to terminal
      stderr: "pipe"     // stderr piped so we can scrape it real-time
    });

    const decoder = new TextDecoder();
    let stderrAccumulator = "";

    const reader = proc.stderr.getReader();
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      const chunk = decoder.decode(value, { stream: true });
      process.stderr.write(chunk);
      stderrAccumulator += chunk;
    }

    const exitCode = await proc.exited;
    if (exitCode !== 0) {
      console.error(`\nCargo command failed with exit code ${exitCode}`);
      process.exit(exitCode);
    }

    // Capture the ID matches from output
    const matches = stderrAccumulator.matchAll(/--id\s+(\d+)/g);
    for (const match of matches) {
      collectedReportIds.add(match[1]);
    }
  }

  // ── 5c. Build lean_stdlib (sequential by dependency order) ──
  console.log("=== Stage2: building lean_stdlib with cargo (sequential packages) ===");
  for (const pkg of PACKAGES) {
    console.log(`  cargo build ${pkg}...`);
    await runCargoWithCapture([
      "build", "--release", "-p", pkg,
      "--future-incompat-report",
      "--manifest-path", `${LEAN_STDLIB_DIR}/Cargo.toml`
    ]);
  }
  console.log("  cargo build final lean_stdlib staticlib...");
  await runCargoWithCapture([
    "build", "--release", "-p", "lean_stdlib",
    "--future-incompat-report",
    "--manifest-path", `${LEAN_STDLIB_DIR}/Cargo.toml`
  ]);

  // ── 5d. Build the stage2 lean binary ──
  console.log("=== Stage2: building lean binary ===");
  await runCargoWithCapture([
    "build", "--release", "-p", "lean_binary",
    "--future-incompat-report",
    "--manifest-path", `${LEAN_STDLIB_DIR}/Cargo.toml`
  ]);

  await fs.mkdir(path.join(STAGE2_DIR, "bin"), { recursive: true });
  await $`cp ${LEAN_STDLIB_DIR}/target/release/lean ${STAGE2_DIR}/bin/lean`;
  console.log(`  stage2 lean binary: ${STAGE2_DIR}/bin/lean`);

  // ── Process collected future-incompatibility reports ──
  if (collectedReportIds.size > 0) {
    console.log(`\n=== Found future-incompatibility reports: IDs ${Array.from(collectedReportIds).join(", ")} ===`);
    const REPORT_RAW_DIR = "/tmp/reports";
    const REPORT_SHORT_DIR = "/tmp/reports-short";

    // Clean and recreate directories
    await $`rm -rf ${REPORT_RAW_DIR} ${REPORT_SHORT_DIR}`;
    await fs.mkdir(REPORT_RAW_DIR, { recursive: true });
    await fs.mkdir(REPORT_SHORT_DIR, { recursive: true });

    for (const id of collectedReportIds) {
      console.log(`  Generating raw report for ID ${id}...`);
      const reportProc = Bun.spawn([
        "cargo", "report", "future-incompatibilities",
        "--id", id,
        "--manifest-path", `${LEAN_STDLIB_DIR}/Cargo.toml`
      ], {
        stdout: "pipe",
        stderr: "inherit"
      });
      const outputBytes = await Bun.readableStreamToArrayBuffer(reportProc.stdout);
      const outputText = new TextDecoder().decode(outputBytes);
      await reportProc.exited;

      await Bun.write(path.join(REPORT_RAW_DIR, `${id}.txt`), outputText);
    }

    console.log(`  Processing and parsing reports...`);
    await processReports(REPORT_RAW_DIR, REPORT_SHORT_DIR);
  }
}

// ============================================================================
// 5e. Populate stage2 layout for cmake test infrastructure
// ============================================================================
console.log("=== Stage2: setting up cmake test infrastructure ===");
await fs.mkdir(path.join(STAGE2_DIR, "lib/lean"), { recursive: true });
await fs.mkdir(path.join(STAGE2_DIR, "bin"), { recursive: true });

// Oleans: use stage2-generated ones
await $`rsync -a --delete ${STAGE2_OLEAN}/ ${STAGE2_DIR}/lib/lean/`;

// Tests also need cadical, leantar, and leanc.sh from stage1
for (const f of ["cadical", "leantar", "leanc.sh"]) {
  const srcF = path.join(BUILD, "stage1/bin", f);
  if (await Bun.file(srcF).exists()) {
    await $`cp -f ${srcF} ${STAGE2_DIR}/bin/${f}`;
  }
}

// Generate leanc wrapper that uses stage2 lean binary
const leancWrapper = `#!/usr/bin/env bash\nexec "${STAGE2_DIR}/bin/lean" --run "$@"\n`;
const leancPath = path.join(STAGE2_DIR, "bin/leanc");
await Bun.write(leancPath, leancWrapper);
await $`chmod +x ${leancPath}`;

// cmake configure for stage2
await $`cmake -S ${PROJECT}/src -B ${STAGE2_DIR} -DCMAKE_BUILD_TYPE=Release -DSTAGE=2 -DPREV_STAGE=${BUILD}/stage1`;
console.log(`  stage2 cmake configured — tests point at ${STAGE2_DIR}/bin/lean`);

if (RUN_TESTS) {
  console.log("=== Running cargo tests ===");
  const runtimeDir = path.join(PROJECT, "src/rust/lean_runtime");
  await $`cargo test -p lean_runtime`.cwd(runtimeDir);
  await $`cargo test -p lean_shell`.cwd(runtimeDir);
  await $`cargo build -p lean_runtime`.cwd(runtimeDir);
  await $`cargo build -p lean_shell`.cwd(runtimeDir);

  console.log("=== Running CTest against stage2 (Rust lean binary) ===");
  await $`CTEST_PARALLEL_LEVEL=${NPROC} CTEST_OUTPUT_ON_FAILURE=1 ctest --test-dir ${STAGE2_DIR} -E bench -j${NPROC} --output-on-failure`;
} else {
  console.log("=== Skipping tests. Use --run-tests to execute them. ===");
}

// ============================================================================
// Done
// ============================================================================
console.log(`
=== Done ===
  stage0 lean : ${BUILD}/stage0/bin/lean
  stage1 lean : ${BUILD}/stage1/bin/lean
  stage2 lean : ${STAGE2_DIR}/bin/lean  (pure Rust)
  stage2 stdlib: ${LEAN_STDLIB_DIR} (liblean_stdlib.a)

Run tests against stage2 (Rust lean binary):
  CTEST_PARALLEL_LEVEL=$(nproc) CTEST_OUTPUT_ON_FAILURE=1 \\
    ctest --test-dir ${STAGE2_DIR} -E bench -j$(nproc)

Run a single test manually:
  tests/with_stage2_test_env.sh tests/elab/run_test.sh grind_ematch.lean
`);
