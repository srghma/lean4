#!/usr/bin/env bun

import path from "node:path";
import { lean4Root, moveRustFn, usage, workRoot, type Destination, type FnOccurrence } from "./lib/move_rust_fn";

const initRoot = path.join(workRoot, "leanh_l1_initializers/src");
const runtimeRoot = path.join(workRoot, "runtime/src");
const leanhL2Root = path.join(workRoot, "leanh_l2/src");
const generatedRoots = [
  path.join(workRoot, "gen_init/src"),
  path.join(workRoot, "gen_lean/src"),
  path.join(workRoot, "gen_lean_part_1/src"),
  path.join(workRoot, "gen_lean_part_2/src"),
  path.join(workRoot, "gen_lean_part_3/src"),
  path.join(workRoot, "gen_lean_part_4/src"),
  path.join(workRoot, "gen_lean_part_5/src"),
  path.join(workRoot, "gen_std/src"),
  path.join(workRoot, "lake/src"),
];

function moduleNameFromFile(file: string): string | null {
  const base = path.basename(file).replace(/\.rs_?$/, "");
  if (/^(?:kernel|library|runtime)_[A-Za-z0-9_]+$/.test(base)) {
    return base;
  }
  return null;
}

function getDestination(sourceOcc: FnOccurrence): Destination {
  const normalized = path.resolve(sourceOcc.file);

  if (
    normalized === path.resolve(path.join(runtimeRoot, "base.rs")) ||
    normalized === path.resolve(path.join(leanhL2Root, "base.rs")) ||
    path.basename(normalized) === "lib.rs"
  ) {
    return {
      kind: "priv",
      targetDir: path.join(initRoot, "priv"),
      moduleFile: path.join(initRoot, "priv.rs"),
      prelude:
        "use std::ffi::c_void;\nuse leanh_l1::datatypes::{LeanExternalObject, LeanObject, Size};\n",
    };
  }

  const moduleName = moduleNameFromFile(normalized);
  if (moduleName) {
    return {
      kind: "module",
      targetDir: path.join(initRoot, moduleName),
      moduleFile: path.join(initRoot, `${moduleName}.rs`),
      rootModuleFile: path.join(initRoot, "lib.rs"),
      prelude:
        "use std::ffi::c_void;\nuse leanh_l1::datatypes::{LeanExternalObject, LeanObject, Size};\n",
    };
  }

  throw new Error(
    `unsupported source location for destination routing: ${path.relative(lean4Root, sourceOcc.file)}\n` +
      `expected runtime/src/base.rs, leanh_l2/src/base.rs, lean4-rust/.../lib.rs, or a kernel_*/library_*/runtime_* module`,
  );
}

async function main() {
  const fnNames = process.argv.slice(2);
  if (fnNames.length === 0) {
    usage("Usage: move_rust_fn_to_leanh_l1_initializers.ts <function_name> [function_name ...]");
  }
  for (const fnName of fnNames) {
    await moveRustFn(fnName, {
      usage: "Usage: move_rust_fn_to_leanh_l1_initializers.ts <function_name> [function_name ...]",
      currentRoots: [runtimeRoot, leanhL2Root],
      ignoreDir: initRoot,
      getDestination,
      logScriptName: "move_rust_fn_to_leanh_l1_initializers.ts",
      generatedFallback: {
        roots: generatedRoots,
        targetDir: path.join(initRoot, "todo_import_from_lean"),
        moduleFile: path.join(initRoot, "todo_import_from_lean.rs"),
      },
    });
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
