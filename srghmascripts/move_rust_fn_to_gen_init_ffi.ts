#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";
import {
  ensureModLine,
  findOccurrencesInRoots,
  lean4Root,
  moveRustFn,
  printOccurrences,
  rustfmtFiles,
  usage,
  workRoot,
  type Destination,
  type FnOccurrence,
} from "./lib/move_rust_fn";

type ExportJsonItem = {
  symbolName: string;
};

type ExportJsonReport = {
  bySymbol: Record<string, Array<{ relativePath: string; item: ExportJsonItem }>>;
};

const genInitFfiRoot = path.join(workRoot, "gen_init_ffi/src");
const genInitFfiLib = path.join(genInitFfiRoot, "lib.rs");
const privRoot = path.join(genInitFfiRoot, "priv");
const privModuleFile = path.join(genInitFfiRoot, "priv.rs");
const todoRoot = path.join(genInitFfiRoot, "todo_import_from_lean");
const todoModuleFile = path.join(genInitFfiRoot, "todo_import_from_lean.rs");

const runtimeRoot = path.join(workRoot, "runtime/src");
const leanhL2Root = path.join(workRoot, "leanh_l2/src");
const leanhL1Root = path.join(workRoot, "leanh_l1/src");
const leanhL1InitializersRoot = path.join(workRoot, "leanh_l1_initializers/src");

const exportJsonPath = path.join(
  lean4Root,
  "srghmascripts/exported_imported_lean_rust_fns--rust_should_import_from_lean.json",
);

const genericPrelude = [
  "use std::ffi::c_void;",
  "use leanh_l1::datatypes::{LeanExternalObject, LeanObject, LeanScalarArray, LeanStringObject, Size};",
  "",
].join("\n");

async function loadTodoImportSymbols(): Promise<Set<string>> {
  let parsed: ExportJsonReport;
  try {
    parsed = JSON.parse(await fs.readFile(exportJsonPath, "utf8")) as ExportJsonReport;
  } catch (err) {
    throw new Error(
      `failed to read ${path.relative(lean4Root, exportJsonPath)}.\n` +
        `run srghmascripts/exported_imported_lean_rust_fns.ts first so the JSON reports exist.\n` +
        `inner error: ${String(err)}`,
    );
  }
  return new Set(Object.keys(parsed.bySymbol ?? {}));
}

function destinationFor(fnName: string, todoSymbols: Set<string>): Destination {
  const shouldGoToTodo = todoSymbols.has(fnName);
  if (shouldGoToTodo) {
    return {
      kind: "todo_import_from_lean",
      targetDir: todoRoot,
      moduleFile: todoModuleFile,
      rootModuleFile: genInitFfiLib,
    };
  }
  return {
    kind: "priv",
    targetDir: privRoot,
    moduleFile: privModuleFile,
    rootModuleFile: genInitFfiLib,
    prelude: genericPrelude,
  };
}

async function assertNotInForbiddenRoots(fnName: string) {
  const forbiddenBodies = await findOccurrencesInRoots(
    [leanhL1Root, leanhL1InitializersRoot],
    fnName,
    "body",
    genInitFfiRoot,
  );
  const forbiddenDecls = await findOccurrencesInRoots(
    [leanhL1Root, leanhL1InitializersRoot],
    fnName,
    "decl",
    genInitFfiRoot,
  );
  if (forbiddenBodies.length === 0 && forbiddenDecls.length === 0) return;

  await printOccurrences("Forbidden bodies in leanh_l1 / leanh_l1_initializers", forbiddenBodies);
  await printOccurrences("Forbidden decls in leanh_l1 / leanh_l1_initializers", forbiddenDecls);
  throw new Error(
    `refusing to move ${fnName}: it already exists in leanh_l1 or leanh_l1_initializers, so it must not be moved into gen_init_ffi`,
  );
}

async function createTodoPlaceholder(fnName: string) {
  await fs.mkdir(todoRoot, { recursive: true });
  const targetPath = path.join(todoRoot, `${fnName}.rs`);
  const exists = await fs
    .stat(targetPath)
    .then((s) => s.isFile())
    .catch(() => false);
  if (!exists) {
    const content = [
      `// placeholder created by move_rust_fn_to_gen_init_ffi.ts`,
      `// function is listed in exported_imported_lean_rust_fns--rust_should_import_from_lean.json`,
      `// fill this module manually from Lean-side implementation details`,
      "",
    ].join("\n");
    await fs.writeFile(targetPath, content, "utf8");
  }
  await ensureModLine(todoModuleFile, fnName);
  await ensureModLine(genInitFfiLib, "todo_import_from_lean");
  await rustfmtFiles([todoModuleFile, genInitFfiLib, targetPath]);
  console.log(`\nCreated placeholder ${path.relative(lean4Root, targetPath)}.`);
}

async function main() {
  const fnNames = process.argv.slice(2);
  if (fnNames.length === 0) {
    usage("Usage: move_rust_fn_to_gen_init_ffi.ts <function_name> [function_name ...]");
  }

  const todoSymbols = await loadTodoImportSymbols();

  for (const fnName of fnNames) {
    await assertNotInForbiddenRoots(fnName);

    const currentBodies = await findOccurrencesInRoots(
      [runtimeRoot, leanhL2Root],
      fnName,
      "body",
      genInitFfiRoot,
    );
    const currentDecls = await findOccurrencesInRoots(
      [runtimeRoot, leanhL2Root],
      fnName,
      "decl",
      genInitFfiRoot,
    );

    if (currentBodies.length === 0 && currentDecls.length === 0 && todoSymbols.has(fnName)) {
      await createTodoPlaceholder(fnName);
      continue;
    }

    await moveRustFn(fnName, {
      usage: "Usage: move_rust_fn_to_gen_init_ffi.ts <function_name> [function_name ...]",
      currentRoots: [runtimeRoot, leanhL2Root],
      ignoreDir: genInitFfiRoot,
      getDestination: (_sourceOcc: FnOccurrence) => destinationFor(fnName, todoSymbols),
      logScriptName: "move_rust_fn_to_gen_init_ffi.ts",
      rustfmtTargets: (destination, targetPath) => {
        const targets = [destination.moduleFile, targetPath];
        if (destination.rootModuleFile) targets.push(destination.rootModuleFile);
        return targets;
      },
    });
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
