#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";
import {
  ensureModLine,
  ensureFnVisibility,
  findOccurrencesInRoots,
  findFunctionBodies,
  groupDistinctBodies,
  lean4Root,
  listRustFiles,
  moveRustFn,
  printOccurrences,
  removeBlock,
  rustfmtFiles,
  sourceRoot,
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
const commonRoot = path.join(genInitFfiRoot, "ffi/common");
const commonModuleFile = path.join(commonRoot, "mod.rs");
const initRoot = path.join(genInitFfiRoot, "ffi/Init");
const privRoot = path.join(genInitFfiRoot, "priv");
const privModuleFile = path.join(privRoot, "mod.rs");
const todoRoot = path.join(genInitFfiRoot, "todo_import_from_lean");
const todoModuleFile = path.join(todoRoot, "mod.rs");

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
  "use leanh_l1::datatypes::{LeanExternalObject, LeanObject, LeanScalarArray, LeanStringObject};",
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

function destinationFor(fnName: string, todoSymbols: Set<string>, commonExists: boolean): Destination {
  if (commonExists) {
    return {
      kind: "ffi_common",
      targetDir: commonRoot,
      moduleFile: commonModuleFile,
      rootModuleFile: genInitFfiLib,
    };
  }
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

async function findExistingInitBody(fnName: string): Promise<FnOccurrence | null> {
  const files = await listRustFiles(initRoot);
  const matches: FnOccurrence[] = [];
  for (const file of files) {
    const text = await fs.readFile(file, "utf8");
    for (const occ of findFunctionBodies(text, fnName)) {
      occ.file = file;
      matches.push(occ);
    }
  }

  if (matches.length === 0) return null;
  if (matches.length > 1) {
    await printOccurrences("Existing gen_init_ffi Init bodies", matches);
    throw new Error(`expected at most one existing ffi/Init body for ${fnName}`);
  }
  return matches[0];
}

function renderDistinctBodies(distinctBodies: ReturnType<typeof groupDistinctBodies>, logScriptName: string): string {
  return distinctBodies
    .map((group) => {
      const files = group.sources
        .map((src) => `${src.file}:${src.startLine}-${src.endLine}`)
        .filter((value, idx, arr) => arr.indexOf(value) === idx)
        .join(" and from ");
      return [
        `// appended by ${logScriptName} from ${files}`,
        ensureFnVisibility(group.text),
      ].join("\n");
    })
    .join("\n\n");
}

type ForbiddenRootReport = {
  leanhL1Bodies: FnOccurrence[];
  leanhL1Decls: FnOccurrence[];
  leanhL1InitializersBodies: FnOccurrence[];
  leanhL1InitializersDecls: FnOccurrence[];
  runtimeBodies: FnOccurrence[];
  runtimeDecls: FnOccurrence[];
  leanhL2Bodies: FnOccurrence[];
  leanhL2Decls: FnOccurrence[];
};

async function reportForbiddenRoots(fnName: string): Promise<ForbiddenRootReport> {
  const leanhL1Bodies = await findOccurrencesInRoots([leanhL1Root], fnName, "body", genInitFfiRoot);
  const leanhL1Decls = await findOccurrencesInRoots([leanhL1Root], fnName, "decl", genInitFfiRoot);
  const leanhL1InitializersBodies = await findOccurrencesInRoots(
    [leanhL1InitializersRoot],
    fnName,
    "body",
    genInitFfiRoot,
  );
  const leanhL1InitializersDecls = await findOccurrencesInRoots(
    [leanhL1InitializersRoot],
    fnName,
    "decl",
    genInitFfiRoot,
  );
  const runtimeBodies = await findOccurrencesInRoots([runtimeRoot], fnName, "body", genInitFfiRoot);
  const runtimeDecls = await findOccurrencesInRoots([runtimeRoot], fnName, "decl", genInitFfiRoot);
  const leanhL2Bodies = await findOccurrencesInRoots([leanhL2Root], fnName, "body", genInitFfiRoot);
  const leanhL2Decls = await findOccurrencesInRoots([leanhL2Root], fnName, "decl", genInitFfiRoot);
  return {
    leanhL1Bodies,
    leanhL1Decls,
    leanhL1InitializersBodies,
    leanhL1InitializersDecls,
    runtimeBodies,
    runtimeDecls,
    leanhL2Bodies,
    leanhL2Decls,
  };
}

function printRootSummary(label: string, report: ForbiddenRootReport) {
  const bodyCount =
    label === "leanh_l1"
      ? report.leanhL1Bodies.length
      : label === "leanh_l1_initializers"
        ? report.leanhL1InitializersBodies.length
        : label === "runtime"
          ? report.runtimeBodies.length
          : report.leanhL2Bodies.length;
  const declCount =
    label === "leanh_l1"
      ? report.leanhL1Decls.length
      : label === "leanh_l1_initializers"
        ? report.leanhL1InitializersDecls.length
        : label === "runtime"
          ? report.runtimeDecls.length
          : report.leanhL2Decls.length;
  console.log(`- ${label} - ${bodyCount > 0 || declCount > 0 ? "yes" : "no"}`);
}

function rootHasAny(report: ForbiddenRootReport, label: string) {
  if (label === "leanh_l1") {
    return report.leanhL1Bodies.length > 0 || report.leanhL1Decls.length > 0;
  }
  if (label === "leanh_l1_initializers") {
    return report.leanhL1InitializersBodies.length > 0 || report.leanhL1InitializersDecls.length > 0;
  }
  if (label === "runtime") {
    return report.runtimeBodies.length > 0 || report.runtimeDecls.length > 0;
  }
  return report.leanhL2Bodies.length > 0 || report.leanhL2Decls.length > 0;
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
  let hadForbiddenDuplicate = false;

  for (const fnName of fnNames) {
    const forbiddenReport = await reportForbiddenRoots(fnName);
    const rootLabels = ["leanh_l1", "leanh_l1_initializers", "runtime", "leanh_l2"] as const;
    const initOcc = await findExistingInitBody(fnName);
    const missingRoots = rootLabels.filter((label) => !rootHasAny(forbiddenReport, label));
    const hasForbidden = missingRoots.length !== rootLabels.length;
    const hasInitBody = initOcc !== null;

    if (hasForbidden || hasInitBody) {
      await printOccurrences("Forbidden bodies in leanh_l1", forbiddenReport.leanhL1Bodies);
      await printOccurrences("Forbidden decls in leanh_l1", forbiddenReport.leanhL1Decls);
      await printOccurrences(
        "Forbidden bodies in leanh_l1_initializers",
        forbiddenReport.leanhL1InitializersBodies,
      );
      await printOccurrences(
        "Forbidden decls in leanh_l1_initializers",
        forbiddenReport.leanhL1InitializersDecls,
      );
      console.log(`\nSummary for ${fnName}:`);
      for (const label of rootLabels) {
        printRootSummary(label, forbiddenReport);
      }
      console.log(`- gen_init_ffi - ${hasInitBody ? "yes" : "no"}`);
      if (hasInitBody && initOcc) {
        await printOccurrences("Existing gen_init_ffi Init bodies", [initOcc]);
      }
      if (hasForbidden && missingRoots.length > 0) {
        console.log(`- missing roots - ${missingRoots.join(", ")}`);
      }
      console.error(
        `Tried to cut out function ${fnName} but couldnt bc it's already defined in deps of gen_init_ffi or in gen_init_ffi.`,
      );
      hadForbiddenDuplicate = true;
      continue;
    }

    const commonExists = await fs
      .stat(path.join(commonRoot, `${fnName}.rs`))
      .then((s) => s.isFile())
      .catch(() => false);

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
      getDestination: (_sourceOcc: FnOccurrence) => destinationFor(fnName, todoSymbols, commonExists),
      logScriptName: "move_rust_fn_to_gen_init_ffi.ts",
      rustfmtTargets: (destination, targetPath) => {
        const targets = [destination.moduleFile, targetPath];
        if (destination.rootModuleFile) targets.push(destination.rootModuleFile);
        return targets;
      },
    });
  }

  if (hadForbiddenDuplicate) {
    process.exit(1);
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
