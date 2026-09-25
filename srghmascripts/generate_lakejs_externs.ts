#!/usr/bin/env bun
import fs from "node:fs/promises";
import path from "node:path";
import { glob } from "node:fs/promises";
import { parseArgs } from "node:util";
import {
  parseFileExterns,
  extractImports,
  buildScanTree,
  treeToTopoSortedArray,
  loadCppDefinitions,
  loadExistingLakeJsImplementations,
  generateLakeJsContent,
} from "./generate_lakejs_externs/lib";

const ROOT_DIR = path.resolve(path.join(import.meta.dir, ".."));
const SRC_DIR = path.join(ROOT_DIR, "src");
const DEFAULT_OUT_DIR = path.join(SRC_DIR, "LakeJs", "JsImplOfKnownExternFunctions");

const { values, positionals } = parseArgs({
  args: process.argv.slice(2),
  options: {
    all: { type: "boolean", short: "a" },
    print: { type: "boolean", short: "p" },
    "no-write": { type: "boolean" },
    "out-dir": { type: "string" },
    help: { type: "boolean", short: "h" },
  },
  allowPositionals: true,
  strict: true,
});

if (values.help) {
  console.log(`Usage: ./srghmascripts/generate_lakejs_externs.ts [options] [pkg]

Scans Lean files for @[extern] definitions and attributes, orders them topologically,
and generates JS_EXPR scaffolding with Lean & C++ implementations commented out.

Arguments:
  pkg                     Package to process: Init (default), Std, or Lean

Options:
  -a, --all               Process all packages: Init, Std, and Lean
  -p, --print             Print generated Lean file content to stdout
  --no-write              Do not write generated files to disk
  --out-dir <path>        Custom output directory (default: src/LakeJs/JsImplOfKnownExternFunctions)
  -h, --help              Show this help message
`);
  process.exit(0);
}

const outDir = values["out-dir"] ? path.resolve(values["out-dir"]) : DEFAULT_OUT_DIR;
const shouldWrite = !values["no-write"];
const shouldPrint = !!values.print;

let packagesToProcess: string[] = [];
if (values.all) {
  packagesToProcess = ["Init", "Std", "Lean"];
} else if (positionals.length > 0) {
  packagesToProcess = positionals;
} else {
  packagesToProcess = ["Init"];
}

// Preload C++ definitions and existing LakeJs implementations
console.error("Loading C++ definitions and existing LakeJs implementations...");
const cppDefs = await loadCppDefinitions(SRC_DIR);
const existingImpls = await loadExistingLakeJsImplementations(DEFAULT_OUT_DIR);
console.error(`Loaded ${cppDefs.size} C++ definitions and ${existingImpls.global.size} LakeJs implementations.`);

async function processPackage(pkg: string): Promise<string> {
  const pkgDir = path.join(SRC_DIR, pkg);
  const scannedFiles: Array<{
    relPath: string;
    imports: string[];
    functions: ReturnType<typeof parseFileExterns>;
  }> = [];

  for await (const absFile of glob(`${pkgDir}/**/*.lean`)) {
    const relPath = path.relative(SRC_DIR, absFile);
    const content = await fs.readFile(absFile, "utf8");
    const imports = extractImports(content);
    const functions = parseFileExterns(content);
    scannedFiles.push({ relPath, imports, functions });
  }

  // Build directory tree
  const tree = buildScanTree(scannedFiles);

  // Transform to topologically sorted array: Array<[RootRelativePath, FileFunctions]>
  const sortedArray = treeToTopoSortedArray(tree);

  // Generate output content
  const generatedContent = generateLakeJsContent(sortedArray, cppDefs, existingImpls);

  if (shouldWrite) {
    await fs.mkdir(outDir, { recursive: true });
    const outFile = path.join(outDir, `${pkg}.lean`);
    await fs.writeFile(outFile, generatedContent, "utf8");
    console.error(`Wrote ${outFile} (${sortedArray.length} files scanned, generated ${generatedContent.split("\n").length} lines)`);
  }

  return generatedContent;
}

for (const pkg of packagesToProcess) {
  const content = await processPackage(pkg);
  if (shouldPrint) {
    process.stdout.write(content);
  }
}
