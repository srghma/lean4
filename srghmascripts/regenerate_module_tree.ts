#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

type Tree = {
  name: string;
  children: Map<string, Tree>;
  source?: string;
};

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const runtimeSrcDir = path.join(rootDir, "src/rust/lean_runtime/src");
const genRoot = path.join(runtimeSrcDir, "gen");
const leanImportsRoot = path.join(runtimeSrcDir, "lean_imports_rs");

type TargetName = "gen" | "lean_imports_rs";

const usage = () => {
  console.error(
    [
      "usage:",
      "  bun srghmascripts/regenerate_module_tree.ts gen",
      "  bun srghmascripts/regenerate_module_tree.ts lean_imports_rs [--roots=Init,Lean,Std,lake]",
    ].join("\n"),
  );
  process.exit(2);
};

const targetArg = process.argv[2] as TargetName | undefined;
if (targetArg !== "gen" && targetArg !== "lean_imports_rs") usage();

const rootsArg = process.argv.find((arg) => arg.startsWith("--roots="));
const selectedRoots = rootsArg
  ? new Set(
      rootsArg
        .slice("--roots=".length)
        .split(",")
        .map((root) => root.trim())
        .filter(Boolean),
    )
  : undefined;

const targetRoot = targetArg === "gen" ? genRoot : leanImportsRoot;
const targetOutput = path.join(runtimeSrcDir, `${targetArg}.rs`);

async function* walkFiles(dir: string): AsyncGenerator<string> {
  for (const entry of await fs.readdir(dir, { withFileTypes: true }).catch(() => [])) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      yield* walkFiles(abs);
    } else if (entry.isFile()) {
      yield abs;
    }
  }
}

const sanitizeModuleName = (name: string) => {
  const stem = name.replace(/\.rs$/, "");
  return ["gen", "loop", "type"].includes(stem) ? `r#${stem}` : stem;
};

const buildModuleTree = async (sourceRoot: string) => {
  const root: Tree = { name: "", children: new Map() };

  for await (const file of walkFiles(sourceRoot)) {
    if (!file.endsWith(".rs")) continue;
    const rel = path.relative(sourceRoot, file).replaceAll(path.sep, "/");
    const parts = rel.split("/");

    if (selectedRoots && !selectedRoots.has(parts[0]!.replace(/\.rs$/, ""))) {
      continue;
    }

    let node: Tree = root;
    for (const part of parts.slice(0, -1)) {
      const name = sanitizeModuleName(part);
      const child = node.children.get(name) ?? { name, children: new Map() };
      node.children.set(name, child);
      node = child;
    }

    const leafName = sanitizeModuleName(parts.at(-1)!);
    const child = node.children.get(leafName) ?? { name: leafName, children: new Map() };
    child.source = file;
    node.children.set(leafName, child);
  }

  return root;
};

const emitTree = (node: Tree, physicalDir: string, attrBaseDir: string, indent = "") => {
  const lines: string[] = [];
  const children = [...node.children.entries()].sort(([a], [b]) => a.localeCompare(b));

  for (const [name, child] of children) {
    if (child.children.size === 0) {
      if (!child.source) continue;
      const sourcePath = path.relative(attrBaseDir, child.source).replaceAll(path.sep, "/");
      lines.push(`${indent}#[path = ${JSON.stringify(sourcePath)}]`);
      lines.push(`${indent}pub mod ${name};`);
      continue;
    }

    lines.push(`${indent}pub mod ${name} {`);
    const childPhysicalDir = path.join(physicalDir, name);

    if (child.source) {
      const indexPath = path.relative(childPhysicalDir, child.source).replaceAll(path.sep, "/");
      lines.push(`${indent}    #[path = ${JSON.stringify(indexPath)}]`);
      lines.push(`${indent}    pub mod index;`);
      lines.push(`${indent}    pub use index::*;`);
    }

    const nested = emitTree(child, childPhysicalDir, childPhysicalDir, `${indent}    `);
    if (nested.length > 0) lines.push(...nested);
    lines.push(`${indent}}`);
  }

  return lines;
};

const main = async () => {
  const tree = await buildModuleTree(targetRoot);
  const lines = emitTree(tree, targetRoot, path.dirname(targetOutput));
  const content = [
    "#![allow(unused_variables)]",
    "#![allow(unused_assignments)]",
    "#![allow(unused_parens)]",
    "#![allow(unused_mut)]",
    "",
    ...lines,
    "",
  ].join("\n");
  await fs.writeFile(targetOutput, content);
  console.error(
    [
      `wrote ${path.relative(rootDir, targetOutput)}`,
      selectedRoots ? `filtered roots: ${[...selectedRoots].join(", ")}` : "all roots included",
    ].join("; "),
  );
};

main().catch((err) => {
  console.error(String(err?.stack ?? err));
  process.exit(1);
});
