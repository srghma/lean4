#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

type Tree = {
  name: string;
  children: Map<string, Tree>;
  source?: string;
};

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const rustDir = path.join(rootDir, "src/rust");

type TargetName = "gen" | "ffi";

const crateRoots = new Map([
  ["gen_init", ["Init"]],
  ["gen_std", ["Std"]],
  ["gen_lean", ["Lean"]],
  ["lake", ["Lake", "LakeMain"]],
  ["lean_checker", ["LeanChecker"]],
  ["lean_ir", ["LeanIR"]],
  ["leanc", ["Leanc"]],
]);

const usage = () => {
  console.error(
    [
      "usage:",
      "  bun srghmascripts/regenerate_module_tree.ts <crate> [--depends-on=gen_init,gen_std]",
      "  bun srghmascripts/regenerate_module_tree.ts gen <crate> [--roots=Init,Lean,Std] [--depends-on=gen_init,gen_std]",
      "  bun srghmascripts/regenerate_module_tree.ts ffi <crate>",
      "",
      "examples:",
      "  bun srghmascripts/regenerate_module_tree.ts gen_init",
      "  bun srghmascripts/regenerate_module_tree.ts gen gen_init",
      "  bun srghmascripts/regenerate_module_tree.ts ffi gen_init",
    ].join("\n"),
  );
  process.exit(2);
};

const cliArg = process.argv[2];
const targetArg: TargetName = cliArg === "ffi" ? "ffi" : "gen";
const crateArg = cliArg === "gen" || cliArg === "ffi" ? process.argv[3] : cliArg;
if (!crateArg || !crateRoots.has(crateArg)) usage();

const rootsArg = process.argv.find((arg) => arg.startsWith("--roots="));
const dependsOnArg = process.argv.find((arg) => arg.startsWith("--depends-on="));
const selectedRoots = rootsArg
  ? new Set(
      rootsArg
        .slice("--roots=".length)
        .split(",")
        .map((root) => root.trim())
        .filter(Boolean),
    )
  : undefined;
const dependsOn = dependsOnArg
  ? dependsOnArg
      .slice("--depends-on=".length)
      .split(",")
      .map((crate) => crate.trim())
      .filter(Boolean)
  : [];

const crateSrcDir = path.join(rustDir, crateArg, "src");
const targetRoot = path.join(crateSrcDir, targetArg);
const targetOutput = path.join(crateSrcDir, `${targetArg}.rs`);

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

const moduleIdent = (name: string) => sanitizeModuleName(name);

const emitIncludeTree = (sourceRoot: string, roots: string[]) => {
  const lines: string[] = [];

  const emitDir = async (relDir: string, indent: string): Promise<void> => {
    const indexPath = relDir ? path.join(sourceRoot, `${relDir}.rs`) : "";
    if (relDir && await fs.stat(indexPath).then((s) => s.isFile()).catch(() => false)) {
      lines.push(`${indent}pub mod index {`);
      lines.push(`${indent}    include!(${JSON.stringify(path.posix.join("gen", relDir.replaceAll(path.sep, "/") + ".rs"))});`);
      lines.push(`${indent}}`);
      lines.push(`${indent}pub use index::*;`);
    }

    const dir = path.join(sourceRoot, relDir);
    const entries = await fs.readdir(dir, { withFileTypes: true }).catch(() => []);
    for (const entry of entries.sort((a, b) => a.name.localeCompare(b.name))) {
      const childRel = path.join(relDir, entry.name.replace(/\.rs$/, ""));
      const childIdent = moduleIdent(entry.name.replace(/\.rs$/, ""));
      if (entry.isDirectory()) {
        lines.push(`${indent}pub mod ${childIdent} {`);
        await emitDir(childRel, `${indent}    `);
        lines.push(`${indent}}`);
      } else if (entry.isFile() && entry.name.endsWith(".rs")) {
        const dirForStem = path.join(sourceRoot, childRel);
        if (await fs.stat(dirForStem).then((s) => s.isDirectory()).catch(() => false)) continue;
        lines.push(`${indent}pub mod ${childIdent} {`);
        lines.push(`${indent}    include!(${JSON.stringify(path.posix.join("gen", childRel.replaceAll(path.sep, "/") + ".rs"))});`);
        lines.push(`${indent}}`);
      }
    }
  };

  return { lines, emitDir };
};

const main = async () => {
  if (targetArg === "gen") {
    const roots = selectedRoots ? [...selectedRoots] : crateRoots.get(crateArg)!;
    const emitter = emitIncludeTree(targetRoot, roots);
    for (const depCrate of dependsOn) {
      const depRoots = crateRoots.get(depCrate);
      if (!depRoots) {
        throw new Error(`unknown dependency crate ${depCrate}`);
      }
      for (const depRoot of depRoots) {
        emitter.lines.push(`pub use ${depCrate}::r#gen::${depRoot};`);
      }
    }
    for (const root of roots) {
      emitter.lines.push(`pub mod ${moduleIdent(root)} {`);
      await emitter.emitDir(root, "    ");
      emitter.lines.push("}");
    }
    const content = [
      "#![allow(dead_code, non_upper_case_globals, non_snake_case)]",
      "#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]",
      "",
      ...emitter.lines,
      "",
    ].join("\n");
    await fs.writeFile(targetOutput, content);
    console.error(`wrote ${path.relative(rootDir, targetOutput)}`);
    return;
  }

  const tree = await buildModuleTree(targetRoot);
  const lines = emitTree(tree, targetRoot, path.dirname(targetOutput));
  const content = [
    "#![allow(dead_code, non_upper_case_globals, non_snake_case)]",
    "#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]",
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
