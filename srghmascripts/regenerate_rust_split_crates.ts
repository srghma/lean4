#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

type Tree = {
  name: string;
  children: Map<string, Tree>;
  source?: string;
};

type SplitCrate = {
  name: string;
  roots: string[];
  deps: string[];
};

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const rustDir = path.join(rootDir, "src/rust");
const runtimeSrcDir = path.join(rustDir, "lean_runtime/src");
const genRoot = path.join(runtimeSrcDir, "gen");
const leanImportsRoot = path.join(runtimeSrcDir, "lean_imports_rs");

const crates: SplitCrate[] = [
  { name: "lean_gen_init", roots: ["Init"], deps: [] },
  { name: "lean_gen_std", roots: ["Std"], deps: ["lean_gen_init"] },
  { name: "lean_gen_lean", roots: ["Lean"], deps: ["lean_gen_init", "lean_gen_std"] },
  { name: "lean_gen_lake", roots: ["Lake", "LakeMain"], deps: ["lean_gen_init", "lean_gen_std", "lean_gen_lean"] },
  {
    name: "lean_gen_tools",
    roots: ["Leanc", "LeanIR", "LeanChecker"],
    deps: ["lean_gen_init", "lean_gen_std", "lean_gen_lean", "lean_gen_lake"],
  },
];

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

const buildModuleTree = async (sourceRoot: string, roots?: Set<string>) => {
  const root: Tree = { name: "", children: new Map() };

  for await (const file of walkFiles(sourceRoot)) {
    if (!file.endsWith(".rs")) continue;
    const rel = path.relative(sourceRoot, file).replaceAll(path.sep, "/");
    const parts = rel.split("/");
    if (roots && !roots.has(parts[0]!.replace(/\.rs$/, ""))) continue;

    let node = root;
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

const modulePath = (fromDir: string, toFile: string) => path.relative(fromDir, toFile).replaceAll(path.sep, "/");

const emitTree = (node: Tree, includeBaseDir: string, indent = "") => {
  const lines: string[] = [];
  const children = [...node.children.entries()].sort(([a], [b]) => a.localeCompare(b));

  for (const [name, child] of children) {
    if (child.children.size === 0) {
      if (!child.source) continue;
      lines.push(`${indent}pub mod ${name} {`);
      lines.push(`${indent}    include!(${JSON.stringify(modulePath(includeBaseDir, child.source))});`);
      lines.push(`${indent}}`);
      continue;
    }

    lines.push(`${indent}pub mod ${name} {`);
    if (child.source) {
      lines.push(`${indent}    pub mod index {`);
      lines.push(`${indent}        include!(${JSON.stringify(modulePath(includeBaseDir, child.source))});`);
      lines.push(`${indent}    }`);
      lines.push(`${indent}    pub use index::*;`);
    }

    const nested = emitTree(child, includeBaseDir, `${indent}    `);
    if (nested.length > 0) lines.push(...nested);
    lines.push(`${indent}}`);
  }

  return lines;
};

const dependencyPackage = (name: string) => `${name} = { path = "../${name}" }`;

const writeCommonCrate = async () => {
  const crateDir = path.join(rustDir, "lean_runtime_common");
  const leanImportsTree = await buildModuleTree(leanImportsRoot);
  const leanImportsLines = emitTree(leanImportsTree, path.join(crateDir, "src"), "    ");
  const leanImportsExtraLines = leanImportsTree.children.has("lake") ? ["", "    pub use lake::Lake;"] : [];
  await fs.mkdir(path.join(crateDir, "src"), { recursive: true });
  await fs.writeFile(
    path.join(crateDir, "Cargo.toml"),
    [
      "[package]",
      'name = "lean_runtime_common"',
      'version = "0.1.0"',
      'edition = "2024"',
      "publish = false",
      "",
      "[dependencies]",
      'libc = "0.2"',
      'libloading = "0.9"',
      "",
      "[lints.rust]",
      "",
    ].join("\n"),
  );
  await fs.writeFile(
    path.join(crateDir, "src/lib.rs"),
    [
      "#![allow(dead_code, non_upper_case_globals, non_snake_case)]",
      "#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]",
      "",
      `#[path = ${JSON.stringify(modulePath(path.join(crateDir, "src"), path.join(runtimeSrcDir, "leanh.rs")))}]`,
      "pub mod leanh;",
      "",
      "pub mod lean_imports_rs {",
      ...leanImportsLines,
      ...leanImportsExtraLines,
      "}",
      "",
    ].join("\n"),
  );
};

const writeSplitCrate = async ({ name, roots, deps }: SplitCrate) => {
  const crateDir = path.join(rustDir, name);
  await fs.mkdir(path.join(crateDir, "src"), { recursive: true });
  await fs.writeFile(
    path.join(crateDir, "Cargo.toml"),
    [
      "[package]",
      `name = ${JSON.stringify(name)}`,
      'version = "0.1.0"',
      'edition = "2024"',
      "publish = false",
      "",
      "[dependencies]",
      'lean_runtime_common = { path = "../lean_runtime_common" }',
      ...deps.map(dependencyPackage),
      "",
    ].join("\n"),
  );

  const tree = await buildModuleTree(genRoot, new Set(roots));
  const depRootReexports = deps.flatMap((dep) => {
    const depCrate = crates.find((c) => c.name === dep);
    if (!depCrate) return [];
    return depCrate.roots.map((root) => `    pub use ${dep}::r#gen::${root};`);
  });
  const rootLines = emitTree(tree, path.join(crateDir, "src"), "    ");
  await fs.writeFile(
    path.join(crateDir, "src/lib.rs"),
    [
      "#![allow(dead_code, non_upper_case_globals, non_snake_case)]",
      "#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]",
      "",
      "pub mod leanh {",
      "    pub use lean_runtime_common::leanh::*;",
      "}",
      "",
      "pub mod lean_imports_rs {",
      "    pub use lean_runtime_common::lean_imports_rs::*;",
      "}",
      "",
      "pub mod r#gen {",
      ...depRootReexports,
      ...rootLines,
      "}",
      "",
    ].join("\n"),
  );
};

await writeCommonCrate();
for (const splitCrate of crates) {
  await writeSplitCrate(splitCrate);
}

console.error(`wrote ${crates.length + 1} split Rust crates under ${path.relative(rootDir, rustDir)}`);
