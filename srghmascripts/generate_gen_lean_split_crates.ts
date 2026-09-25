#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

type ModuleInfo = {
  module: string;
  rustFile: string;
  deps: Set<string>;
  rustLines: number;
};

type Part = {
  crate: string;
  modules: string[];
  rustLines: number;
};

type Tree = {
  name: string;
  children: Map<string, Tree>;
  module?: string;
  depCrate?: string;
};

const PART_COUNT = 5;

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const rustDir = path.join(rootDir, "src/rust");
const genLeanCrate = path.join(rustDir, "gen_lean");
const genLeanSrc = path.join(genLeanCrate, "src/gen");

async function* walkFiles(dir: string): AsyncGenerator<string> {
  for (const entry of await fs.readdir(dir, { withFileTypes: true }).catch(() => [])) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) yield* walkFiles(abs);
    else if (entry.isFile()) yield abs;
  }
}

const collect = async <T>(items: AsyncIterable<T>) => {
  const out: T[] = [];
  for await (const item of items) out.push(item);
  return out;
};

const lineCount = async (file: string) => {
  const text = await fs.readFile(file, "utf8").catch(() => "");
  if (text.length === 0) return 0;
  return text.endsWith("\n") ? text.split("\n").length - 1 : text.split("\n").length;
};

const moduleForRustFile = (file: string) =>
  path.relative(genLeanSrc, file).replace(/\.rs$/, "").replaceAll(path.sep, ".");

const moduleRel = (mod: string) => `${mod.replaceAll(".", "/")}.rs`;

const sanitizeIdent = (name: string) => {
  const stem = name.replace(/\.rs$/, "");
  return ["gen", "loop", "type"].includes(stem) ? `r#${stem}` : stem;
};

const rustPathForModule = (mod: string) => mod.split(".").map(sanitizeIdent).join("::");

const formatNum = (n: number) => n.toLocaleString("en-US");

const tarjan = <T>(nodes: T[], deps: (node: T) => Iterable<T>) => {
  let index = 0;
  const stack: T[] = [];
  const onStack = new Set<T>();
  const indices = new Map<T, number>();
  const lowlinks = new Map<T, number>();
  const sccs: T[][] = [];

  const strongConnect = (v: T) => {
    indices.set(v, index);
    lowlinks.set(v, index);
    index += 1;
    stack.push(v);
    onStack.add(v);

    for (const w of deps(v)) {
      if (!indices.has(w)) {
        strongConnect(w);
        lowlinks.set(v, Math.min(lowlinks.get(v)!, lowlinks.get(w)!));
      } else if (onStack.has(w)) {
        lowlinks.set(v, Math.min(lowlinks.get(v)!, indices.get(w)!));
      }
    }

    if (lowlinks.get(v) === indices.get(v)) {
      const component: T[] = [];
      while (true) {
        const w = stack.pop()!;
        onStack.delete(w);
        component.push(w);
        if (w === v) break;
      }
      sccs.push(component);
    }
  };

  for (const node of nodes) if (!indices.has(node)) strongConnect(node);
  return sccs;
};

const topoComponents = (sccs: string[][], modules: Map<string, ModuleInfo>) => {
  const moduleToComponent = new Map<string, number>();
  sccs.forEach((scc, i) => scc.forEach((mod) => moduleToComponent.set(mod, i)));

  const deps = sccs.map(() => new Set<number>());
  const reverse = sccs.map(() => new Set<number>());
  for (const [mod, info] of modules) {
    const from = moduleToComponent.get(mod)!;
    for (const dep of info.deps) {
      const to = moduleToComponent.get(dep)!;
      if (from === to) continue;
      deps[from]!.add(to);
      reverse[to]!.add(from);
    }
  }

  const indegree = deps.map((d) => d.size);
  const ready = indegree.map((d, i) => d === 0 ? i : -1).filter((i) => i >= 0);
  const order: number[] = [];
  while (ready.length > 0) {
    ready.sort((a, b) => sccs[a]![0]!.localeCompare(sccs[b]![0]!));
    const cur = ready.shift()!;
    order.push(cur);
    for (const user of reverse[cur]!) {
      indegree[user] -= 1;
      if (indegree[user] === 0) ready.push(user);
    }
  }

  if (order.length !== sccs.length) throw new Error("module dependency graph has a cycle after SCC condensation");
  return order.map((i) => sccs[i]!.slice().sort());
};

const dependencyModulesFromRust = (src: string, modules: Set<string>) => {
  const deps = new Set<string>();
  const re = /crate::r#gen::((?:[A-Za-z_][A-Za-z0-9_]*)(?:::[A-Za-z_][A-Za-z0-9_]*)*)/g;
  for (const match of src.matchAll(re)) {
    const parts = match[1]!.split("::");
    for (let len = parts.length; len >= 1; len -= 1) {
      const candidate = parts.slice(0, len).join(".");
      if (modules.has(candidate)) {
        deps.add(candidate);
        break;
      }
    }
  }
  return deps;
};

const splitIntoParts = (components: string[][], modules: Map<string, ModuleInfo>) => {
  const componentLines = components.map((component) =>
    component.reduce((sum, mod) => sum + modules.get(mod)!.rustLines, 0)
  );
  const totalLines = componentLines.reduce((sum, n) => sum + n, 0);
  const parts: Part[] = [];
  let currentModules: string[] = [];
  let currentLines = 0;

  for (let i = 0; i < components.length; i += 1) {
    const remainingParts = PART_COUNT - parts.length;
    const remainingLines = componentLines.slice(i).reduce((sum, n) => sum + n, 0) + currentLines;
    const target = remainingLines / remainingParts;
    const nextLines = componentLines[i]!;

    if (
      currentModules.length > 0 &&
      remainingParts > 1 &&
      components.length - i >= remainingParts &&
      currentLines + nextLines > target &&
      Math.abs(target - currentLines) <= Math.abs(target - (currentLines + nextLines))
    ) {
      parts.push({
        crate: `gen_lean_part_${parts.length + 1}`,
        modules: currentModules,
        rustLines: currentLines,
      });
      currentModules = [];
      currentLines = 0;
    }

    currentModules.push(...components[i]!);
    currentLines += nextLines;
  }

  if (currentModules.length > 0) {
    parts.push({
      crate: `gen_lean_part_${parts.length + 1}`,
      modules: currentModules,
      rustLines: currentLines,
    });
  }

  if (parts.length > PART_COUNT) throw new Error(`expected at most ${PART_COUNT} parts, got ${parts.length}`);
  while (parts.length < PART_COUNT) {
    parts.push({ crate: `gen_lean_part_${parts.length + 1}`, modules: [], rustLines: 0 });
  }

  console.error(`total generated Lean Rust: ${formatNum(totalLines)} lines`);
  for (const part of parts) {
    console.error(`${part.crate}: ${formatNum(part.rustLines)} lines, ${formatNum(part.modules.length)} modules`);
  }
  return parts;
};

const insertTree = (tree: Tree, module: string) => {
  let node = tree;
  for (const part of module.split(".")) {
    const name = sanitizeIdent(part);
    const child = node.children.get(name) ?? { name, children: new Map<string, Tree>() };
    node.children.set(name, child);
    node = child;
  }
  node.module = module;
};

const insertDepTree = (tree: Tree, module: string, depCrate: string) => {
  let node = tree;
  for (const part of module.split(".")) {
    const name = sanitizeIdent(part);
    const child = node.children.get(name) ?? { name, children: new Map<string, Tree>() };
    node.children.set(name, child);
    node = child;
  }
  node.depCrate = depCrate;
  node.module = module;
};

const emitTree = (node: Tree, crateDir: string, indent = ""): string[] => {
  const lines: string[] = [];
  for (const [name, child] of [...node.children.entries()].sort(([a], [b]) => a.localeCompare(b))) {
    lines.push(`${indent}pub mod ${name} {`);
    if (child.depCrate && child.module) {
      lines.push(`${indent}    pub use ${child.depCrate}::r#gen::${rustPathForModule(child.module)}::*;`);
    }
    if (child.module && !child.depCrate) {
      if (child.children.size === 0) {
        lines.push(`${indent}    include!(${JSON.stringify(path.join(crateDir, "src/gen", moduleRel(child.module)))});`);
      } else {
        lines.push(`${indent}    pub mod index {`);
        lines.push(`${indent}        include!(${JSON.stringify(path.join(crateDir, "src/gen", moduleRel(child.module)))});`);
        lines.push(`${indent}    }`);
        lines.push(`${indent}    pub use index::*;`);
      }
    }
    lines.push(...emitTree(child, crateDir, `${indent}    `));
    lines.push(`${indent}}`);
  }
  return lines;
};

const writeOnePart = async (part: Part, priorParts: Part[], modules: Map<string, ModuleInfo>) => {
  const crateDir = path.join(rustDir, part.crate);
  await fs.rm(crateDir, { recursive: true, force: true });
  await fs.mkdir(path.join(crateDir, "src/gen"), { recursive: true });

  for (const mod of part.modules) {
    const src = modules.get(mod)!.rustFile;
    const dest = path.join(crateDir, "src/gen", moduleRel(mod));
    await fs.mkdir(path.dirname(dest), { recursive: true });
    await fs.copyFile(src, dest);
  }

  await fs.writeFile(path.join(crateDir, "Cargo.toml"), [
    "[package]",
    `name = ${JSON.stringify(part.crate)}`,
    'version = "0.1.0"',
    'edition = "2024"',
    "publish = false",
    "",
    "[dependencies]",
    'leanh = { path = "../leanh" }',
    'runtime = { path = "../runtime" }',
    'gen_init_ffi = { path = "../gen_init_ffi" }',
    'gen_init = { path = "../gen_init" }',
    'gen_std_ffi = { path = "../gen_std_ffi" }',
    'gen_std = { path = "../gen_std" }',
    'gen_lean_ffi = { path = "../gen_lean_ffi" }',
    ...priorParts.map((dep) => `${dep.crate} = { path = "../${dep.crate}" }`),
    "",
  ].join("\n"));

  const tree: Tree = { name: "", children: new Map() };
  for (const dep of priorParts) {
    for (const mod of dep.modules) insertDepTree(tree, mod, dep.crate);
  }
  for (const mod of part.modules) insertTree(tree, mod);

  await fs.writeFile(path.join(crateDir, "src/lib.rs"), [
    "#![allow(dead_code, non_upper_case_globals, non_snake_case)]",
    "#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports, unsafe_op_in_unsafe_fn)]",
    "",
    "pub mod ffi {",
    "    pub use gen_init_ffi::*;",
    "    pub use gen_std_ffi::*;",
    "    pub use gen_lean_ffi::*;",
    "}",
    "",
    "pub mod r#gen {",
    "    pub use gen_init::r#gen::Init;",
    "    pub use gen_std::r#gen::Std;",
    ...emitTree(tree, crateDir, "    "),
    "}",
    "",
  ].join("\n"));
};

const rewriteWorkspaceMembers = async (parts: Part[]) => {
  const workspacePath = path.join(rustDir, "Cargo.toml");
  let workspace = await fs.readFile(workspacePath, "utf8");
  workspace = workspace.replace(/  "gen_lean_part_\d+",\n/g, "");
  const memberLines = parts.map((part) => `  "${part.crate}",`).join("\n");
  workspace = workspace.replace(/(  "gen_lean",\n)/, `${memberLines}\n$1`);
  await fs.writeFile(workspacePath, workspace);
};

const main = async () => {
  const rustFiles = (await collect(walkFiles(genLeanSrc))).filter((file) => file.endsWith(".rs")).sort();
  const moduleNames = new Set(rustFiles.map(moduleForRustFile));
  const modules = new Map<string, ModuleInfo>();

  for (const rustFile of rustFiles) {
    const module = moduleForRustFile(rustFile);
    const src = await fs.readFile(rustFile, "utf8");
    const deps = dependencyModulesFromRust(src, moduleNames);
    deps.delete(module);
    modules.set(module, {
      module,
      rustFile,
      deps,
      rustLines: await lineCount(rustFile),
    });
  }

  const sccs = tarjan([...modules.keys()].sort(), (mod) => modules.get(mod)!.deps);
  const cyclic = sccs.filter((scc) => scc.length > 1);
  if (cyclic.length > 0) {
    console.error(`found ${formatNum(cyclic.length)} cyclic module components; keeping each component in one crate part`);
  }

  const components = topoComponents(sccs, modules);
  const parts = splitIntoParts(components, modules);

  const oldPartDirs = (await fs.readdir(rustDir, { withFileTypes: true }))
    .filter((e) => e.isDirectory() && /^gen_lean_part_\d+$/.test(e.name))
    .map((e) => path.join(rustDir, e.name));
  await Promise.all(oldPartDirs.map((dir) => fs.rm(dir, { recursive: true, force: true })));

  for (let i = 0; i < parts.length; i += 1) {
    await writeOnePart(parts[i]!, parts.slice(0, i), modules);
  }

  await fs.writeFile(path.join(genLeanCrate, "Cargo.toml"), [
    "[package]",
    'name = "gen_lean"',
    'version = "0.1.0"',
    'edition = "2024"',
    "publish = false",
    "",
    "[dependencies]",
    ...parts.map((part) => `${part.crate} = { path = "../${part.crate}" }`),
    "",
  ].join("\n"));

  const joinTree: Tree = { name: "", children: new Map() };
  for (const part of parts) {
    for (const mod of part.modules) insertDepTree(joinTree, mod, part.crate);
  }

  await fs.writeFile(path.join(genLeanCrate, "src/lib.rs"), [
    "#![allow(dead_code, non_upper_case_globals, non_snake_case)]",
    "#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]",
    "",
    "pub mod r#gen {",
    "    pub use gen_lean_part_5::r#gen::Init;",
    "    pub use gen_lean_part_5::r#gen::Std;",
    ...emitTree(joinTree, genLeanCrate, "    "),
    "}",
    "",
    "pub mod ffi {",
    "    pub use gen_lean_part_5::ffi::*;",
    "}",
    "",
  ].join("\n"));

  await rewriteWorkspaceMembers(parts);
  console.error(`wrote ${PART_COUNT} gen_lean split implementation crates`);
};

main().catch((err) => {
  console.error(String(err?.stack ?? err));
  process.exit(1);
});
