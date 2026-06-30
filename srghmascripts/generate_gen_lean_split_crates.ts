#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

type ModuleInfo = {
  module: string;
  rustFile: string;
  deps: Set<string>;
};

type Atom = {
  name: string;
  modules: Set<string>;
};

type GroupInfo = {
  name: string;
  modules: Set<string>;
  deps: Set<string>;
  rustLines: number;
};

type Part = {
  crate: string;
  groups: string[];
  modules: string[];
  deps: Set<number>;
};

type Tree = {
  name: string;
  children: Map<string, Tree>;
  module?: string;
  depCrate?: string;
};

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const rustDir = path.join(rootDir, "src/rust");
const leanRoot = path.join(rootDir, "src/Lean");
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

const moduleForLeanFile = (file: string) =>
  "Lean." + path.relative(leanRoot, file).replace(/\.lean$/, "").replaceAll(path.sep, ".");

const rustFileForModule = (mod: string) => path.join(genLeanSrc, `${mod.replaceAll(".", "/")}.rs`);

const parseImports = (src: string) => {
  const imports = new Set<string>();
  for (const rawLine of src.split("\n")) {
    const line = rawLine.replace(/--.*$/, "").trim();
    const match = line.match(/^(?:(?:public|private|protected|meta|noncomputable|unsafe)\s+)*import\s+(.+)$/);
    if (!match) continue;
    for (const token of match[1]!.trim().split(/\s+/)) {
      if (token.startsWith("Lean.")) imports.add(token);
    }
  }
  return imports;
};

const moduleHasPrefix = (mod: string, prefix: string) => mod === prefix || mod.startsWith(`${prefix}.`);

const initialAtom = (mod: string, moduleHasChildren: Set<string>) => {
  if (moduleHasChildren.has(mod)) return `${mod}.__index`;
  const parts = mod.split(".");
  if (parts.length <= 2) return "Lean.Base";
  return parts.slice(0, 2).join(".");
};

const splitAtomOneLevel = (atom: Atom, moduleHasChildren: Set<string>) => {
  const out = new Map<string, Atom>();
  const baseName = atom.name.replace(/\.__index$/, "");
  const baseParts = baseName === "Lean.Base" ? ["Lean"] : baseName.split(".");
  for (const mod of atom.modules) {
    let name: string;
    if (moduleHasChildren.has(mod)) name = `${mod}.__index`;
    else if (atom.name === "Lean.Base") name = mod.split(".").length <= 2 ? mod : mod.split(".").slice(0, 2).join(".");
    else if (!moduleHasPrefix(mod, baseName)) name = mod;
    else {
      const parts = mod.split(".");
      name = parts.length <= baseParts.length + 1 ? mod : parts.slice(0, baseParts.length + 1).join(".");
    }
    const next = out.get(name) ?? { name, modules: new Set<string>() };
    next.modules.add(mod);
    out.set(name, next);
  }
  return [...out.values()];
};

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

const buildGroups = async (atoms: Atom[], modules: Map<string, ModuleInfo>) => {
  const moduleToAtom = new Map<string, string>();
  const groups = new Map<string, GroupInfo>();
  for (const atom of atoms) {
    const group: GroupInfo = { name: atom.name, modules: new Set(atom.modules), deps: new Set(), rustLines: 0 };
    for (const mod of atom.modules) {
      moduleToAtom.set(mod, atom.name);
      group.rustLines += await lineCount(modules.get(mod)!.rustFile);
    }
    groups.set(atom.name, group);
  }
  for (const atom of atoms) {
    const group = groups.get(atom.name)!;
    for (const mod of atom.modules) {
      for (const dep of modules.get(mod)!.deps) {
        const depGroup = moduleToAtom.get(dep)!;
        if (depGroup !== group.name) group.deps.add(depGroup);
      }
    }
  }
  return { groups, moduleToAtom };
};

const refineAtoms = async (modules: Map<string, ModuleInfo>, moduleHasChildren: Set<string>) => {
  const initial = new Map<string, Atom>();
  for (const mod of modules.keys()) {
    const name = initialAtom(mod, moduleHasChildren);
    const atom = initial.get(name) ?? { name, modules: new Set<string>() };
    atom.modules.add(mod);
    initial.set(name, atom);
  }
  let atoms = [...initial.values()];
  for (let round = 0; round < 20; round += 1) {
    const { groups } = await buildGroups(atoms, modules);
    const sccs = tarjan([...groups.keys()].sort(), (group) => groups.get(group)!.deps);
    const toRefine = new Set<string>();
    for (const scc of sccs.filter((scc) => scc.length > 1)) {
      const rustLines = scc.reduce((sum, group) => sum + groups.get(group)!.rustLines, 0);
      if (rustLines <= 1_500_000) continue;
      for (const group of scc) if (groups.get(group)!.modules.size > 1) toRefine.add(group);
    }
    if (toRefine.size === 0) return atoms;
    atoms = atoms.flatMap((atom) => toRefine.has(atom.name) ? splitAtomOneLevel(atom, moduleHasChildren) : [atom]);
  }
  return atoms;
};

const topoParts = (parts: Part[]) => {
  const reverse = parts.map(() => new Set<number>());
  const indegree = parts.map((p) => p.deps.size);
  parts.forEach((p, i) => p.deps.forEach((dep) => reverse[dep]!.add(i)));
  const ready = indegree.map((d, i) => d === 0 ? i : -1).filter((i) => i >= 0);
  const order: number[] = [];
  while (ready.length > 0) {
    ready.sort((a, b) => parts[a]!.crate.localeCompare(parts[b]!.crate));
    const cur = ready.shift()!;
    order.push(cur);
    for (const user of reverse[cur]!) {
      indegree[user] -= 1;
      if (indegree[user] === 0) ready.push(user);
    }
  }
  if (order.length !== parts.length) throw new Error("part dependency graph has a cycle");
  return order.map((i) => parts[i]!);
};

const sanitizeIdent = (name: string) => {
  const stem = name.replace(/\.rs$/, "");
  return ["gen", "loop", "type"].includes(stem) ? `r#${stem}` : stem;
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

const moduleRel = (mod: string) => `${mod.replaceAll(".", "/")}.rs`;

const rustPathForModule = (mod: string) => mod.split(".").map(sanitizeIdent).join("::");

const emitOwnTree = (node: Tree, crateDir: string, indent = ""): string[] => {
  const lines: string[] = [];
  for (const [name, child] of [...node.children.entries()].sort(([a], [b]) => a.localeCompare(b))) {
    if (child.children.size === 0) {
      lines.push(`${indent}pub mod ${name} {`);
      if (child.depCrate && child.module) {
        lines.push(`${indent}    pub use ${child.depCrate}::r#gen::${rustPathForModule(child.module)}::*;`);
      }
      if (child.module && !child.depCrate) {
        lines.push(`${indent}    include!(${JSON.stringify(path.join(crateDir, "src/gen", moduleRel(child.module)))});`);
      }
      lines.push(`${indent}}`);
      continue;
    }
    lines.push(`${indent}pub mod ${name} {`);
    if (child.depCrate && child.module) {
      lines.push(`${indent}    pub use ${child.depCrate}::r#gen::${rustPathForModule(child.module)}::*;`);
    }
    if (child.module && !child.depCrate) {
      lines.push(`${indent}    pub mod index {`);
      lines.push(`${indent}        include!(${JSON.stringify(path.join(crateDir, "src/gen", moduleRel(child.module)))});`);
      lines.push(`${indent}    }`);
      lines.push(`${indent}    pub use index::*;`);
    }
    lines.push(...emitOwnTree(child, crateDir, `${indent}    `));
    lines.push(`${indent}}`);
  }
  return lines;
};

const writeOnePart = async (part: Part, orderedParts: Part[], partByModule: Map<string, number>, modules: Map<string, ModuleInfo>) => {
  const crateDir = path.join(rustDir, part.crate);
  await fs.rm(crateDir, { recursive: true, force: true });
  await fs.mkdir(path.join(crateDir, "src/gen"), { recursive: true });
  for (const mod of part.modules) {
    const src = modules.get(mod)!.rustFile;
    const dest = path.join(crateDir, "src/gen", moduleRel(mod));
    await fs.mkdir(path.dirname(dest), { recursive: true });
    await fs.copyFile(src, dest);
  }
  const depCrates = [...part.deps].sort((a, b) => a - b).map((i) => orderedParts[i]!.crate);
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
    'gen_std_ffi = { path = "../gen_std_ffi" }',
    'gen_lean_base_ffi = { path = "../gen_lean_base_ffi" }',
    'gen_lean_meta_ffi = { path = "../gen_lean_meta_ffi" }',
    'gen_lean_meta_tactic_ffi = { path = "../gen_lean_meta_tactic_ffi" }',
    'gen_lean_meta_grind_ffi = { path = "../gen_lean_meta_grind_ffi" }',
    'gen_lean_compiler_ffi = { path = "../gen_lean_compiler_ffi" }',
    'gen_lean_elab_tactic_ffi = { path = "../gen_lean_elab_tactic_ffi" }',
    "gen_init = { path = \"../gen_init\" }",
    "gen_std = { path = \"../gen_std\" }",
    ...depCrates.map((crate) => `${crate} = { path = "../${crate}" }`),
    "",
  ].join("\n"));

  const ownTree: Tree = { name: "", children: new Map() };
  for (const depIndex of part.deps) {
    const depCrate = orderedParts[depIndex]!.crate;
    for (const mod of orderedParts[depIndex]!.modules) insertDepTree(ownTree, mod, depCrate);
  }
  for (const mod of part.modules) insertTree(ownTree, mod);

  // Cheap dependency namespace: each earlier part exports a complete r#gen tree,
  // and explicit local modules below shadow any duplicate glob names.
  const lib = [
    "#![allow(dead_code, non_upper_case_globals, non_snake_case)]",
    "#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports, unsafe_op_in_unsafe_fn)]",
    "",
    "pub mod ffi {",
    "    pub use gen_init_ffi::*;",
    "    pub use gen_std_ffi::*;",
    "    pub use gen_lean_base_ffi::*;",
    "    pub use gen_lean_compiler_ffi::*;",
    "    pub use gen_lean_elab_tactic_ffi::*;",
    "    pub use gen_lean_meta_ffi::*;",
    "    pub use gen_lean_meta_grind_ffi::*;",
    "    pub use gen_lean_meta_tactic_ffi::*;",
    "}",
    "",
    "pub mod r#gen {",
    "    pub use gen_init::r#gen::Init;",
    "    pub use gen_std::r#gen::Std;",
    ...emitOwnTree(ownTree, crateDir, "    "),
    "}",
    "",
  ].join("\n");
  await fs.writeFile(path.join(crateDir, "src/lib.rs"), lib);
};

const main = async () => {
  const leanFiles = (await collect(walkFiles(leanRoot))).filter((f) => f.endsWith(".lean")).sort();
  const modules = new Map<string, ModuleInfo>();
  for (const leanFile of leanFiles) {
    const mod = moduleForLeanFile(leanFile);
    modules.set(mod, {
      module: mod,
      rustFile: rustFileForModule(mod),
      deps: parseImports(await fs.readFile(leanFile, "utf8")),
    });
  }
  for (const info of modules.values()) info.deps = new Set([...info.deps].filter((dep) => modules.has(dep)));

  const moduleHasChildren = new Set<string>();
  for (const mod of modules.keys()) {
    for (const other of modules.keys()) {
      if (other.startsWith(`${mod}.`)) {
        moduleHasChildren.add(mod);
        break;
      }
    }
  }

  const atoms = await refineAtoms(modules, moduleHasChildren);
  const { groups, moduleToAtom } = await buildGroups(atoms, modules);
  const sccs = tarjan([...groups.keys()].sort(), (group) => groups.get(group)!.deps);
  const groupToComponent = new Map<string, number>();
  sccs.forEach((scc, i) => scc.forEach((group) => groupToComponent.set(group, i)));

  let parts: Part[] = sccs.map((groupsInPart, i) => {
    const moduleSet = new Set<string>();
    for (const group of groupsInPart) for (const mod of groups.get(group)!.modules) moduleSet.add(mod);
    return {
      crate: `gen_lean_part_${String(i + 1).padStart(3, "0")}`,
      groups: groupsInPart.sort(),
      modules: [...moduleSet].sort(),
      deps: new Set<number>(),
    };
  });
  for (const [group, info] of groups) {
    const from = groupToComponent.get(group)!;
    for (const dep of info.deps) {
      const to = groupToComponent.get(dep)!;
      if (from !== to) parts[from]!.deps.add(to);
    }
  }
  parts = topoParts(parts);
  parts.forEach((part, i) => part.crate = `gen_lean_part_${String(i + 1).padStart(3, "0")}`);
  const oldIndexByNewIndex = new Map<Part, number>();
  parts.forEach((p, i) => oldIndexByNewIndex.set(p, i));
  const partByModule = new Map<string, number>();
  parts.forEach((part, i) => part.modules.forEach((mod) => partByModule.set(mod, i)));
  // Recompute deps after renumbering/order.
  parts.forEach((part) => part.deps.clear());
  for (const [mod, info] of modules) {
    const from = partByModule.get(mod)!;
    for (const dep of info.deps) {
      const to = partByModule.get(dep)!;
      if (from !== to) parts[from]!.deps.add(to);
    }
  }
  const closure = (index: number, seen = new Set<number>()) => {
    for (const dep of parts[index]!.deps) {
      if (seen.has(dep)) continue;
      seen.add(dep);
      closure(dep, seen);
    }
    return seen;
  };
  parts.forEach((part, i) => {
    part.deps = closure(i);
  });

  const oldPartDirs = (await fs.readdir(rustDir, { withFileTypes: true }))
    .filter((e) => e.isDirectory() && /^gen_lean_part_\d+$/.test(e.name))
    .map((e) => path.join(rustDir, e.name));
  await Promise.all(oldPartDirs.map((dir) => fs.rm(dir, { recursive: true, force: true })));
  for (const part of parts) await writeOnePart(part, parts, partByModule, modules);

  const genLeanCargo = [
    "[package]",
    'name = "gen_lean"',
    'version = "0.1.0"',
    'edition = "2024"',
    "publish = false",
    "",
    "[dependencies]",
    ...parts.map((part) => `${part.crate} = { path = "../${part.crate}" }`),
    "",
  ].join("\n");
  await fs.writeFile(path.join(genLeanCrate, "Cargo.toml"), genLeanCargo);
  await fs.writeFile(path.join(genLeanCrate, "src/lib.rs"), [
    "#![allow(dead_code, non_upper_case_globals, non_snake_case)]",
    "#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]",
    "",
    "pub mod r#gen {",
    ...parts.map((part) => `    pub use ${part.crate}::r#gen::*;`),
    "}",
    "",
    "pub mod ffi {",
    ...parts.map((part) => `    pub use ${part.crate}::ffi::*;`),
    "}",
    "",
  ].join("\n"));

  let workspace = await fs.readFile(path.join(rustDir, "Cargo.toml"), "utf8");
  workspace = workspace.replace(/  "gen_lean_part_\d+",\n/g, "");
  const memberLines = parts.map((part) => `  "${part.crate}",`).join("\n");
  workspace = workspace.replace(/(  "gen_lean",\n)/, `${memberLines}\n$1`);
  await fs.writeFile(path.join(rustDir, "Cargo.toml"), workspace);
  console.error(`wrote ${parts.length} gen_lean split implementation crates`);
};

main().catch((err) => {
  console.error(String(err?.stack ?? err));
  process.exit(1);
});
