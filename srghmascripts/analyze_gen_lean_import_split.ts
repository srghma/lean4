#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

type ModuleInfo = {
  module: string;
  leanFile: string;
  rustFile: string;
  leanLines: number;
  rustLines: number;
  deps: Set<string>;
};

type GroupInfo = {
  name: string;
  modules: Set<string>;
  leanLines: number;
  rustLines: number;
  deps: Set<string>;
};

type Atom = {
  name: string;
  modules: Set<string>;
};

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const leanRoot = path.join(rootDir, "src/Lean");
const rustGenRoot = path.join(rootDir, "src/rust/gen_lean/src/gen");

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

const moduleForLeanFile = (file: string) => {
  const rel = path.relative(path.join(rootDir, "src"), file).replaceAll(path.sep, "/");
  return rel.replace(/\.lean$/, "").replaceAll("/", ".");
};

const rustFileForModule = (mod: string) =>
  path.join(rustGenRoot, `${mod.replaceAll(".", "/")}.rs`);

const parseImports = (src: string) => {
  const imports = new Set<string>();
  for (const rawLine of src.split("\n")) {
    const line = rawLine.replace(/--.*$/, "").trim();
    const match = line.match(/^(?:(?:public|private|protected|meta|noncomputable|unsafe)\s+)*import\s+(.+)$/);
    if (!match) continue;
    for (const token of match[1]!.trim().split(/\s+/)) {
      if (token.length > 0) imports.add(token);
    }
  }
  return imports;
};

const directoryAtom = (mod: string, moduleHasChildren: Set<string>) => {
  if (moduleHasChildren.has(mod)) return `${mod}.__index`;

  const parts = mod.split(".");
  if (parts[0] !== "Lean") throw new Error(`expected Lean module, got ${mod}`);
  const top = parts[1] ?? "_root";
  const second = parts[2];
  const third = parts[3];

  // Keep known large semantic directories as atoms, but avoid arbitrary topo ranges.
  if (top === "Meta") {
    if (second === "Tactic") {
      if (third === "Grind") return "Lean.Meta.Tactic.Grind";
      if (third === "BVDecide") return "Lean.Meta.Tactic.BVDecide";
      if (third === "Simp") return "Lean.Meta.Tactic.Simp";
      return "Lean.Meta.Tactic";
    }
    if (second === "Sym") return "Lean.Meta.Sym";
    if (second === "Match") return "Lean.Meta.Match";
    if (second === "Constructions") return "Lean.Meta.Constructions";
    return "Lean.Meta";
  }

  if (top === "Elab") {
    if (second === "Tactic") {
      if (third === "Do") return "Lean.Elab.Tactic.Do";
      if (third === "Grind") return "Lean.Elab.Tactic.Grind";
      if (third === "Omega") return "Lean.Elab.Tactic.Omega";
      if (third === "Conv") return "Lean.Elab.Tactic.Conv";
      return "Lean.Elab.Tactic";
    }
    if (second === "PreDefinition") return "Lean.Elab.PreDefinition";
    if (second === "DocString") return "Lean.Elab.DocString";
    if (second === "Deriving") return "Lean.Elab.Deriving";
    if (second === "ConfigEval") return "Lean.Elab.ConfigEval";
    if (second === "BuiltinDo") return "Lean.Elab.BuiltinDo";
    if (second === "Do") return "Lean.Elab.Do";
    return "Lean.Elab";
  }

  if (top === "Compiler") {
    if (second === "LCNF") {
      if (third === "Simp") return "Lean.Compiler.LCNF.Simp";
      return "Lean.Compiler.LCNF";
    }
    if (second === "IR") return "Lean.Compiler.IR";
    return "Lean.Compiler";
  }

  if (top === "Server") return second ? `Lean.Server.${second}` : "Lean.Server";
  if (top === "Data") return second ? `Lean.Data.${second}` : "Lean.Data";
  if (top === "Parser") return second ? `Lean.Parser.${second}` : "Lean.Parser";
  if (top === "PrettyPrinter") return second ? `Lean.PrettyPrinter.${second}` : "Lean.PrettyPrinter";
  if (top === "Linter") return second ? `Lean.Linter.${second}` : "Lean.Linter";
  if (top === "Util") return "Lean.Util";
  if (top === "LibrarySuggestions") return "Lean.LibrarySuggestions";
  return "Lean.Base";
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

  for (const node of nodes) {
    if (!indices.has(node)) strongConnect(node);
  }
  return sccs;
};

const topoComponents = (groups: Map<string, GroupInfo>, sccs: string[][]) => {
  const groupToComponent = new Map<string, number>();
  sccs.forEach((scc, i) => scc.forEach((group) => groupToComponent.set(group, i)));

  const compDeps = sccs.map(() => new Set<number>());
  const reverse = sccs.map(() => new Set<number>());
  for (const [group, info] of groups) {
    const from = groupToComponent.get(group)!;
    for (const dep of info.deps) {
      const to = groupToComponent.get(dep)!;
      if (from === to) continue;
      compDeps[from]!.add(to);
      reverse[to]!.add(from);
    }
  }

  // Edges point group -> dependency. Build earliest-first order by reversing them.
  const indegree = compDeps.map((deps) => deps.size);
  const ready = indegree.map((d, i) => d === 0 ? i : -1).filter((i) => i >= 0);
  const order: number[] = [];
  while (ready.length > 0) {
    ready.sort((a, b) => componentName(sccs[a]!).localeCompare(componentName(sccs[b]!)));
    const cur = ready.shift()!;
    order.push(cur);
    for (const user of reverse[cur]!) {
      indegree[user] -= 1;
      if (indegree[user] === 0) ready.push(user);
    }
  }
  return order.map((i) => sccs[i]!);
};

const componentName = (groups: string[]) => groups.slice().sort().join(" + ");

const formatNum = (n: number) => n.toLocaleString("en-US");

const moduleHasPrefix = (mod: string, prefix: string) =>
  mod === prefix || mod.startsWith(`${prefix}.`);

const initialRecursiveAtom = (mod: string, moduleHasChildren: Set<string>) => {
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
    if (moduleHasChildren.has(mod)) {
      name = `${mod}.__index`;
    } else if (atom.name === "Lean.Base") {
      name = mod.split(".").length <= 2 ? mod : mod.split(".").slice(0, 2).join(".");
    } else if (!moduleHasPrefix(mod, baseName)) {
      name = mod;
    } else {
      const parts = mod.split(".");
      name = parts.length <= baseParts.length + 1
        ? mod
        : parts.slice(0, baseParts.length + 1).join(".");
    }
    const next = out.get(name) ?? { name, modules: new Set<string>() };
    next.modules.add(mod);
    out.set(name, next);
  }
  return [...out.values()];
};

const buildGroupsFromAtoms = (atoms: Atom[], modules: Map<string, ModuleInfo>, moduleToAtom: Map<string, string>) => {
  const groups = new Map<string, GroupInfo>();
  for (const atom of atoms) {
    const group: GroupInfo = {
      name: atom.name,
      modules: new Set(atom.modules),
      leanLines: 0,
      rustLines: 0,
      deps: new Set<string>(),
    };
    for (const mod of atom.modules) {
      const info = modules.get(mod)!;
      group.leanLines += info.leanLines;
      group.rustLines += info.rustLines;
      moduleToAtom.set(mod, atom.name);
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
  return groups;
};

const refineDirectoryAtoms = (
  modules: Map<string, ModuleInfo>,
  moduleHasChildren: Set<string>,
  maxCyclicRustLines: number,
) => {
  const initial = new Map<string, Atom>();
  for (const mod of modules.keys()) {
    const name = initialRecursiveAtom(mod, moduleHasChildren);
    const atom = initial.get(name) ?? { name, modules: new Set<string>() };
    atom.modules.add(mod);
    initial.set(name, atom);
  }

  let atoms = [...initial.values()];
  for (let round = 0; round < 20; round += 1) {
    const moduleToAtom = new Map<string, string>();
    const groups = buildGroupsFromAtoms(atoms, modules, moduleToAtom);
    const sccs = tarjan([...groups.keys()].sort(), (group) => groups.get(group)!.deps);
    const cyclic = sccs.filter((scc) => scc.length > 1);
    const toRefine = new Set<string>();
    for (const scc of cyclic) {
      const rustLines = scc.reduce((sum, group) => sum + groups.get(group)!.rustLines, 0);
      if (rustLines <= maxCyclicRustLines) continue;
      for (const group of scc) {
        if (groups.get(group)!.modules.size > 1) toRefine.add(group);
      }
    }
    if (toRefine.size === 0) return { atoms, groups, sccs, rounds: round };

    const nextAtoms: Atom[] = [];
    for (const atom of atoms) {
      if (toRefine.has(atom.name)) nextAtoms.push(...splitAtomOneLevel(atom, moduleHasChildren));
      else nextAtoms.push(atom);
    }
    atoms = nextAtoms;
  }

  const moduleToAtom = new Map<string, string>();
  const groups = buildGroupsFromAtoms(atoms, modules, moduleToAtom);
  const sccs = tarjan([...groups.keys()].sort(), (group) => groups.get(group)!.deps);
  return { atoms, groups, sccs, rounds: 20 };
};

const main = async () => {
  const leanFiles = (await collect(walkFiles(leanRoot)))
    .filter((file) => file.endsWith(".lean"))
    .sort();

  const modules = new Map<string, ModuleInfo>();
  for (const leanFile of leanFiles) {
    const mod = moduleForLeanFile(leanFile);
    const rustFile = rustFileForModule(mod);
    const src = await fs.readFile(leanFile, "utf8");
    modules.set(mod, {
      module: mod,
      leanFile,
      rustFile,
      leanLines: await lineCount(leanFile),
      rustLines: await lineCount(rustFile),
      deps: parseImports(src),
    });
  }

  for (const info of modules.values()) {
    info.deps = new Set([...info.deps].filter((dep) => modules.has(dep)));
  }

  const moduleSccs = tarjan([...modules.keys()], (mod) => modules.get(mod)!.deps);
  const cyclicModuleSccs = moduleSccs.filter((scc) => scc.length > 1);

  const groups = new Map<string, GroupInfo>();
  const moduleToGroup = new Map<string, string>();
  const moduleHasChildren = new Set<string>();
  for (const mod of modules.keys()) {
    for (const other of modules.keys()) {
      if (other.startsWith(`${mod}.`)) {
        moduleHasChildren.add(mod);
        break;
      }
    }
  }

  for (const info of modules.values()) {
    const group = directoryAtom(info.module, moduleHasChildren);
    moduleToGroup.set(info.module, group);
    const groupInfo = groups.get(group) ?? {
      name: group,
      modules: new Set<string>(),
      leanLines: 0,
      rustLines: 0,
      deps: new Set<string>(),
    };
    groupInfo.modules.add(info.module);
    groupInfo.leanLines += info.leanLines;
    groupInfo.rustLines += info.rustLines;
    groups.set(group, groupInfo);
  }

  for (const info of modules.values()) {
    const group = groups.get(moduleToGroup.get(info.module)!)!;
    for (const dep of info.deps) {
      const depGroup = moduleToGroup.get(dep)!;
      if (depGroup !== group.name) group.deps.add(depGroup);
    }
  }

  const groupNames = [...groups.keys()].sort();
  const groupSccs = tarjan(groupNames, (group) => groups.get(group)!.deps);
  const cyclicGroupSccs = groupSccs.filter((scc) => scc.length > 1);
  const proposal = topoComponents(groups, groupSccs);

  const lines: string[] = [];
  lines.push("# gen_lean Import Split Analysis");
  lines.push("");
  lines.push(`Modules: ${formatNum(modules.size)}`);
  lines.push(`Directory atoms: ${formatNum(groups.size)}`);
  lines.push(`Module SCCs: ${formatNum(moduleSccs.length)} total, ${formatNum(cyclicModuleSccs.length)} cyclic`);
  lines.push(`Directory-atom SCCs: ${formatNum(groupSccs.length)} total, ${formatNum(cyclicGroupSccs.length)} cyclic`);
  lines.push("");
  lines.push("## Directory Atom Sizes");
  lines.push("");
  lines.push("| Atom | Modules | Lean LOC | Generated Rust LOC | Direct atom deps |");
  lines.push("|---|---:|---:|---:|---:|");
  for (const group of [...groups.values()].sort((a, b) => b.rustLines - a.rustLines)) {
    lines.push(`| ${group.name} | ${formatNum(group.modules.size)} | ${formatNum(group.leanLines)} | ${formatNum(group.rustLines)} | ${formatNum(group.deps.size)} |`);
  }
  lines.push("");
  lines.push("## Cyclic Directory Atom Components");
  lines.push("");
  if (cyclicGroupSccs.length === 0) {
    lines.push("No directory-atom cycles.");
  } else {
    for (const scc of cyclicGroupSccs.sort((a, b) => b.length - a.length)) {
      const rustLines = scc.reduce((sum, group) => sum + groups.get(group)!.rustLines, 0);
      lines.push(`- ${componentName(scc)} (${scc.length} atoms, ${formatNum(rustLines)} generated Rust LOC)`);
    }
  }
  lines.push("");
  lines.push("## Semi-Topological Proposal");
  lines.push("");
  lines.push("Each row is a crate candidate. A row may contain multiple directory atoms only when the atom graph has a cycle that requires merging them.");
  lines.push("");
  lines.push("| Order | Crate candidate | Atoms | Modules | Generated Rust LOC |");
  lines.push("|---:|---|---|---:|---:|");
  proposal.forEach((component, i) => {
    const modulesCount = component.reduce((sum, group) => sum + groups.get(group)!.modules.size, 0);
    const rustLines = component.reduce((sum, group) => sum + groups.get(group)!.rustLines, 0);
    const crate = `gen_lean_part_${String(i + 1).padStart(2, "0")}`;
    lines.push(`| ${i + 1} | ${crate} | ${componentName(component)} | ${formatNum(modulesCount)} | ${formatNum(rustLines)} |`);
  });
  lines.push("");
  lines.push("## Notes");
  lines.push("");
  lines.push("- This is semi-topological: it preserves directory atoms first, then uses the import graph only to order or merge atoms.");
  lines.push("- `.__index` atoms are umbrella modules such as `Lean.Meta.lean` next to `Lean/Meta/`; these should usually live in late facade crates.");
  lines.push("- Crates should be generated in the listed order. Later crates may depend on earlier crates.");
  lines.push("- Any row with multiple atoms is a required merge under the current atom policy because Cargo cannot represent cycles.");

  const refined = refineDirectoryAtoms(modules, moduleHasChildren, 1_500_000);
  const refinedCyclic = refined.sccs.filter((scc) => scc.length > 1);
  const refinedProposal = topoComponents(refined.groups, refined.sccs);
  lines.push("");
  lines.push("## Recursive Directory Refinement");
  lines.push("");
  lines.push("This section starts from real directories, then refines only directory atoms participating in oversized cyclic components. It keeps path prefixes intact and uses individual modules only where directory grouping creates Cargo cycles.");
  lines.push("");
  lines.push(`Refinement rounds: ${refined.rounds}`);
  lines.push(`Refined atoms: ${formatNum(refined.groups.size)}`);
  lines.push(`Refined cyclic components: ${formatNum(refinedCyclic.length)}`);
  if (refinedCyclic.length > 0) {
    for (const scc of refinedCyclic.sort((a, b) => b.length - a.length).slice(0, 10)) {
      const rustLines = scc.reduce((sum, group) => sum + refined.groups.get(group)!.rustLines, 0);
      lines.push(`- remaining cycle: ${componentName(scc)} (${scc.length} atoms, ${formatNum(rustLines)} generated Rust LOC)`);
    }
  }
  lines.push("");
  lines.push("Largest refined atoms:");
  lines.push("");
  lines.push("| Atom | Modules | Generated Rust LOC |");
  lines.push("|---|---:|---:|");
  for (const group of [...refined.groups.values()].sort((a, b) => b.rustLines - a.rustLines).slice(0, 40)) {
    lines.push(`| ${group.name} | ${formatNum(group.modules.size)} | ${formatNum(group.rustLines)} |`);
  }
  lines.push("");
  lines.push("Refined semi-topological crate candidates over 250k generated Rust LOC:");
  lines.push("");
  lines.push("| Order | Candidate | Atoms | Modules | Generated Rust LOC |");
  lines.push("|---:|---|---|---:|---:|");
  refinedProposal.forEach((component, i) => {
    const modulesCount = component.reduce((sum, group) => sum + refined.groups.get(group)!.modules.size, 0);
    const rustLines = component.reduce((sum, group) => sum + refined.groups.get(group)!.rustLines, 0);
    if (rustLines < 250_000) return;
    lines.push(`| ${i + 1} | gen_lean_part_${String(i + 1).padStart(2, "0")} | ${componentName(component)} | ${formatNum(modulesCount)} | ${formatNum(rustLines)} |`);
  });

  const out = path.join(rootDir, "src/rust/gen_lean/import-split-analysis.md");
  await fs.mkdir(path.dirname(out), { recursive: true });
  await fs.writeFile(out, `${lines.join("\n")}\n`);
  console.log(lines.join("\n"));
  console.error(`wrote ${path.relative(rootDir, out)}`);
};

main().catch((err) => {
  console.error(String(err?.stack ?? err));
  process.exit(1);
});
