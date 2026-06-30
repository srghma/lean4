#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";
import { leanSplitCrateForRel, leanSplitCrates, type LeanSplitCrate } from "./gen_lean_split_common";

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const genLeanRoot = path.join(rootDir, "src/rust/gen_lean/src/gen");

type Edge = {
  from: LeanSplitCrate;
  to: LeanSplitCrate;
  file: string;
  importPath: string;
};

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

const importRe = /crate::r#gen::Lean::([A-Za-z0-9_]+)(?:::([A-Za-z0-9_]+))?(?:::([A-Za-z0-9_]+))?/g;

const relForImport = (match: RegExpExecArray) => {
  const [, top, second, third] = match;
  return ["Lean", top, second, third].filter(Boolean).join("/") + ".rs";
};

const edges: Edge[] = [];

for await (const file of walkFiles(genLeanRoot)) {
  if (!file.endsWith(".rs")) continue;
  const rel = path.relative(genLeanRoot, file).replaceAll(path.sep, "/");
  if (!rel.startsWith("Lean")) continue;
  const from = leanSplitCrateForRel(rel);
  const src = await fs.readFile(file, "utf8");
  for (const match of src.matchAll(importRe)) {
    const importRel = relForImport(match);
    const to = leanSplitCrateForRel(importRel);
    if (from !== to) {
      edges.push({ from, to, file: rel, importPath: match[0] });
    }
  }
}

const edgeKey = (edge: Pick<Edge, "from" | "to">) => `${edge.from}->${edge.to}`;
const firstByEdge = new Map<string, Edge>();
for (const edge of edges) {
  const key = edgeKey(edge);
  if (!firstByEdge.has(key)) firstByEdge.set(key, edge);
}

const graph = new Map<LeanSplitCrate, Set<LeanSplitCrate>>();
for (const crate of leanSplitCrates) graph.set(crate, new Set());
for (const edge of edges) graph.get(edge.from)!.add(edge.to);

let index = 0;
const stack: LeanSplitCrate[] = [];
const onStack = new Set<LeanSplitCrate>();
const indices = new Map<LeanSplitCrate, number>();
const lowlinks = new Map<LeanSplitCrate, number>();
const sccs: LeanSplitCrate[][] = [];

const strongConnect = (v: LeanSplitCrate) => {
  indices.set(v, index);
  lowlinks.set(v, index);
  index += 1;
  stack.push(v);
  onStack.add(v);

  for (const w of graph.get(v) ?? []) {
    if (!indices.has(w)) {
      strongConnect(w);
      lowlinks.set(v, Math.min(lowlinks.get(v)!, lowlinks.get(w)!));
    } else if (onStack.has(w)) {
      lowlinks.set(v, Math.min(lowlinks.get(v)!, indices.get(w)!));
    }
  }

  if (lowlinks.get(v) === indices.get(v)) {
    const component: LeanSplitCrate[] = [];
    while (true) {
      const w = stack.pop()!;
      onStack.delete(w);
      component.push(w);
      if (w === v) break;
    }
    sccs.push(component);
  }
};

for (const crate of leanSplitCrates) {
  if (!indices.has(crate)) strongConnect(crate);
}

console.log("gen_lean proposed crate dependency edges:");
for (const edge of [...firstByEdge.values()].sort((a, b) => edgeKey(a).localeCompare(edgeKey(b)))) {
  console.log(`- ${edge.from} -> ${edge.to}`);
  console.log(`  example: ${edge.file}: ${edge.importPath}`);
}

const cyclic = sccs.filter((scc) => scc.length > 1);
if (cyclic.length > 0) {
  console.log("");
  console.log("cyclic components:");
  for (const scc of cyclic) console.log(`- ${scc.sort().join(", ")}`);
  if (process.argv.includes("--fail-on-cycle")) process.exit(1);
} else {
  console.log("");
  console.log("no crate-level cycles found");
}
