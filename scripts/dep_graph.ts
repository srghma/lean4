#!/usr/bin/env bun
/**
 * dep_graph.ts — generate a Graphviz DOT file + order_of_review.md
 *
 *   1. Rust crate/module graph (src/rust/**)
 *   2. C++ file graph (src/removed_cpp/**)
 *
 * Usage:
 *   bun scripts/dep_graph.ts [--rust-only | --cpp-only] [--out graph.dot]
 *   dot -Tsvg graph.dot -o graph.svg
 */

import {
  readdirSync, readFileSync, statSync, writeFileSync, existsSync, realpathSync,
} from "fs";
import { join, relative, extname, basename, dirname } from "path";
import { execSync } from "child_process";

// ─── Branded types ───────────────────────────────────────────────────────────

type Ext = ".cpp" | ".h" | ".hpp";
type AbsPath = string & { readonly _brand: "AbsPath" };
type RelPath = string & { readonly _brand: "RelPath" };
/** Absolute path with no file extension — the canonical identity for a C++ pair. */
type Stem = string & { readonly _brand: "Stem" };

interface FilePair {
  readonly stem: Stem;
  readonly name: RelPath;   // relative to CPP_ROOT, no extension
  readonly h?: RelPath;
  readonly cpp?: RelPath;
}

// ─── Rose tree ───────────────────────────────────────────────────────────────
//
// This is the canonical data structure that drives BOTH the DOT output and the
// Markdown output.  Building from a rose tree guarantees that depth in the
// rendered Markdown is always exactly parentDepth+1, so MD007 can never fire.
//
//   data TaskTree = Node { pair :: FilePair, children :: [TaskTree] }

interface TaskTree {
  readonly pair: FilePair;
  readonly children: TaskTree[];
}

// ─── CLI ─────────────────────────────────────────────────────────────────────

const args = process.argv.slice(2);
const rustOnly = args.includes("--rust-only");
const cppOnly = args.includes("--cpp-only");
const outIdx = args.indexOf("--out");
const outFile = outIdx !== -1 ? args[outIdx + 1] : "dep_graph.dot";

const ROOT = join(import.meta.dir, "..");
const RUST_ROOT = join(ROOT, "src/rust") as AbsPath;
const CPP_ROOT = join(ROOT, "src/removed_cpp") as AbsPath;
const CPP_INCLUDE_ROOT = join(CPP_ROOT, "include") as AbsPath;

// ─── Known external dependency groups ────────────────────────────────────────

const KNOWN_EXTERNALS: ReadonlyArray<readonly [string, RegExp[]]> = [
  ["cadical", [/cadical/i]],
  ["mimalloc", [/mimalloc/i]],
  ["libuv", [/libuv\.h|uv\.h/i]],
  ["ICU (<icu.h>)", [/icu\.h|unicode\//i]],
  ["emscripten", [/emscripten\.h|emscripten\//i]],
  ["<windows.h>", [/windows\.h|psapi\.h|ntdef\.h|bcrypt\.h|io\.h|tchar\.h|strsafe\.h/i]],
  ["<pthread.h>", [/pthread\.h/i]],
  ["<unistd.h>", [/\bunistd\.h\b/]],
  ["<dlfcn.h>", [/dlfcn\.h/i]],
  ["<dirent.h>", [/dirent\.h/i]],
  ["<link.h>", [/\blink\.h\b/]],
  ["<execinfo.h>", [/execinfo\.h/i]],
  ["<sys/mman.h>", [/sys\/mman\.h/i]],
  ["<sys/stat.h>", [/sys\/stat\.h|sys\/types\.h|sys\/wait\.h|sys\/syscall\.h|sys\/resource\.h|sys\/time\.h|sys\/random\.h|sys\/file\.h/i]],
  ["<mach-o/dyld.h>", [/mach-o\/dyld\.h|mach-o\/getsect\.h|mach\/mach\.h/i]],
  ["<sanitizer>", [/sanitizer\/lsan_interface\.h/i]],
  ["<jemalloc>", [/jemalloc\/jemalloc\.h/i]],
  ["LLVM", [/llvm-c\/Core\.h|llvm\.h|llvm-c\//i]],
  ["libc", [/^use libc\b|libc::/m]],
  ["libuv-sys2", [/^use libuv_sys2\b|libuv_sys2::/m]],
] as const;

// ─── File system utilities ────────────────────────────────────────────────────

const statSafe = (p: string) => { try { return statSync(p); } catch { return null; } };
const isFile = (p: string): boolean => statSafe(p)?.isFile() ?? false;
const isDir = (p: string): boolean => statSafe(p)?.isDirectory() ?? false;

const walkDir = (dir: string, exts: readonly string[]): AbsPath[] =>
  !isDir(dir) ? [] :
    readdirSync(dir, { withFileTypes: true })
      .sort((a, b) => a.name.localeCompare(b.name))
      .flatMap(entry => {
        if (entry.name.startsWith(".")) return [];
        const full = join(dir, entry.name);
        return entry.isDirectory()
          ? walkDir(full, exts)
          : exts.includes(extname(entry.name)) ? [full as AbsPath] : [];
      });

const fileStem = (absFile: string): Stem =>
  join(dirname(absFile), basename(absFile, extname(absFile))) as Stem;

const nodeId = (path: string) => relative(ROOT, path).replace(/[^a-zA-Z0-9_]/g, "_");
const shortLabel = (path: string) => relative(ROOT, path);

// ─── Review-status check ─────────────────────────────────────────────────────

const isReviewed = (srcPath: string): boolean => {
  const mdPath = srcPath.replace(/\.(cpp|h|hpp)$/, ".md");
  if (!existsSync(mdPath)) return false;
  const text = readFileSync(mdPath, "utf8");
  return !/^\s*-\s*\[\s*\]/m.test(text) && !/\bTODO\b/i.test(text);
};

// ─── C++ dependency graph ─────────────────────────────────────────────────────

const STD_HEADERS = new Set([
  "string", "vector", "map", "set", "memory", "algorithm", "iostream", "sstream",
  "cstdlib", "cstdio", "cstdint", "cstring", "new", "utility", "functional",
  "thread", "mutex", "condition_variable", "atomic", "chrono", "cassert", "cmath",
  "climits", "csignal", "cerrno", "cwchar", "cwctype", "locale", "bitset",
  "initializer_list", "typeinfo", "numeric", "iterator", "type_traits", "tuple",
  "array", "deque", "forward_list", "list", "queue", "stack", "unordered_map",
  "unordered_set", "ios", "system_error", "iomanip", "fstream",
]);

const realpathSafe = (p: string): string => {
  try { return realpathSync(p); } catch { return p; }
};

const buildCppDeps = (
  cppFiles: ReadonlyArray<AbsPath>,
): {
  allStems: ReadonlySet<Stem>;
  stemDepsOn: ReadonlyMap<Stem, ReadonlySet<Stem>>;
  dotEdges: ReadonlyArray<readonly [string, string, Record<string, string>]>;
  dotMissing: ReadonlyArray<readonly [string, string, string]>;
  externalEdges: ReadonlyArray<readonly [string, string]>;
} => {
  const resolvedToStem = new Map<string, Stem>();
  for (const f of cppFiles) {
    const s = fileStem(f);
    resolvedToStem.set(f, s);
    resolvedToStem.set(realpathSafe(f), s);
    resolvedToStem.set(fileStem(f), s);
    resolvedToStem.set(realpathSafe(fileStem(f) + extname(f)), s);
  }

  const allStems = new Set<Stem>(cppFiles.map(fileStem));

  const dotEdges: Array<readonly [string, string, Record<string, string>]> = [];
  const dotMissing: Array<readonly [string, string, string]> = [];
  const externalEdges: Array<readonly [string, string]> = [];

  const stemDepsOnMut = new Map<Stem, Set<Stem>>(
    [...allStems].map(s => [s, new Set()]),
  );

  for (const f of cppFiles) {
    const fromStem = fileStem(f);
    const id = nodeId(f);
    const src = readFileSync(f, "utf8");
    const baseDir = dirname(f);

    const includes = [...src.matchAll(/^#include\s+["<]([^>"]+)[">]/gm)];
    for (const inc of includes) {
      const target = inc[1];

      const extMatch = KNOWN_EXTERNALS.find(([, pats]) => pats.some(p => p.test(target)));
      if (extMatch) {
        externalEdges.push([id, extMatch[0]]);
        continue;
      }

      const resolved = (
        [join(baseDir, target), join(CPP_ROOT, target), join(CPP_INCLUDE_ROOT, target)]
          .find(c => isFile(c)) ?? null
      ) as AbsPath | null;

      if (resolved) {
        dotEdges.push([id, nodeId(resolved), { color: "#882288" }]);

        const toStem: Stem | undefined =
          resolvedToStem.get(resolved) ??
          resolvedToStem.get(realpathSafe(resolved)) ??
          (allStems.has(fileStem(resolved)) ? fileStem(resolved) : undefined);

        if (toStem !== undefined && toStem !== fromStem) {
          stemDepsOnMut.get(fromStem)!.add(toStem);
        } else if (toStem === undefined) {
          console.warn(`  ⚠ include resolved outside CPP_ROOT: ${resolved} (from ${relative(CPP_ROOT, f)})`);
        }
      } else if (!target.startsWith("<") && !STD_HEADERS.has(target)) {
        const misId = "missing_" + target.replace(/[^a-zA-Z0-9_]/g, "_");
        dotMissing.push([id, misId, target]);
      }
    }
  }

  return {
    allStems,
    stemDepsOn: stemDepsOnMut as ReadonlyMap<Stem, ReadonlySet<Stem>>,
    dotEdges,
    dotMissing,
    externalEdges,
  };
};

// ─── Topo sort (Kahn's algorithm) ────────────────────────────────────────────

const kahnSort = (
  allStems: ReadonlySet<Stem>,
  stemDepsOn: ReadonlyMap<Stem, ReadonlySet<Stem>>,
): Stem[] => {
  const inDegree = new Map<Stem, number>([...allStems].map(s => [s, 0]));
  const revGraph = new Map<Stem, Stem[]>([...allStems].map(s => [s, []]));

  for (const [stem, deps] of stemDepsOn) {
    for (const dep of deps) {
      if (!revGraph.has(dep)) continue;
      revGraph.get(dep)!.push(stem);
      inDegree.set(stem, inDegree.get(stem)! + 1);
    }
  }

  const queue = [...allStems].filter(s => inDegree.get(s) === 0).sort();
  const sorted: Stem[] = [];

  while (queue.length > 0) {
    queue.sort();
    const cur = queue.shift()!;
    sorted.push(cur);
    for (const nb of revGraph.get(cur)!) {
      const d = inDegree.get(nb)! - 1;
      inDegree.set(nb, d);
      if (d === 0) queue.push(nb);
    }
  }

  for (const s of [...allStems].sort()) {
    if (!sorted.includes(s)) sorted.push(s);
  }

  return sorted;
};

// ─── Rose tree construction ───────────────────────────────────────────────────
//
// Strategy:
//   For each stem (in topo order, so dependencies always come before dependents),
//   choose its "display parent": the dependency with the HIGHEST index in the
//   topo-sorted list (placed last = most recently seen = best cluster anchor).
//   Tie-break alphabetically.
//
//   IMPORTANT: we only consider deps that are strictly BEFORE this stem in the
//   sorted order, which is always true by construction of a topo sort — every
//   dep of X comes before X.
//
//   We then literally insert each stem as a child of its chosen parent node in
//   the rose tree.  The DFS renderer below will assign depth = parentDepth + 1,
//   so depth can never skip a level (MD007 is structurally impossible to violate).

const stemToFilePair = (stem: Stem): FilePair => {
  const dir = dirname(stem);
  const base = basename(stem as string);
  const cppPath = join(dir, base + ".cpp");
  const hPath = join(dir, base + ".h");
  const hppPath = join(dir, base + ".hpp");
  return {
    stem,
    name: relative(CPP_ROOT, stem as string) as RelPath,
    h: isFile(hPath) ? relative(CPP_ROOT, hPath) as RelPath
      : isFile(hppPath) ? relative(CPP_ROOT, hppPath) as RelPath
        : undefined,
    cpp: isFile(cppPath) ? relative(CPP_ROOT, cppPath) as RelPath : undefined,
  };
};

const buildRoseTree = (
  sortedStems: ReadonlyArray<Stem>,
  stemDepsOn: ReadonlyMap<Stem, ReadonlySet<Stem>>,
): TaskTree[] => {
  const stemToIdx = new Map<Stem, number>(sortedStems.map((s, i) => [s, i]));

  // Map from stem → its TaskTree node (so we can push children into it)
  const nodeMap = new Map<Stem, TaskTree>();
  for (const stem of sortedStems) {
    nodeMap.set(stem, { pair: stemToFilePair(stem), children: [] });
  }

  // Roots of the forest (stems with no chosen parent)
  const roots: TaskTree[] = [];

  for (const stem of sortedStems) {
    const curIdx = stemToIdx.get(stem)!;

    // CRITICAL: only consider deps that appear STRICTLY BEFORE this stem in the
    // topo-sorted list. Deps that appear after (possible due to cycles in the C++
    // dep graph — Kahn's appends cycle members at the end) must be excluded, or
    // they produce cycles in the rose tree itself, which the DFS can never fully
    // visit (nodes in rose-tree cycles are unreachable from any root, so they
    // silently vanish from the markdown output).
    const eligibleDeps = [...(stemDepsOn.get(stem) ?? [])].filter(dep => {
      const iDep = stemToIdx.get(dep) ?? -1;
      return iDep !== -1 && iDep < curIdx;
    });

    if (eligibleDeps.length === 0) {
      // No eligible parent: this stem is a root (either truly leaf, or all its
      // C++ deps are part of a cycle placed after it by Kahn's).
      roots.push(nodeMap.get(stem)!);
      continue;
    }

    // Pick the eligible dep with the HIGHEST index — the one placed most recently
    // before us in the sorted list. This clusters related files together: siblings
    // that share a common "last" dependency end up under the same parent.
    // Tie-break alphabetically for determinism.
    const parentStem = eligibleDeps.reduce<Stem>((best, dep) => {
      const iDep = stemToIdx.get(dep) ?? -1;
      const iBest = stemToIdx.get(best) ?? -1;
      return iDep > iBest || (iDep === iBest && dep < best) ? dep : best;
    }, eligibleDeps[0]);

    const parentNode = nodeMap.get(parentStem)!;
    (parentNode.children as TaskTree[]).push(nodeMap.get(stem)!);
  }

  return roots;
};

// ─── Rose tree → Markdown ─────────────────────────────────────────────────────
//
// DFS traversal.  Depth of a node = depth of its parent + 1.
// This is the ONLY correct way to assign depths — the flat topoIndent approach
// could assign a depth that jumps by more than 1 from the previous list item,
// which is what was triggering MD007.

const renderTreeToMdLines = (roots: ReadonlyArray<TaskTree>): string[] => {
  const lines: string[] = [];

  const visit = (node: TaskTree, depth: number): void => {
    const pair = node.pair;
    const files = ([pair.h, pair.cpp].filter(Boolean) as RelPath[])
      .map(x => `\`${x}\``).join(" and ");
    const done = ([pair.h, pair.cpp].filter(Boolean) as RelPath[])
      .map(x => join(CPP_ROOT, x))
      .every(p => isReviewed(p));
    const checkbox = done ? "[x]" : "[ ]";
    const indent = " ".repeat(depth * 2);
    lines.push(`${indent}- ${checkbox} ${pair.name} (${files})`);

    // Children are already in topo order (they were pushed in sortedStems order)
    for (const child of node.children) {
      visit(child, depth + 1);
    }
  };

  for (const root of roots) {
    visit(root, 0);
  }

  return lines;
};

// ─── Validation ──────────────────────────────────────────────────────────────
//
// After building the rose tree and rendering, validate:
//   1. MD007: every `-` in the output has an indent that is a multiple of 2.
//   2. MD007 no-skip: no list item is indented more than 2 spaces beyond the
//      previous item's indentation (i.e., depth never jumps by more than 1).
//
// If these fire it means the rose tree renderer has a bug — they should be
// structurally impossible given a correct DFS over a rose tree.

const validateMdLines = (mdLines: ReadonlyArray<string>): void => {
  const listLine = /^( *)-[ \t]/;
  let prevIndent = 0;

  for (let i = 0; i < mdLines.length; i++) {
    const m = mdLines[i].match(listLine);
    if (!m) { prevIndent = 0; continue; }

    const actual = m[1].length;

    // MD007: must be a multiple of 2
    if (actual % 2 !== 0) {
      throw new Error(
        `MD007 violation at output line ${i + 1}: indent=${actual} is not a multiple of 2.\n` +
        `Line: ${JSON.stringify(mdLines[i])}`,
      );
    }

    // MD007 no-skip: may not jump more than one level (2 spaces) deeper than previous
    if (actual > prevIndent + 2) {
      throw new Error(
        `MD007 no-skip violation at output line ${i + 1}: ` +
        `jumped from indent=${prevIndent} to indent=${actual} (max allowed: ${prevIndent + 2}).\n` +
        `Line: ${JSON.stringify(mdLines[i])}`,
      );
    }

    prevIndent = actual;
  }
};

// ─── Markdown file builder ────────────────────────────────────────────────────

const buildOrderMd = (
  sortedStems: ReadonlyArray<Stem>,
  stemDepsOn: ReadonlyMap<Stem, ReadonlySet<Stem>>,
): TaskTree[] => {
  const roots = buildRoseTree(sortedStems, stemDepsOn);
  const mdBody = renderTreeToMdLines(roots);

  // ── Completeness check: every stem must appear exactly once in the output ──
  // If this fires, buildRoseTree produced rose-tree cycles (unreachable nodes).
  const listItemCount = mdBody.filter(l => /^\s*-\s/.test(l)).length;
  if (listItemCount !== sortedStems.length) {
    throw new Error(
      `Rose tree completeness failure: rendered ${listItemCount} items but expected ${sortedStems.length}.\n` +
      `This usually means a cycle in the rose tree (dep-graph cycles causing a node to be ` +
      `both an ancestor and a descendant of itself). Check buildRoseTree's parent selection.`,
    );
  }

  const mdLines = [
    "# C++ to Rust Porting Review Order",
    "",
    "Files are topologically sorted by dependency order (leaves first).",
    "Siblings at the same indentation level are independent and can be reviewed in any order.",
    "",
    ...mdBody,
  ];

  validateMdLines(mdLines);

  const mdPath = join(CPP_ROOT, "order_of_review.md");
  writeFileSync(mdPath, mdLines.join("\n") + "\n");
  console.log(`✅  Written ${mdPath}`);

  return roots;
};

// ─── DOT builder ─────────────────────────────────────────────────────────────

const buildDot = (() => {
  const lines: string[] = [];
  const addedNodes = new Set<string>();
  const addedEdges = new Set<string>();
  const externalIds = new Map<string, string>();

  const addNode = (id: string, label: string, attrs: Record<string, string> = {}): void => {
    if (addedNodes.has(id)) return;
    addedNodes.add(id);
    const attrStr = Object.entries({
      label: `"${label}"`,
      ...Object.fromEntries(Object.entries(attrs).map(([k, v]) => [k, `"${v}"`]))
    }).map(([k, v]) => `${k}=${v}`).join(", ");
    lines.push(`  ${id} [${attrStr}];`);
  };

  const addEdge = (from: string, to: string, attrs: Record<string, string> = {}): void => {
    const key = `${from}->${to}`;
    if (addedEdges.has(key)) return;
    addedEdges.add(key);
    const attrStr = Object.entries(attrs).map(([k, v]) => `${k}="${v}"`).join(", ");
    lines.push(`  ${from} -> ${to}${attrStr ? ` [${attrStr}]` : ""};`);
  };

  const ensureExternal = (label: string): string => {
    if (externalIds.has(label)) return externalIds.get(label)!;
    const id = "ext_" + label.replace(/[^a-zA-Z0-9_]/g, "_");
    externalIds.set(label, id);
    addNode(id, label, {
      shape: "diamond", style: "filled",
      fillcolor: "#ffcccc", fontcolor: "#880000"
    });
    return id;
  };

  // ── Rust ──────────────────────────────────────────────────────────────────
  const buildRustGraph = (): void => {
    const workspacePath = join(RUST_ROOT, "Cargo.toml");
    if (!isFile(workspacePath)) return;

    const workspaceToml = readFileSync(workspacePath, "utf8");
    const membersMatch = workspaceToml.match(/members\s*=\s*\[([^\]]+)\]/);
    const members: string[] = membersMatch
      ? membersMatch[1].split(",").map(s => s.trim().replace(/['"]/g, "").trim()).filter(Boolean)
      : [];

    lines.push(`  subgraph cluster_rust {`);
    lines.push(`    label="Rust workspace (src/rust)";`);
    lines.push(`    style=filled; fillcolor="#e8f4e8"; color="#228822";`);

    for (const member of members) {
      const memberDir = join(RUST_ROOT, member);
      const memberCargoPath = join(memberDir, "Cargo.toml");
      if (!isFile(memberCargoPath)) continue;

      const cargo = readFileSync(memberCargoPath, "utf8");
      const nameMatch = cargo.match(/\[package\][^[]*name\s*=\s*"([^"]+)"/s);
      const pkgName = nameMatch ? nameMatch[1] : member;

      const depSection = cargo.match(/\[dependencies\]([\s\S]*?)(?=\[|$)/)?.[1] ?? "";
      const cargoDeps = depSection.split("\n")
        .filter(l => l.trim() && !l.trim().startsWith("#"))
        .flatMap(dl => { const m = dl.match(/^([a-zA-Z0-9_-]+)\s*=/); return m ? [m[1]] : []; });

      const rsFiles = walkDir(join(memberDir, "src"), [".rs"]);

      lines.push(`    subgraph cluster_${nodeId(memberDir)} {`);
      lines.push(`      label="${pkgName}"; style=filled; fillcolor="#d0ecd0";`);
      for (const rs of rsFiles) {
        const id = nodeId(rs);
        addNode(id, basename(rs), {
          shape: "box", style: "filled", fillcolor: "#f0fff0",
          fontsize: "10", tooltip: shortLabel(rs),
        });
        lines.push(`      ${id};`);
      }
      lines.push(`    }`);

      for (const dep of cargoDeps) {
        const isWs = members.includes(dep) || members.some(m => m.replace(/-/g, "_") === dep);
        if (isWs) continue;
        const extId = ensureExternal(dep);
        const crateNode = "crate_" + pkgName.replace(/[^a-zA-Z0-9_]/g, "_");
        if (!addedNodes.has(crateNode)) {
          lines.push(`  ${crateNode} [label="${pkgName}", shape=component, style=filled, fillcolor="#c8e8c8"];`);
          addedNodes.add(crateNode);
        }
        addEdge(crateNode, extId, { style: "dashed", color: "#cc0000", label: "cargo dep" });
      }

      for (const rs of rsFiles) {
        const id = nodeId(rs);
        const src = readFileSync(rs, "utf8");
        for (const [extLabel, patterns] of KNOWN_EXTERNALS) {
          for (const pat of patterns) {
            if (pat.test(src)) { addEdge(id, ensureExternal(extLabel), { style: "dashed", color: "#cc4400" }); break; }
          }
        }
        const portMatch = src.match(/\/\/\s*Port(?:ed)?\s+of\s+([^\n]+)/i);
        if (portMatch) {
          const cppRel = portMatch[1].trim().replace(/^src\//, "");
          const cppId = "cpp_" + cppRel.replace(/[^a-zA-Z0-9_]/g, "_");
          if (!addedNodes.has(cppId)) {
            addNode(cppId, cppRel, {
              shape: "note", style: "filled", fillcolor: "#fff0cc", fontsize: "9", fontcolor: "#664400",
            });
          }
          addEdge(id, cppId, { style: "dotted", color: "#888800", label: "port of", fontsize: "8" });
        }
      }
    }
    lines.push(`  }`);
  };

  // ── C++ ───────────────────────────────────────────────────────────────────
  const buildCppGraph = (): void => {
    const cppFiles = walkDir(CPP_ROOT, [".cpp", ".h", ".hpp"]);

    lines.push(`  subgraph cluster_cpp {`);
    lines.push(`    label="C++ source (src/removed_cpp)"; style=filled; fillcolor="#f0e8ff"; color="#882288";`);

    const dirGroups = cppFiles.reduce<Map<string, AbsPath[]>>((acc, f) => {
      const group = relative(CPP_ROOT, f).split("/")[0] ?? "(root)";
      return acc.set(group, [...(acc.get(group) ?? []), f]);
    }, new Map());

    for (const [group, files] of dirGroups) {
      const gid = "cpp_grp_" + group.replace(/[^a-zA-Z0-9_]/g, "_");
      lines.push(`    subgraph cluster_${gid} {`);
      lines.push(`      label="${group}"; style=filled; fillcolor="#e8d8ff";`);
      for (const f of files) {
        const id = nodeId(f);
        const color = [".h", ".hpp"].includes(extname(f)) ? "#f8f0ff" : "#fff8ff";
        addNode(id, basename(f), { shape: "box", style: "filled", fillcolor: color, fontsize: "9", tooltip: shortLabel(f) });
        lines.push(`      ${id};`);
      }
      lines.push(`    }`);
    }
    lines.push(`  }`);

    // Build deps
    const { allStems, stemDepsOn, dotEdges, dotMissing, externalEdges } = buildCppDeps(cppFiles);

    // Emit DOT edges
    const missingAdded = new Set<string>();
    for (const [from, to, attrs] of dotEdges) addEdge(from, to, attrs);
    for (const [from, misId, label] of dotMissing) {
      if (!missingAdded.has(misId)) {
        addNode(misId, label, { shape: "plaintext", fontsize: "8", fontcolor: "#aaaaaa" });
        missingAdded.add(misId);
      }
      addEdge(from, misId, { style: "dotted", color: "#aaaaaa" });
    }
    for (const [from, extLabel] of externalEdges) {
      addEdge(from, ensureExternal(extLabel), { style: "dashed", color: "#cc00cc" });
    }

    // Build rose tree → order_of_review.md
    const sortedStems = kahnSort(allStems, stemDepsOn);
    buildOrderMd(sortedStems, stemDepsOn);
  };

  return {
    buildRustGraph,
    buildCppGraph,
    getLines: () => lines,
    stats: () => ({ nodes: addedNodes.size, edges: addedEdges.size }),
  };
})();

// ─── Main ─────────────────────────────────────────────────────────────────────

const dotPreamble: string[] = [
  `digraph lean_deps {`,
  `  rankdir=LR;`,
  `  overlap=false;`,
  `  splines=true;`,
  `  fontname="sans-serif";`,
  `  node [fontname="monospace", fontsize=10];`,
  `  edge [fontsize=8];`,
  ``,
  `  subgraph cluster_externals {`,
  `    label="External dependencies"; style=filled; fillcolor="#fff0f0"; color="#aa0000";`,
  `  }`,
  ``,
];

if (!cppOnly) buildDot.buildRustGraph();
if (!rustOnly) buildDot.buildCppGraph();

const dot = [...dotPreamble, ...buildDot.getLines(), `}`].join("\n");
writeFileSync(outFile, dot);

const { nodes, edges } = buildDot.stats();
console.log(`✅  Written ${outFile}  (${dot.length} bytes)`);
console.log(`   Nodes: ${nodes}   Edges: ${edges}`);

// ── Auto-render SVG ───────────────────────────────────────────────────────────
const svgFile = outFile.replace(/\.dot$/, "") + ".svg";
const dotBinFound = (() => {
  try { execSync("which dot", { stdio: "ignore" }); return true; }
  catch { return false; }
})();

if (dotBinFound) {
  try {
    console.log(`🔄  Rendering SVG with dot…`);
    execSync(`dot -Tsvg "${outFile}" -o "${svgFile}"`, { stdio: "inherit" });
    console.log(`✅  Written ${svgFile}`);
    console.log(`\nOpen: xdg-open "${svgFile}"`);
  } catch (e) {
    console.warn(`⚠️  dot render failed: ${(e as Error).message}`);
    printManual();
  }
} else {
  printManual();
}

function printManual(): void {
  console.log(`Render with:`);
  console.log(`   dot -Tsvg ${outFile} -o ${svgFile}`);
  console.log(`   dot -Tpng ${outFile} -o ${outFile.replace(/\.dot$/, ".png")}`);
}
