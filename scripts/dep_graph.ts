#!/usr/bin/env bun
/**
 * dep_graph.ts — generate a Graphviz DOT file showing:
 *
 *   1. Rust crate/module graph (src/rust/**)
 *      - Cargo workspace members as cluster subgraphs
 *      - Rust source files as nodes
 *      - External crates (libc, libuv-sys2, …) as external nodes
 *      - "use <crate>" edges from each .rs file
 *      - "Port of <cpp>" annotation edges linking Rust files back to removed_cpp/
 *
 *   2. C++ file graph (src/removed_cpp/**)
 *      - #include edges (local and system)
 *      - Known external deps (cadical, mimalloc, libuv, ICU, emscripten,
 *        windows.h, posix headers, execinfo.h, llvm-c/Core.h) as external nodes
 *
 * Usage:
 *   bun scripts/dep_graph.ts [--rust-only | --cpp-only] [--out graph.dot]
 *   dot -Tsvg graph.dot -o graph.svg
 */

import { readdirSync, readFileSync, statSync } from "fs";
import { join, relative, extname, basename, dirname } from "path";

// ─── CLI ──────────────────────────────────────────────────────────────────────
const args = process.argv.slice(2);
const rustOnly  = args.includes("--rust-only");
const cppOnly   = args.includes("--cpp-only");
const outIdx    = args.indexOf("--out");
const outFile   = outIdx !== -1 ? args[outIdx + 1] : "dep_graph.dot";

const ROOT = join(import.meta.dir, "..");
const RUST_ROOT       = join(ROOT, "src/rust");
const CPP_ROOT        = join(ROOT, "src/removed_cpp");
const CPP_INCLUDE_ROOT = join(ROOT, "src/removed_cpp/include"); // may not exist

// ─── Known external dependency groups ────────────────────────────────────────
// Maps a "canonical label" → list of patterns that identify it in source code.
const KNOWN_EXTERNALS: Record<string, RegExp[]> = {
  // C++ externals
  "cadical":         [/cadical/i],
  "mimalloc":        [/mimalloc/i],
  "libuv":           [/libuv\.h|uv\.h/i],
  "ICU (<icu.h>)":   [/icu\.h|unicode\//i],
  "emscripten":      [/emscripten\.h/i],
  "<windows.h>":     [/windows\.h|psapi\.h|ntdef\.h|bcrypt\.h/i],
  "<pthread.h>":     [/pthread\.h/i],
  "<unistd.h>":      [/\bunistd\.h\b/],
  "<dlfcn.h>":       [/dlfcn\.h/i],
  "<dirent.h>":      [/dirent\.h/i],
  "<link.h>":        [/\blink\.h\b/],
  "<execinfo.h>":    [/execinfo\.h/i],
  "LLVM":            [/llvm-c\/Core\.h|llvm\.h/i],
  // Rust externals (Cargo deps)
  "libc":            [/^use libc\b|libc::/m],
  "libuv-sys2":      [/^use libuv_sys2\b|libuv_sys2::/m],
};

// ─── Utilities ────────────────────────────────────────────────────────────────
function walkDir(dir: string, exts: string[]): string[] {
  const results: string[] = [];
  if (!statSafe(dir)?.isDirectory()) return results;
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    if (entry.name.startsWith(".")) continue;          // skip .still-nanoda etc
    const full = join(dir, entry.name);
    if (entry.isDirectory()) {
      results.push(...walkDir(full, exts));
    } else if (exts.includes(extname(entry.name))) {
      results.push(full);
    }
  }
  return results;
}

function statSafe(p: string) {
  try { return statSync(p); } catch { return null; }
}

/** Convert an absolute path to a stable DOT node id (no slashes/dots/spaces) */
function nodeId(path: string): string {
  return relative(ROOT, path).replace(/[^a-zA-Z0-9_]/g, "_");
}

function shortLabel(path: string): string {
  return relative(ROOT, path);
}

// ─── DOT builder ─────────────────────────────────────────────────────────────
const lines: string[] = [];
const addedNodes = new Set<string>();
const addedEdges = new Set<string>();

function addNode(id: string, label: string, attrs: Record<string, string> = {}) {
  if (addedNodes.has(id)) return;
  addedNodes.add(id);
  const attrStr = Object.entries({ label: `"${label}"`, ...Object.fromEntries(Object.entries(attrs).map(([k,v]) => [k, `"${v}"`])) })
    .map(([k, v]) => `${k}=${v}`).join(", ");
  lines.push(`  ${id} [${attrStr}];`);
}

function addEdge(from: string, to: string, attrs: Record<string, string> = {}) {
  const key = `${from}->${to}`;
  if (addedEdges.has(key)) return;
  addedEdges.add(key);
  const attrStr = Object.entries(attrs).map(([k, v]) => `${k}="${v}"`).join(", ");
  lines.push(`  ${from} -> ${to}${attrStr ? ` [${attrStr}]` : ""};`);
}

// ─── External dependency node helper ─────────────────────────────────────────
const externalNodeIds: Map<string, string> = new Map();
function ensureExternalNode(label: string) {
  if (externalNodeIds.has(label)) return externalNodeIds.get(label)!;
  const id = "ext_" + label.replace(/[^a-zA-Z0-9_]/g, "_");
  externalNodeIds.set(label, id);
  addNode(id, label, {
    shape: "diamond",
    style: "filled",
    fillcolor: "#ffcccc",
    fontcolor: "#880000",
  });
  return id;
}

// ─────────────────────────────────────────────────────────────────────────────
//  RUST graph
// ─────────────────────────────────────────────────────────────────────────────
function buildRustGraph() {
  // Discover workspace members from Cargo.toml
  const workspaceToml = readFileSync(join(RUST_ROOT, "Cargo.toml"), "utf8");
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
    if (!statSafe(memberCargoPath)) continue;

    const cargo = readFileSync(memberCargoPath, "utf8");

    // Parse package name
    const nameMatch = cargo.match(/\[package\][^[]*name\s*=\s*"([^"]+)"/s);
    const pkgName = nameMatch ? nameMatch[1] : member;

    // Parse dependencies
    const depSection = cargo.match(/\[dependencies\]([\s\S]*?)(?=\[|$)/)?.[1] ?? "";
    const depLines = depSection.split("\n").filter(l => l.trim() && !l.trim().startsWith("#"));
    const cargoDeps: string[] = [];
    for (const dl of depLines) {
      const m = dl.match(/^([a-zA-Z0-9_-]+)\s*=/);
      if (m) cargoDeps.push(m[1]);
    }

    // Collect .rs files
    const srcDir = join(memberDir, "src");
    const rsFiles = walkDir(srcDir, [".rs"]);

    lines.push(`    subgraph cluster_${nodeId(memberDir)} {`);
    lines.push(`      label="${pkgName}"; style=filled; fillcolor="#d0ecd0";`);

    // File nodes
    for (const rs of rsFiles) {
      const id = nodeId(rs);
      addNode(id, basename(rs), {
        shape: "box",
        style: "filled",
        fillcolor: "#f0fff0",
        fontsize: "10",
        tooltip: shortLabel(rs),
      });
      lines.push(`      ${id};`);
    }
    lines.push(`    }`);

    // Cargo dependency edges (crate → external)
    for (const dep of cargoDeps) {
      const isWorkspaceMember = members.includes(dep) || members.some(m => m.replace(/-/g,"_") === dep);
      if (isWorkspaceMember) continue; // handled below via workspace links
      const extId = ensureExternalNode(dep);
      // Add an edge from the crate cluster node (use memberDir id)
      const crateNode = "crate_" + pkgName.replace(/[^a-zA-Z0-9_]/g, "_");
      // We use a proxy node for the crate itself
      if (!addedNodes.has(crateNode)) {
        lines.push(`  ${crateNode} [label="${pkgName}", shape=component, style=filled, fillcolor="#c8e8c8"];`);
        addedNodes.add(crateNode);
      }
      addEdge(crateNode, extId, { style: "dashed", color: "#cc0000", label: "cargo dep" });
    }

    // Within-crate: parse each .rs file for:
    //   - `use <external_crate>::` → external dep edge
    //   - `// Port of <path>` / `// Ported from <path>` → port-of annotation
    //   - internal `use crate::` or `mod` → edges between files
    for (const rs of rsFiles) {
      const id = nodeId(rs);
      const src = readFileSync(rs, "utf8");

      // External crate usage
      for (const [extLabel, patterns] of Object.entries(KNOWN_EXTERNALS)) {
        for (const pat of patterns) {
          if (pat.test(src)) {
            const extId = ensureExternalNode(extLabel);
            addEdge(id, extId, { style: "dashed", color: "#cc4400" });
            break;
          }
        }
      }

      // Port-of links
      const portMatch = src.match(/\/\/\s*Port(?:ed)?\s+of\s+([^\n]+)/i);
      if (portMatch) {
        // Try to find the C++ file
        const rawPath = portMatch[1].trim();
        // Strip leading 'src/' if present
        const cppRel = rawPath.replace(/^src\//, "");
        const cppFull = join(CPP_ROOT, cppRel.replace(/^(runtime|kernel|library|util|shell|initialize)/, "$1"));
        const cppId = "cpp_" + cppRel.replace(/[^a-zA-Z0-9_]/g, "_");
        if (!addedNodes.has(cppId)) {
          addNode(cppId, cppRel, {
            shape: "note",
            style: "filled",
            fillcolor: "#fff0cc",
            fontsize: "9",
            fontcolor: "#664400",
          });
        }
        addEdge(id, cppId, { style: "dotted", color: "#888800", label: "port of", fontsize: "8" });
      }
    }
  }

  // Workspace inter-crate edges (lean_shell → lean_runtime)
  const allCargos = members.map(m => {
    const p = join(RUST_ROOT, m, "Cargo.toml");
    if (!statSafe(p)) return null;
    const c = readFileSync(p, "utf8");
    const nm = c.match(/\[package\][^[]*name\s*=\s*"([^"]+)"/s);
    return { name: nm?.[1] ?? m, cargo: c };
  }).filter(Boolean) as { name: string; cargo: string }[];

  for (const { name, cargo } of allCargos) {
    const depSection = cargo.match(/\[dependencies\]([\s\S]*?)(?=\[|$)/)?.[1] ?? "";
    for (const m of depSection.matchAll(/^([a-zA-Z0-9_-]+)\s*=\s*\{[^}]*path\s*=/gm)) {
      const dep = m[1].replace(/-/g, "_");
      const fromNode = "crate_" + name.replace(/[^a-zA-Z0-9_]/g, "_");
      const toNode   = "crate_" + dep.replace(/[^a-zA-Z0-9_]/g, "_");
      // ensure proxy nodes exist
      if (!addedNodes.has(fromNode)) {
        lines.push(`  ${fromNode} [label="${name}", shape=component, style=filled, fillcolor="#c8e8c8"];`);
        addedNodes.add(fromNode);
      }
      if (!addedNodes.has(toNode)) {
        lines.push(`  ${toNode} [label="${dep}", shape=component, style=filled, fillcolor="#c8e8c8"];`);
        addedNodes.add(toNode);
      }
      addEdge(fromNode, toNode, { style: "bold", color: "#226622", label: "depends" });
    }
  }

  lines.push(`  }`); // end cluster_rust
}

// ─────────────────────────────────────────────────────────────────────────────
//  C++ graph
// ─────────────────────────────────────────────────────────────────────────────
function buildCppGraph() {
  const cppFiles = walkDir(CPP_ROOT, [".cpp", ".h", ".hpp"]);

  lines.push(`  subgraph cluster_cpp {`);
  lines.push(`    label="C++ source (src/removed_cpp)"; style=filled; fillcolor="#f0e8ff"; color="#882288";`);

  // Group by subdirectory
  const dirGroups: Map<string, string[]> = new Map();
  for (const f of cppFiles) {
    const rel = relative(CPP_ROOT, f);
    const parts = rel.split("/");
    const group = parts.length > 1 ? parts[0] : "(root)";
    if (!dirGroups.has(group)) dirGroups.set(group, []);
    dirGroups.get(group)!.push(f);
  }

  for (const [group, files] of dirGroups) {
    const gid = "cpp_grp_" + group.replace(/[^a-zA-Z0-9_]/g, "_");
    lines.push(`    subgraph cluster_${gid} {`);
    lines.push(`      label="${group}"; style=filled; fillcolor="#e8d8ff";`);
    for (const f of files) {
      const id = nodeId(f);
      const color = extname(f) === ".h" || extname(f) === ".hpp" ? "#f8f0ff" : "#fff8ff";
      addNode(id, basename(f), {
        shape: "box",
        style: "filled",
        fillcolor: color,
        fontsize: "9",
        tooltip: shortLabel(f),
      });
      lines.push(`      ${id};`);
    }
    lines.push(`    }`);
  }
  lines.push(`  }`); // end cluster_cpp

  // Now add #include edges
  for (const f of cppFiles) {
    const id = nodeId(f);
    const src = readFileSync(f, "utf8");
    const baseDir = dirname(f);

    // Find all #include lines
    const includes = [...src.matchAll(/^#include\s+["<]([^>"]+)[">]/gm)];
    for (const inc of includes) {
      const target = inc[1];

      // Check if it's a known external
      let matched = false;
      for (const [extLabel, patterns] of Object.entries(KNOWN_EXTERNALS)) {
        for (const pat of patterns) {
          if (pat.test(target)) {
            const extId = ensureExternalNode(extLabel);
            addEdge(id, extId, { style: "dashed", color: "#cc00cc" });
            matched = true;
            break;
          }
        }
        if (matched) break;
      }
      if (matched) continue;

      // Try to resolve as a local file
      // Lean uses includes like "runtime/foo.h" resolved from src/removed_cpp/
      const candidatePaths = [
        join(baseDir, target),
        join(CPP_ROOT, target),
        join(CPP_ROOT, "..", target),
      ];
      let resolved: string | null = null;
      for (const cand of candidatePaths) {
        if (statSafe(cand)?.isFile()) {
          resolved = cand;
          break;
        }
      }

      if (resolved) {
        const toId = nodeId(resolved);
        addEdge(id, toId, { color: "#882288" });
      } else if (!target.startsWith("<") && !target.match(/^(string|vector|map|set|memory|algorithm|iostream|sstream|cstdlib|cstdio|cstdint|cstring|new|utility|functional|thread|mutex|condition_variable|atomic|chrono|cassert|cmath|climits|csignal|cerrno|cwchar|cwctype|locale|bitset|initializer_list|typeinfo|numeric|iterator|type_traits|tuple|array|deque|forward_list|list|queue|stack|unordered_map|unordered_set)$/)) {
        // Unknown local-ish include — add as a grey "missing" node
        const misId = "missing_" + target.replace(/[^a-zA-Z0-9_]/g, "_");
        if (!addedNodes.has(misId)) {
          addNode(misId, target, {
            shape: "plaintext",
            fontsize: "8",
            fontcolor: "#aaaaaa",
          });
        }
        addEdge(id, misId, { style: "dotted", color: "#aaaaaa" });
      }
    }
  }
}

// ─────────────────────────────────────────────────────────────────────────────
//  Main
// ─────────────────────────────────────────────────────────────────────────────
lines.push(`digraph lean_deps {`);
lines.push(`  rankdir=LR;`);
lines.push(`  overlap=false;`);
lines.push(`  splines=true;`);
lines.push(`  fontname="sans-serif";`);
lines.push(`  node [fontname="monospace", fontsize=10];`);
lines.push(`  edge [fontsize=8];`);
lines.push(``);

lines.push(`  // ── External dependency cluster ──`);
lines.push(`  subgraph cluster_externals {`);
lines.push(`    label="External dependencies"; style=filled; fillcolor="#fff0f0"; color="#aa0000";`);
// External nodes will be injected here; we close the subgraph after building
// (Graphviz ignores ordering within the source for cluster membership;
//  we'll just add external nodes inside a late-bound subgraph by prefixing their id in output)
lines.push(`  }`);
lines.push(``);

if (!cppOnly) buildRustGraph();
if (!rustOnly) buildCppGraph();

lines.push(`}`);

// Fix: move external nodes into the cluster_externals block
// (they were added inline; we need them before the closing brace).
// Instead of reorganising, just append them outside — Graphviz still renders
// the attribute grouping via node attributes (diamond/fillcolor).
const dot = lines.join("\n");
await Bun.write(outFile, dot);

console.log(`✅  Written ${outFile}  (${dot.length} bytes)`);
console.log(`   Nodes: ${addedNodes.size}   Edges: ${addedEdges.size}`);
console.log(``);
console.log(`Render with:`);
console.log(`   dot -Tsvg ${outFile} -o dep_graph.svg`);
console.log(`   dot -Tpng ${outFile} -o dep_graph.png`);
console.log(`   xdot ${outFile}   # interactive`);
