#!/usr/bin/env bun
/**
 * Validate borrow-annotation consistency between the C runtime and Lean:
 *   1. Collect CPP function definitions (with bodies) and re-exports (declarations).
 *   2. Report CPP signature drift (same name, different type-level signature).   [point 3]
 *   3. Parse Lean `@[extern "sym"]` declarations and their `@&` markers.
 *   4. Report where borrow disagrees:                                            [point 5]
 *        - CPP `b_lean_obj_arg` but Lean not `@&`
 *        - Lean `@&` but CPP not `b_lean_obj_arg`
 *
 * The `*lean_obj_arg` typedefs live in the C *headers* (the `.cpp` bodies use bare
 * `object *`), so the canonical borrow signature prefers the typedef-bearing entry.
 *
 * Usage: ./srghmascripts/borrow_annotation_consistency.ts [--help] [--only-summary]
 *        [--show-consistent] [--show-unmatched] [--low-confidence] [--no-color]
 */

import fs from "node:fs";
import path from "node:path";
import { glob } from "node:fs/promises";
import { parseArgs } from "node:util";
import {
  parseCppFunctions,
  parseLeanExterns,
  pickCanonicalCppFn,
  findCppSignatureDrift,
  compareBorrow,
  type CppFn,
  type LeanExtern,
  type Comparison,
} from "./borrow_annotation_consistency/lib";
import { makePathExcluder } from "./exported_imported_lean_rust_fns/glob";

const ROOT_DIR = "/home/srghma/projects/lean4";
const LEAN_DIR = path.join(ROOT_DIR, "src");
const CPP_DIR = path.join(ROOT_DIR, "origin-master-src");

const IGNORED_LEAN_GLOBS = [
  "src/rust/**",
  "src/**/.lake/**",
  "src/**/build/**",
  "src/**/dist/**",
  "src/**/out/**",
];

// ── CLI ──────────────────────────────────────────────────────────────────────
const { values } = parseArgs({
  args: process.argv.slice(2),
  options: {
    help: { type: "boolean", short: "h" },
    "only-summary": { type: "boolean" },
    "show-consistent": { type: "boolean" },
    "show-unmatched": { type: "boolean" },
    "low-confidence": { type: "boolean" },
    "no-color": { type: "boolean" },
  },
  strict: true,
});

if (values.help) {
  console.log(`Usage: ./srghmascripts/borrow_annotation_consistency.ts [options]

Compares C borrow typedefs (b_lean_obj_arg) with Lean @& annotations.

Options:
  -h, --help          Show this help
  --only-summary      Only print the final summary counts
  --show-consistent   List the symbols whose borrow annotations already agree
  --show-unmatched    List informational buckets (extern/cpp with no counterpart)
  --low-confidence    Include arity-mismatch (prefix-aligned) findings in the main list
  --no-color          Disable ANSI colors
`);
  process.exit(0);
}

const useColor = !!process.stdout.isTTY && !process.env.NO_COLOR && !values["no-color"];
const paint = (code: string, s: string) => (useColor ? `\x1b[${code}m${s}\x1b[0m` : s);
const c = {
  h: (s: string) => paint("1;35", s),
  file: (s: string) => paint("36", s),
  sym: (s: string) => paint("1;33", s),
  ok: (s: string) => paint("32", s),
  warn: (s: string) => paint("1;31", s),
  dim: (s: string) => paint("2", s),
};
const rel = (p: string) => path.relative(ROOT_DIR, p);

// ── Collect ──────────────────────────────────────────────────────────────────
async function collectCpp(): Promise<CppFn[]> {
  const fns: CppFn[] = [];
  for await (const file of glob("**/*.{h,hpp,cpp,c}", { cwd: CPP_DIR })) {
    const abs = path.join(CPP_DIR, file);
    const content = await fs.promises.readFile(abs, "utf8");
    fns.push(...parseCppFunctions(content, rel(abs)));
  }
  return fns;
}

async function collectLean(): Promise<LeanExtern[]> {
  const externs: LeanExtern[] = [];
  const exclude = makePathExcluder(LEAN_DIR, ROOT_DIR, IGNORED_LEAN_GLOBS);
  for await (const file of glob("**/*.lean", { cwd: LEAN_DIR, exclude })) {
    const abs = path.join(LEAN_DIR, file);
    const content = await fs.promises.readFile(abs, "utf8");
    externs.push(...parseLeanExterns(content, rel(abs)));
  }
  return externs;
}

// ── Main ─────────────────────────────────────────────────────────────────────
const onlySummary = !!values["only-summary"];
const section = (title: string) => {
  if (!onlySummary) console.log(`\n${c.h(`── ${title} ─────────────────────────────────────────`)}`);
};

if (!onlySummary) console.log(c.dim(`Scanning CPP under ${rel(CPP_DIR)}/ and Lean under ${rel(LEAN_DIR)}/ ...`));

const [cppFns, leanExterns] = await Promise.all([collectCpp(), collectLean()]);

// Group CPP by name; canonical (borrow-richest) entry per symbol.
const cppByName = new Map<string, CppFn[]>();
for (const f of cppFns) {
  const l = cppByName.get(f.fnName) ?? [];
  l.push(f);
  cppByName.set(f.fnName, l);
}
const cppCanon = new Map<string, CppFn>();
for (const [name, entries] of cppByName) cppCanon.set(name, pickCanonicalCppFn(entries));

// Group Lean externs by symbol; prefer a parseable one.
const leanBySym = new Map<string, LeanExtern[]>();
for (const e of leanExterns) {
  const l = leanBySym.get(e.symbolName) ?? [];
  l.push(e);
  leanBySym.set(e.symbolName, l);
}

const cppHasBorrow = (f: CppFn) => f.args.some((a) => a.kind === "b");
const leanHasBorrow = (e: LeanExtern) => e.params.includes("B");

// ── Point 3: CPP signature drift ─────────────────────────────────────────────
const drift = findCppSignatureDrift(cppFns);
section(`CPP signature drift — same name, different ABI-level signature (${drift.length})`);
if (!onlySummary) {
  if (drift.length === 0) console.log(c.ok("  none"));
  for (const d of drift) {
    console.log(`  ${c.sym(d.fnName)}`);
    for (const v of d.variants) {
      console.log(`    ${c.warn(v.sig)}`);
      for (const e of v.entries) {
        console.log(`      ${c.dim(`${e.filePath}:${e.lineNum}`)} ${e.hasBody ? "(def)" : "(decl)"} — ${e.returnType} (${e.args.map((a) => a.raw).join(", ")})`);
      }
    }
  }
}

// ── Borrow comparison over matched symbols ───────────────────────────────────
const comparisons: Comparison[] = [];
for (const [sym, entries] of leanBySym) {
  const lean = entries.find((e) => e.parseOk);
  if (!lean) continue;
  const cpp = cppCanon.get(sym);
  if (!cpp) continue;
  comparisons.push(compareBorrow(sym, cpp, lean));
}

const mismatches = comparisons.filter((c) => c.findings.length > 0);
const highMismatch = mismatches.filter((m) => m.findings.some((f) => f.confidence === "high"));
const lowMismatch = mismatches.filter((m) => m.findings.every((f) => f.confidence === "low"));
const consistent = comparisons.filter((c) => c.findings.length === 0);

const printComparison = (m: Comparison) => {
  console.log(`  ${c.sym(m.symbolName)} ${c.dim(`(${m.lean.leanName})`)}${m.arityMatch ? "" : c.warn(` [arity ${m.cppArity} cpp vs ${m.leanArity} lean]`)}`);
  console.log(`    ${c.dim("cpp: ")}${c.file(`${m.cpp.filePath}:${m.cpp.lineNum}`)}  ${m.cpp.args.map((a) => (a.kind === "b" ? c.warn(a.raw) : a.raw)).join(", ")}`);
  console.log(`    ${c.dim("lean:")} ${c.file(`${m.lean.filePath}:${m.lean.lineNum}`)}  ${m.lean.params.map((p) => (p === "B" ? c.warn("@&") : "_")).join(", ")}  ${c.dim(m.lean.rawSig.slice(0, 120))}`);
  for (const f of m.findings) {
    const msg =
      f.direction === "cpp_borrowed_lean_not"
        ? `arg #${f.position}: CPP is ${c.warn("b_lean_obj_arg")} but Lean is NOT @&`
        : `arg #${f.position}: Lean is ${c.warn("@&")} but CPP is ${f.cppArg.raw} (not borrowed)`;
    console.log(`      ${c.warn("✗")} ${msg}`);
  }
};

section(`Borrow MISMATCHES — high confidence, arities align (${highMismatch.length})`);
if (!onlySummary) {
  if (highMismatch.length === 0) console.log(c.ok("  none"));
  for (const m of highMismatch) printComparison(m);
}

if (values["low-confidence"] || !onlySummary) {
  section(`Borrow mismatches — low confidence, arity differs (${lowMismatch.length})`);
  if (!onlySummary) {
    if (lowMismatch.length === 0) console.log(c.ok("  none"));
    for (const m of lowMismatch) printComparison(m);
  }
}

if (values["show-consistent"] && !onlySummary) {
  section(`Consistent (borrow agrees) (${consistent.length})`);
  for (const m of consistent) {
    console.log(`  ${c.ok("✓")} ${c.sym(m.symbolName)} ${c.dim(`${m.lean.rawSig}`)}`);
  }
}

// ── Informational: unmatched sets ────────────────────────────────────────────
const leanBorrowNoCpp = [...leanBySym.entries()]
  .filter(([sym, es]) => es.some((e) => e.parseOk && leanHasBorrow(e)) && !cppCanon.has(sym))
  .map(([sym, es]) => ({ sym, e: es.find((e) => e.parseOk && leanHasBorrow(e))! }));

const cppBorrowNoLean = [...cppCanon.entries()]
  .filter(([sym, f]) => cppHasBorrow(f) && !leanBySym.has(sym))
  .map(([sym, f]) => ({ sym, f }));

const attrFormOverBorrowCpp = leanExterns.filter(
  (e) => !e.parseOk && cppCanon.has(e.symbolName) && cppHasBorrow(cppCanon.get(e.symbolName)!),
);

if (values["show-unmatched"] && !onlySummary) {
  section(`Lean @& externs with NO CPP signature in origin-master-src (${leanBorrowNoCpp.length})`);
  for (const { sym, e } of leanBorrowNoCpp) console.log(`  ${c.sym(sym)} ${c.dim(`${e.filePath}:${e.lineNum} — ${e.rawSig}`)}`);
  section(`CPP b_lean_obj_arg functions with NO Lean @[extern] (${cppBorrowNoLean.length})`);
  for (const { sym, f } of cppBorrowNoLean) console.log(`  ${c.sym(sym)} ${c.dim(`${f.filePath}:${f.lineNum}`)}`);
  section(`Attribute-form externs over a borrowing CPP fn (args unparsed) (${attrFormOverBorrowCpp.length})`);
  for (const e of attrFormOverBorrowCpp) console.log(`  ${c.sym(e.symbolName)} ${c.dim(`${e.filePath}:${e.lineNum} — ${e.rawSig}`)}`);
}

// ── Summary ──────────────────────────────────────────────────────────────────
const cppBorrowFns = [...cppCanon.values()].filter(cppHasBorrow).length;
const leanBorrowExterns = [...leanBySym.values()].filter((es) => es.some((e) => e.parseOk && leanHasBorrow(e))).length;

console.log(`\n${c.h("── Summary ──────────────────────────────────────────")}`);
const row = (label: string, n: number, color?: (s: string) => string) => {
  const val = color ? color(String(n)) : String(n);
  console.log(`  ${label.padEnd(58, ".")} ${val}`);
};
row("CPP functions parsed (defs + decls)", cppFns.length);
row("CPP distinct symbols", cppCanon.size);
row("CPP symbols with a b_lean_obj_arg param", cppBorrowFns);
row("CPP signature drift (point 3)", drift.length, drift.length ? c.warn : c.ok);
row("Lean @[extern] occurrences", leanExterns.length);
row("Lean externs with parsed signature", leanExterns.filter((e) => e.parseOk).length);
row("Lean externs with @& param", leanBorrowExterns);
row("Matched symbols (cpp ∩ lean, comparable)", comparisons.length);
row("  → borrow agrees", consistent.length, c.ok);
row("  → MISMATCH (high confidence)", highMismatch.length, highMismatch.length ? c.warn : c.ok);
row("  → mismatch (low confidence / arity differs)", lowMismatch.length, lowMismatch.length ? c.warn : c.dim);
row("Lean @& externs with no CPP ref (unverifiable)", leanBorrowNoCpp.length, c.dim);
row("CPP borrow fns with no Lean extern", cppBorrowNoLean.length, c.dim);
row("Attribute-form externs over borrow CPP (unparsed)", attrFormOverBorrowCpp.length, c.dim);

const hardFailures = drift.length + highMismatch.length;
console.log("");
if (hardFailures === 0) {
  console.log(c.ok("✓ No high-confidence borrow inconsistencies or CPP signature drift."));
} else {
  console.log(c.warn(`✗ ${hardFailures} issue(s): ${drift.length} CPP drift + ${highMismatch.length} borrow mismatch.`));
}
process.exit(hardFailures === 0 ? 0 : 1);
