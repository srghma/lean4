#!/usr/bin/env bun

import { existsSync, readFileSync } from "node:fs";
import path from "node:path";

type Occurrence = {
  name: string;
  line: number;
  kind:
    | "lean-extern"
    | "rust-pub-fn"
    | "rust-pub-reexport"
    | "rust-moved-target";
  text: string;
  file: string;
};

const useColors = !!process.stdout.isTTY && !process.env.NO_COLOR;
const colors = useColors
  ? {
      reset: "\x1b[0m",
      bold: "\x1b[1m",
      green: "\x1b[32m",
      yellow: "\x1b[33m",
      red: "\x1b[31m",
      cyan: "\x1b[36m",
      dim: "\x1b[2m",
    }
  : {
      reset: "",
      bold: "",
      green: "",
      yellow: "",
      red: "",
      cyan: "",
      dim: "",
    };

const c = {
  ok: (text: string) => `${colors.green}${text}${colors.reset}`,
  warn: (text: string) => `${colors.yellow}${text}${colors.reset}`,
  err: (text: string) => `${colors.red}${text}${colors.reset}`,
  head: (text: string) => `${colors.bold}${colors.cyan}${text}${colors.reset}`,
  dim: (text: string) => `${colors.dim}${text}${colors.reset}`,
  file: (text: string) => `${colors.bold}${text}${colors.reset}`,
};

function usage(): never {
  console.error(
    `Usage: ./srghmascripts/are_there_extra_definitions.ts <rust-file> <lean-file>`,
  );
  process.exit(1);
}

function stripCommentsKeepLines(text: string, kind: "rust" | "lean"): string {
  const out: string[] = [];
  let i = 0;
  let blockDepth = 0;
  let inLineComment = false;
  let inString = false;
  let stringQuote: '"' | "'" | null = null;

  while (i < text.length) {
    const ch = text[i]!;
    const next = text[i + 1] ?? "";

    if (inLineComment) {
      if (ch === "\n") {
        inLineComment = false;
        out.push("\n");
      } else {
        out.push(" ");
      }
      i += 1;
      continue;
    }

    if (blockDepth > 0) {
      const opensRust = kind === "rust" && ch === "/" && next === "*";
      const closesRust = kind === "rust" && ch === "*" && next === "/";
      const opensLean = kind === "lean" && ch === "/" && next === "-";
      const closesLean = kind === "lean" && ch === "-" && next === "/";

      if (opensRust || opensLean) {
        blockDepth += 1;
        out.push(" ", " ");
        i += 2;
        continue;
      }
      if (closesRust || closesLean) {
        blockDepth -= 1;
        out.push(" ", " ");
        i += 2;
        continue;
      }
      out.push(ch === "\n" ? "\n" : " ");
      i += 1;
      continue;
    }

    if (inString) {
      out.push(ch);
      if (ch === "\\") {
        if (i + 1 < text.length) out.push(text[i + 1]!);
        i += 2;
        continue;
      }
      if (ch === stringQuote) {
        inString = false;
        stringQuote = null;
      }
      i += 1;
      continue;
    }

    const startsLineComment =
      (kind === "rust" && ch === "/" && next === "/") ||
      (kind === "lean" && ch === "-" && next === "-");
    const startsBlockComment =
      (kind === "rust" && ch === "/" && next === "*") ||
      (kind === "lean" && ch === "/" && next === "-");

    if (startsLineComment) {
      inLineComment = true;
      out.push(" ", " ");
      i += 2;
      continue;
    }

    if (startsBlockComment) {
      blockDepth = 1;
      out.push(" ", " ");
      i += 2;
      continue;
    }

    if (ch === '"' || ch === "'") {
      inString = true;
      stringQuote = ch;
      out.push(ch);
      i += 1;
      continue;
    }

    out.push(ch);
    i += 1;
  }

  return out.join("");
}

function collectLeanExterns(filePath: string): Occurrence[] {
  const original = readFileSync(filePath, "utf8");
  const stripped = stripCommentsKeepLines(original, "lean");
  const lines = stripped.split(/\r?\n/);
  const originalLines = original.split(/\r?\n/);
  const results: Occurrence[] = [];
  const seen = new Set<string>();
  const externRegex = /extern\s+"(lean_[A-Za-z0-9_]+)"/g;

  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i]!;
    let match: RegExpExecArray | null;
    externRegex.lastIndex = 0;
    while ((match = externRegex.exec(line)) !== null) {
      const name = match[1]!;
      const key = `${name}@${i + 1}`;
      if (seen.has(key)) continue;
      seen.add(key);
      results.push({
        name,
        line: i + 1,
        kind: "lean-extern",
        text: originalLines[i]!.trim(),
        file: filePath,
      });
    }
  }

  return results;
}

function collectRustPublicApi(filePath: string): Occurrence[] {
  const original = readFileSync(filePath, "utf8");
  const stripped = stripCommentsKeepLines(original, "rust");
  const lines = stripped.split(/\r?\n/);
  const originalLines = original.split(/\r?\n/);
  const results: Occurrence[] = [];

  const pubFnRegex =
    /\bpub(?:\s*\([^)]*\))?\s+(?:unsafe\s+)?(?:extern\s+"[^"]+"\s+)?fn\s+(lean_[A-Za-z0-9_]+)\b/g;
  const pubUseRegex =
    /\bpub\s+use\b[\s\S]*?::(lean_[A-Za-z0-9_]+)(?:\s+as\s+(lean_[A-Za-z0-9_]+))?\s*;/g;

  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i]!;
    let match: RegExpExecArray | null;
    pubFnRegex.lastIndex = 0;
    while ((match = pubFnRegex.exec(line)) !== null) {
      results.push({
        name: match[1]!,
        line: i + 1,
        kind: "rust-pub-fn",
        text: originalLines[i]!.trim(),
        file: filePath,
      });
    }
  }

  let match: RegExpExecArray | null;
  pubUseRegex.lastIndex = 0;
  while ((match = pubUseRegex.exec(stripped)) !== null) {
    const name = match[2] ?? match[1]!;
    const start = match.index;
    const line = stripped.slice(0, start).split(/\r?\n/).length;
    results.push({
      name,
      line,
      kind: "rust-pub-reexport",
      text: originalLines[line - 1]!.trim(),
      file: filePath,
    });
  }

  return results;
}

function collectMovedTargets(filePath: string): string[] {
  const text = readFileSync(filePath, "utf8");
  const lines = text.split(/\r?\n/);
  const targets: string[] = [];
  const movedRegex = /moved\s+(lean_[A-Za-z0-9_]+)\s+to\s+(.+?)$/;
  const crateSrcDir = (() => {
    let dir = path.dirname(filePath);
    while (dir !== path.dirname(dir)) {
      if (path.basename(dir) === "src") return dir;
      dir = path.dirname(dir);
    }
    return path.dirname(filePath);
  })();

  for (const line of lines) {
    const match = line.match(movedRegex);
    if (!match) continue;
    const rel = match[2]!.trim();
    const resolved = rel.startsWith("ffi/") || rel.startsWith("priv/") || rel.startsWith("todo_import_from_lean/")
      ? path.resolve(crateSrcDir, rel)
      : path.resolve(path.dirname(filePath), rel);
    if (existsSync(resolved)) targets.push(resolved);
  }

  return targets;
}

function collectRustSurface(rootRustFile: string): Occurrence[] {
  const results: Occurrence[] = [];
  const queue = [rootRustFile, ...collectMovedTargets(rootRustFile)];
  const seenFiles = new Set<string>();

  for (const file of queue) {
    if (seenFiles.has(file)) continue;
    seenFiles.add(file);
    for (const occ of collectRustPublicApi(file)) {
      results.push(
        file === rootRustFile
          ? occ
          : { ...occ, kind: "rust-moved-target", file },
      );
    }
  }

  return results;
}

function byName(items: Occurrence[]): Map<string, Occurrence[]> {
  const map = new Map<string, Occurrence[]>();
  for (const item of items) {
    const list = map.get(item.name) ?? [];
    list.push(item);
    map.set(item.name, list);
  }
  return map;
}

function uniqueNames(items: Occurrence[]): string[] {
  return [...new Set(items.map((item) => item.name))].sort((a, b) => a.localeCompare(b));
}

function formatOccurrence(occ: Occurrence): string {
  const source =
    occ.kind === "lean-extern"
      ? "lean"
      : occ.kind === "rust-pub-fn"
        ? "pub fn"
        : occ.kind === "rust-pub-reexport"
          ? "pub use"
          : "moved";
  const relFile = path.relative(process.cwd(), occ.file);
  return `${occ.name} ${c.dim(`(${source} ${relFile}:${occ.line})`)}`;
}

function printSection(
  title: string,
  names: string[],
  sourceMap: Map<string, Occurrence[]>,
  emptyText: string,
  color: (text: string) => string,
) {
  console.log(color(title));
  if (names.length === 0) {
    console.log(`  ${c.dim(emptyText)}`);
    console.log();
    return;
  }
  for (const name of names) {
    console.log(`  - ${formatOccurrence(sourceMap.get(name)![0]!)}`);
  }
  console.log();
}

const args = Bun.argv.slice(2);
if (args.length !== 2) usage();

const rustFile = path.resolve(args[0]!);
const leanFile = path.resolve(args[1]!);

const rustSurface = collectRustSurface(rustFile);
const leanExterns = collectLeanExterns(leanFile);

const rustByName = byName(rustSurface);
const leanByName = byName(leanExterns);

const rustNames = new Set(uniqueNames(rustSurface));
const leanNames = new Set(uniqueNames(leanExterns));

const shouldRemove = [...rustNames].filter((name) => !leanNames.has(name)).sort();
const shouldAdd = [...leanNames].filter((name) => !rustNames.has(name)).sort();
const ok = [...rustNames].filter((name) => leanNames.has(name)).sort();

console.log(c.head("are_there_extra_definitions"));
console.log(`${c.file("Rust root")}: ${rustFile}`);
console.log(`${c.file("Lean")}: ${leanFile}`);
console.log();

console.log(c.head("Summary"));
console.log(`  Lean externs: ${leanNames.size}`);
console.log(`  Rust public surface: ${rustNames.size}`);
console.log(`  ${c.err("Should be removed")}: ${shouldRemove.length}`);
console.log(`  ${c.warn("Should be added")}: ${shouldAdd.length}`);
console.log(`  ${c.ok("OK")}: ${ok.length}`);
console.log();

printSection(
  "Should be removed from Rust surface",
  shouldRemove,
  rustByName,
  "none",
  c.err,
);
printSection(
  "Should be added to Rust surface",
  shouldAdd,
  leanByName,
  "none",
  c.warn,
);
printSection("OK", ok, rustByName, "none", c.ok);
