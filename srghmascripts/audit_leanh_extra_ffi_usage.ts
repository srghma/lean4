#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

type DeclKind = "fn" | "struct" | "enum" | "type" | "static" | "const" | "mod";

type Decl = {
  name: string;
  kind: DeclKind;
  file: string;
  line: number;
  text: string;
};

type FfiHit = {
  name: string;
  kind: DeclKind;
  file: string;
  line: number;
  text: string;
  comment: string;
};

const ROOT = path.resolve(path.join(import.meta.dir, ".."));
const EXTRA_FILE = path.join(ROOT, "src/rust/runtime/src/leanh_extra.rs");
const FFI_ROOTS = [
  path.join(ROOT, "src/rust/gen_init_ffi"),
  path.join(ROOT, "src/rust/gen_lean_ffi"),
  path.join(ROOT, "src/rust/gen_std_ffi"),
  path.join(ROOT, "src/rust/lake_ffi"),
];
const OUT_FILE = path.join(ROOT, "srghmascripts/rust_cpp_audit/leanh_extra_ffi_usage.md");
const MATCH_EMOJI = "🔌";

const itemRegexes: Array<[DeclKind, RegExp]> = [
  ["fn", /^\s*(?:pub(?:\([^)]*\))?\s+)?(?:(?:unsafe|async)\s+)*fn\s+([A-Za-z_][A-Za-z0-9_]*)\b/],
  ["struct", /^\s*(?:pub(?:\([^)]*\))?\s+)?struct\s+([A-Za-z_][A-Za-z0-9_]*)\b/],
  ["enum", /^\s*(?:pub(?:\([^)]*\))?\s+)?enum\s+([A-Za-z_][A-Za-z0-9_]*)\b/],
  ["type", /^\s*(?:pub(?:\([^)]*\))?\s+)?type\s+([A-Za-z_][A-Za-z0-9_]*)\b/],
  ["static", /^\s*(?:pub(?:\([^)]*\))?\s+)?static(?:\s+mut)?\s+([A-Za-z_][A-Za-z0-9_]*)\b/],
  ["const", /^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+([A-Za-z_][A-Za-z0-9_]*)\b/],
  ["mod", /^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\b/],
];

function stripCommentsKeepLines(text: string): string {
  let out = "";
  let i = 0;
  let inLineComment = false;
  let inBlockComment = 0;
  let inString = false;

  while (i < text.length) {
    const ch = text[i]!;
    const next = text[i + 1] ?? "";

    if (inLineComment) {
      if (ch === "\n") {
        inLineComment = false;
        out += "\n";
      } else {
        out += " ";
      }
      i += 1;
      continue;
    }

    if (inBlockComment > 0) {
      if (ch === "/" && next === "*") {
        inBlockComment += 1;
        out += "  ";
        i += 2;
        continue;
      }
      if (ch === "*" && next === "/") {
        inBlockComment -= 1;
        out += "  ";
        i += 2;
        continue;
      }
      out += ch === "\n" ? "\n" : " ";
      i += 1;
      continue;
    }

    if (inString) {
      if (ch === "\\") {
        out += ch + next;
        i += 2;
        continue;
      }
      if (ch === '"') {
        inString = false;
      }
      out += ch;
      i += 1;
      continue;
    }

    if (ch === "/" && next === "/") {
      inLineComment = true;
      out += "  ";
      i += 2;
      continue;
    }
    if (ch === "/" && next === "*") {
      inBlockComment = 1;
      out += "  ";
      i += 2;
      continue;
    }
    if (ch === '"') {
      inString = true;
      out += ch;
      i += 1;
      continue;
    }

    out += ch;
    i += 1;
  }

  return out;
}

async function walkFiles(root: string): Promise<string[]> {
  const result: string[] = [];
  const stack = [root];
  while (stack.length > 0) {
    const cur = stack.pop()!;
    const entries = await fs.readdir(cur, { withFileTypes: true });
    for (const entry of entries) {
      const abs = path.join(cur, entry.name);
      if (entry.isDirectory()) stack.push(abs);
      else if (entry.isFile() && abs.endsWith(".rs")) result.push(abs);
    }
  }
  return result.sort();
}

function relativeFile(file: string): string {
  return path.relative(ROOT, file).replaceAll(path.sep, "/");
}

function extractDecls(text: string, file: string): Decl[] {
  const stripped = stripCommentsKeepLines(text);
  const lines = stripped.split("\n");
  const originalLines = text.split("\n");
  const decls: Decl[] = [];

  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i]!;
    for (const [kind, regex] of itemRegexes) {
      const match = line.match(regex);
      if (!match) continue;
      decls.push({
        name: match[1]!,
        kind,
        file,
        line: i + 1,
        text: originalLines[i]!.trim(),
      });
      break;
    }
  }

  return decls;
}

function declLink(file: string, line: number): string {
  return `[${relativeFile(file)}:${line}](${file}#L${line})`;
}

async function annotateExtraFile(file: string, hitsByLine: Map<number, FfiHit[]>): Promise<boolean> {
  const text = await fs.readFile(file, "utf8");
  const lines = text.split("\n");
  let changed = false;

  for (let i = 0; i < lines.length; i += 1) {
    const lineNo = i + 1;
    const hits = hitsByLine.get(lineNo);
    if (!hits || hits.length === 0) continue;
    const desired = hits.map((hit) => hit.comment).join("; ");
    const current = lines[i]!;
    const normalized = current.replace(/\s*\/\/\s*used.*$/, "");
    if (current.includes(desired)) continue;
    lines[i] = `${normalized} // ${desired}`;
    changed = true;
  }

  if (changed) {
    await fs.writeFile(file, lines.join("\n"));
  }

  return changed;
}

async function main() {
  const extraText = await fs.readFile(EXTRA_FILE, "utf8");
  const extraDecls = extractDecls(extraText, EXTRA_FILE);
  const extraDeclsByName = new Map<string, Decl[]>();
  for (const decl of extraDecls) {
    const list = extraDeclsByName.get(decl.name) ?? [];
    list.push(decl);
    extraDeclsByName.set(decl.name, list);
  }

  const ffiHits: FfiHit[] = [];
  const ffiHitsByName = new Map<string, FfiHit[]>();
  for (const root of FFI_ROOTS) {
    const files = await walkFiles(root);
    for (const file of files) {
      const text = await fs.readFile(file, "utf8");
      const decls = extractDecls(text, file);
      for (const decl of decls) {
        if (!extraDeclsByName.has(decl.name)) continue;
        const hit: FfiHit = {
          name: decl.name,
          kind: decl.kind,
          file,
          line: decl.line,
          text: decl.text,
          comment: `used in ${relativeFile(file)}:${decl.line} (${MATCH_EMOJI})`,
        };
        ffiHits.push(hit);
        const list = ffiHitsByName.get(hit.name) ?? [];
        list.push(hit);
        ffiHitsByName.set(hit.name, list);
      }
    }
  }

  const hitsByLine = new Map<number, FfiHit[]>();
  for (const decl of extraDecls) {
    const hits = ffiHitsByName.get(decl.name);
    if (!hits || hits.length === 0) continue;
    const list = hitsByLine.get(decl.line) ?? [];
    list.push(...hits);
    hitsByLine.set(decl.line, list);
  }

  await annotateExtraFile(EXTRA_FILE, hitsByLine);

  const extraUsed = extraDecls.filter((decl) => ffiHitsByName.has(decl.name));
  const extraUnused = extraDecls.filter((decl) => !ffiHitsByName.has(decl.name));

  const lines: string[] = [];
  lines.push(`# leanh_extra to FFI usage audit`);
  lines.push("");
  lines.push(`- source declarations scanned: ${extraDecls.length}`);
  lines.push(`- ffi definitions matched: ${ffiHits.length}`);
  lines.push(`- used names: ${ffiHitsByName.size}`);
  lines.push(`- output annotations: used in <ffi path>:<line> (${MATCH_EMOJI})`);
  lines.push("");

  lines.push(`## Used`);
  lines.push("");
  for (const decl of extraUsed.sort((a, b) => a.name.localeCompare(b.name))) {
    const matches = ffiHitsByName.get(decl.name) ?? [];
    const matchList = matches.map((hit) => `${declLink(hit.file, hit.line)} (${hit.kind})`).join(", ");
    lines.push(`- \`${decl.name}\` (${decl.kind}) -> ${matchList}`);
  }

  lines.push("");
  lines.push(`## Unused`);
  lines.push("");
  for (const decl of extraUnused.sort((a, b) => a.name.localeCompare(b.name))) {
    lines.push(`- \`${decl.name}\` (${decl.kind})`);
  }

  await fs.mkdir(path.dirname(OUT_FILE), { recursive: true });
  await fs.writeFile(OUT_FILE, lines.join("\n"));

  console.log(`wrote ${OUT_FILE}`);
  console.log(`annotated ${ffiHits.length} ffi matches in leanh_extra`);
}

main().catch((err) => {
  console.error(String(err?.stack ?? err));
  process.exit(1);
});
