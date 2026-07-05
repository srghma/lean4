#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

type SourceOrigin = "leanh" | "leanh_extra";

type DeclKind = "fn" | "struct" | "enum" | "type" | "static" | "const" | "mod";

type Decl = {
  name: string;
  kind: DeclKind;
  origin: SourceOrigin;
  file: string;
  line: number;
  text: string;
};

type RuntimeDef = {
  name: string;
  kind: DeclKind;
  file: string;
  line: number;
  text: string;
  comment: string;
};

const ROOT = path.resolve(path.join(import.meta.dir, ".."));
const SOURCE_FILES: Array<{ origin: SourceOrigin; file: string }> = [
  { origin: "leanh", file: path.join(ROOT, "src/rust/leanh/src/lib.rs") },
  { origin: "leanh_extra", file: path.join(ROOT, "src/rust/runtime/src/leanh_extra.rs") },
];
const SEARCH_ROOTS = [
  path.join(ROOT, "src/rust/runtime/src/kernel"),
  path.join(ROOT, "src/rust/runtime/src/library"),
  path.join(ROOT, "src/rust/runtime/src/runtime"),
];
const OUT_FILE = path.join(ROOT, "srghmascripts/rust_cpp_audit/leanh_runtime_duplicates.md");
const DUP_EMOJI = "🔁";

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

function extractDecls(text: string, file: string, origin: SourceOrigin): Decl[] {
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
        origin,
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

async function annotateRuntimeFile(file: string, hitsByLine: Map<number, RuntimeDef[]>): Promise<boolean> {
  const text = await fs.readFile(file, "utf8");
  const lines = text.split("\n");
  let changed = false;

  for (let i = 0; i < lines.length; i += 1) {
    const lineNo = i + 1;
    const hits = hitsByLine.get(lineNo);
    if (!hits || hits.length === 0) continue;
    const desired = hits.map((hit) => hit.comment).join("; ");
    const current = lines[i]!;
    const normalized = current.replace(/\s*\/\/\s*duplicate.*$/, "");
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
  const sourceDecls: Decl[] = [];
  for (const source of SOURCE_FILES) {
    const text = await fs.readFile(source.file, "utf8");
    sourceDecls.push(...extractDecls(text, source.file, source.origin));
  }

  const sourceNames = new Set(sourceDecls.map((decl) => decl.name));
  const sourceDeclsByName = new Map<string, Decl[]>();
  for (const decl of sourceDecls) {
    const list = sourceDeclsByName.get(decl.name) ?? [];
    list.push(decl);
    sourceDeclsByName.set(decl.name, list);
  }

  const runtimeDefs: RuntimeDef[] = [];
  const runtimeDefsByName = new Map<string, RuntimeDef[]>();
  for (const root of SEARCH_ROOTS) {
    const files = await walkFiles(root);
    for (const file of files) {
      const text = await fs.readFile(file, "utf8");
      const decls = extractDecls(text, file, "leanh");
      for (const decl of decls) {
        if (!sourceNames.has(decl.name)) continue;
        const runtimeDef: RuntimeDef = {
          name: decl.name,
          kind: decl.kind,
          file,
          line: decl.line,
          text: decl.text,
          comment: `duplicate in ${decl.origin} at line ${decl.line} (${DUP_EMOJI})`,
        };
        runtimeDefs.push(runtimeDef);
        const list = runtimeDefsByName.get(runtimeDef.name) ?? [];
        list.push(runtimeDef);
        runtimeDefsByName.set(runtimeDef.name, list);
      }
    }
  }

  const runtimeHitsByFile = new Map<string, Map<number, RuntimeDef[]>>();
  for (const def of runtimeDefs) {
    const byLine = runtimeHitsByFile.get(def.file) ?? new Map<number, RuntimeDef[]>();
    const lineHits = byLine.get(def.line) ?? [];
    lineHits.push(def);
    byLine.set(def.line, lineHits);
    runtimeHitsByFile.set(def.file, byLine);
  }

  for (const [file, hitsByLine] of runtimeHitsByFile) {
    await annotateRuntimeFile(file, hitsByLine);
  }

  const totalSource = sourceDecls.length;
  const totalRuntime = runtimeDefs.length;
  const duplicatedNames = [...runtimeDefsByName.keys()].sort();
  const unduplicatedDecls = sourceDecls.filter((decl) => !runtimeDefsByName.has(decl.name));

  const lines: string[] = [];
  lines.push(`# leanh/runtime duplicate audit`);
  lines.push("");
  lines.push(`- source declarations scanned: ${totalSource}`);
  lines.push(`- runtime definitions matched: ${totalRuntime}`);
  lines.push(`- duplicated names: ${duplicatedNames.length}`);
  lines.push(`- output annotations: duplicate in <source> at line <n> (${DUP_EMOJI})`);
  lines.push("");

  for (const source of SOURCE_FILES) {
    const decls = sourceDecls.filter((decl) => decl.origin === source.origin);
    lines.push(`## ${relativeFile(source.file)}`);
    lines.push("");
    for (const decl of decls) {
      const matches = runtimeDefsByName.get(decl.name) ?? [];
      if (matches.length > 0) {
        const matchList = matches
          .map((hit) => `${declLink(hit.file, hit.line)} (${hit.kind})`)
          .join(", ");
        lines.push(`- [x] \`${decl.name}\` (${decl.kind}) -> ${matchList}`);
      } else {
        lines.push(`- [ ] \`${decl.name}\` (${decl.kind}) -> not found in runtime/src/{kernel,library,runtime}`);
      }
    }
    lines.push("");
  }

  lines.push(`## Runtime matches`);
  lines.push("");
  for (const name of duplicatedNames) {
    const sourceList = (sourceDeclsByName.get(name) ?? [])
      .map((decl) => `${decl.origin}:${decl.kind}`)
      .join(", ");
    const matchList = (runtimeDefsByName.get(name) ?? [])
      .map((hit) => `${declLink(hit.file, hit.line)} (${hit.kind})`)
      .join(", ");
    lines.push(`- \`${name}\` <- ${sourceList} -> ${matchList}`);
  }

  lines.push("");
  lines.push(`## Not duplicated`);
  lines.push("");
  for (const decl of unduplicatedDecls.sort((a, b) => {
    if (a.origin !== b.origin) return a.origin.localeCompare(b.origin);
    return a.name.localeCompare(b.name);
  })) {
    lines.push(`- \`${decl.name}\` (${decl.origin}:${decl.kind})`);
  }

  await fs.mkdir(path.dirname(OUT_FILE), { recursive: true });
  await fs.writeFile(OUT_FILE, lines.join("\n"));

  console.log(`wrote ${OUT_FILE}`);
  console.log(`annotated ${runtimeDefs.length} runtime definitions with duplicate comments`);
}

main().catch((err) => {
  console.error(String(err?.stack ?? err));
  process.exit(1);
});
