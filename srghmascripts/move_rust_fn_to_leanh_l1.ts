#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

const lean4Root = "/home/srghma/projects/lean4";
const sourceRoot = "/home/srghma/projects/lean4-rust/src/rust";
const workRoot = path.join(lean4Root, "src/rust");
const targetDir = path.join(workRoot, "leanh_l1/src");

type FnOccurrence = {
  file: string;
  startLine: number;
  endLine: number;
  text: string;
};

function usage(): never {
  console.error("Usage: move_rust_fn_to_leanh_l1.ts [--write] <function_name>");
  process.exit(1);
}

function isRustFile(file: string): boolean {
  return file.endsWith(".rs") || file.endsWith(".rs_");
}

function normalizeBlock(text: string): string {
  return text.replace(/\s+/g, " ").trim();
}

async function listRustFiles(root: string): Promise<string[]> {
  const out: string[] = [];
  async function walk(dir: string) {
    for (const entry of await fs.readdir(dir, { withFileTypes: true })) {
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        await walk(full);
      } else if (entry.isFile() && isRustFile(entry.name)) {
        out.push(full);
      }
    }
  }
  await walk(root);
  return out;
}

function findFunctionBlock(text: string, fnName: string): FnOccurrence[] {
  const lines = text.split(/\r?\n/);
  const occurrences: FnOccurrence[] = [];
  const fnRegex = new RegExp(
    String.raw`^\s*(?:pub(?:\s*\([^)]+\))?\s+)?(?:unsafe\s+)?(?:extern\s+"[A-Za-z0-9_-]+"\s+)?fn\s+${fnName}\b`,
  );

  for (let i = 0; i < lines.length; i++) {
    if (!fnRegex.test(lines[i])) continue;

    let start = i;
    while (start > 0 && /^\s*#\!?\[/.test(lines[start - 1])) start--;
    while (start > 0 && /^\s*$/.test(lines[start - 1])) start--;

    let braceDepth = 0;
    let sawOpen = false;
    let end = i;
    for (let j = i; j < lines.length; j++) {
      const line = lines[j];
      for (const ch of line) {
        if (ch === "{") {
          braceDepth++;
          sawOpen = true;
        } else if (ch === "}") {
          braceDepth--;
        }
      }
      end = j;
      if (sawOpen && braceDepth === 0) break;
    }

    occurrences.push({
      file: "",
      startLine: start + 1,
      endLine: end + 1,
      text: lines.slice(start, end + 1).join("\n"),
    });
  }

  return occurrences;
}

async function findOccurrences(root: string, fnName: string): Promise<FnOccurrence[]> {
  const files = await listRustFiles(root);
  const result: FnOccurrence[] = [];
  for (const file of files) {
    if (path.resolve(file).startsWith(path.resolve(targetDir))) continue;
    const text = await fs.readFile(file, "utf8");
    for (const occ of findFunctionBlock(text, fnName)) {
      occ.file = file;
      result.push(occ);
    }
  }
  return result;
}

async function printOccurrences(label: string, occs: FnOccurrence[]) {
  console.log(`\n${label}: ${occs.length}`);
  for (const occ of occs) {
    console.log(`- ${path.relative(lean4Root, occ.file)}:${occ.startLine}-${occ.endLine}`);
    console.log(occ.text);
    console.log();
  }
}

function removeBlock(text: string, occ: FnOccurrence): string {
  const lines = text.split(/\r?\n/);
  const before = lines.slice(0, occ.startLine - 1);
  const after = lines.slice(occ.endLine);
  const merged = [...before, ...after];
  while (merged.length > 0 && merged[merged.length - 1] === "") merged.pop();
  return merged.join("\n") + "\n";
}

function uniqueBy<T>(items: T[], keyFn: (item: T) => string): T[] {
  const seen = new Set<string>();
  const out: T[] = [];
  for (const item of items) {
    const key = keyFn(item);
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(item);
  }
  return out;
}

type BodyGroup = {
  normalized: string;
  text: string;
  sources: { file: string; startLine: number; endLine: number }[];
};

function groupDistinctBodies(occs: FnOccurrence[]): BodyGroup[] {
  const groups = new Map<string, BodyGroup>();
  for (const occ of occs) {
    const normalized = normalizeBlock(occ.text);
    const existing = groups.get(normalized);
    if (existing) {
      existing.sources.push({ file: path.relative(lean4Root, occ.file), startLine: occ.startLine, endLine: occ.endLine });
    } else {
      groups.set(normalized, {
        normalized,
        text: occ.text,
        sources: [{ file: path.relative(lean4Root, occ.file), startLine: occ.startLine, endLine: occ.endLine }],
      });
    }
  }
  return [...groups.values()];
}

function printBodyGroups(groups: BodyGroup[]) {
  console.log(`\nDistinct bodies: ${groups.length}`);
  groups.forEach((group, idx) => {
    console.log(`- body #${idx + 1}: ${group.sources.length} occurrence(s)`);
    for (const src of group.sources) {
      console.log(`  - ${src.file}:${src.startLine}-${src.endLine}`);
    }
    console.log(group.text);
    console.log();
  });
}

async function main() {
  const args = process.argv.slice(2);
  const write = args.includes("--write");
  const fnName = args.filter((arg) => arg !== "--write")[0];
  if (!fnName) usage();

  const currentOccs = await findOccurrences(workRoot, fnName);
  const originalOccs = await findOccurrences(sourceRoot, fnName);

  await printOccurrences("Current tree", currentOccs);
  await printOccurrences("Original tree", originalOccs);

  if (!write) return;

  if (originalOccs.length === 0) {
    throw new Error(`No original implementation found for ${fnName} in ${sourceRoot}`);
  }

  const referenceNorm = normalizeBlock(originalOccs[0].text);
  const sameShapeOccs = [...originalOccs, ...currentOccs].filter((occ) => normalizeBlock(occ.text) === referenceNorm);
  const distinctBodies = groupDistinctBodies([...originalOccs, ...currentOccs]);
  printBodyGroups(distinctBodies);

  const targetPath = path.join(targetDir, `${fnName}.rs_`);
  await fs.mkdir(path.dirname(targetPath), { recursive: true });

  const targetExists = await fs.stat(targetPath).then((s) => s.isFile()).catch(() => false);
  const targetText = targetExists ? await fs.readFile(targetPath, "utf8") : "";

  const appendedBodies = distinctBodies
    .map((group) => {
      const files = uniqueBy(
        group.sources.map((src) => `${src.file}:${src.startLine}-${src.endLine}`),
        (x) => x,
      ).join(" and from ");
      return [`// appended by move_rust_fn_to_leanh_l1.ts from ${files}`, group.text, ""].join("\n");
    })
    .join("\n");
  const appended = [
    targetText.replace(/\s*$/, ""),
    "",
    appendedBodies,
    "",
  ].join("\n");
  await fs.writeFile(targetPath, appended, "utf8");

  for (const occ of currentOccs) {
    if (path.resolve(occ.file).startsWith(path.resolve(targetDir))) continue;
    const text = await fs.readFile(occ.file, "utf8");
    const updated = removeBlock(text, occ);
    await fs.writeFile(occ.file, updated, "utf8");
  }

  console.log(
    `\nWrote ${fnName} into ${path.relative(lean4Root, targetPath)} and removed current-tree copies outside leanh_l1.`,
  );
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
