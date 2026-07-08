#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

const lean4Root = "/home/srghma/projects/lean4";
const sourceRoot = "/home/srghma/projects/lean4-rust/src/rust/lean_runtime/src";
const workRoot = path.join(lean4Root, "src/rust");
const red = "\x1b[31m";
const reset = "\x1b[0m";

const emittedFunctions = new Set([
  "lean_alloc_closure",
  "lean_alloc_ctor",
  "lean_box",
  "lean_box_float",
  "lean_box_float32",
  "lean_box_uint32",
  "lean_box_uint64",
  "lean_box_usize",
  "lean_closure_set",
  "lean_cstr_to_nat",
  "lean_ctor_get",
  "lean_ctor_get_float",
  "lean_ctor_get_float32",
  "lean_ctor_get_uint8",
  "lean_ctor_get_uint16",
  "lean_ctor_get_uint32",
  "lean_ctor_get_uint64",
  "lean_ctor_get_usize",
  "lean_ctor_release",
  "lean_ctor_set",
  "lean_ctor_set_float",
  "lean_ctor_set_float32",
  "lean_ctor_set_tag",
  "lean_ctor_set_uint8",
  "lean_ctor_set_uint16",
  "lean_ctor_set_uint32",
  "lean_ctor_set_uint64",
  "lean_ctor_set_usize",
  "lean_dec",
  "lean_dec_ref",
  "lean_dec_ref_known",
  "lean_del_object",
  "lean_float_once",
  "lean_float32_once",
  "lean_inc",
  "lean_inc_n",
  "lean_inc_ref",
  "lean_inc_ref_n",
  "lean_init_task_manager",
  "lean_initialize",
  "lean_initialize_runtime_module",
  "lean_io_mark_end_initialization",
  "lean_io_result_get_value",
  "lean_io_result_is_error",
  "lean_io_result_is_ok",
  "lean_io_result_mk_ok",
  "lean_io_result_show_error",
  "lean_is_exclusive",
  "lean_is_scalar",
  "lean_mark_persistent",
  "lean_mk_string",
  "lean_mk_string_unchecked",
  "lean_obj_once",
  "lean_obj_tag",
  "lean_run_main",
  "lean_setup_args",
  "lean_uint8_dec_eq",
  "lean_uint8_dec_le",
  "lean_uint8_dec_lt",
  "lean_uint8_of_nat_mk",
  "lean_uint8_once",
  "lean_uint8_to_nat",
  "lean_uint16_dec_eq",
  "lean_uint16_dec_le",
  "lean_uint16_dec_lt",
  "lean_uint16_of_nat",
  "lean_uint16_of_nat_mk",
  "lean_uint16_once",
  "lean_uint16_to_nat",
  "lean_uint32_dec_eq",
  "lean_uint32_dec_le",
  "lean_uint32_dec_lt",
  "lean_uint32_of_nat",
  "lean_uint32_of_nat_mk",
  "lean_uint32_once",
  "lean_uint32_to_nat",
  "lean_uint64_dec_eq",
  "lean_uint64_dec_le",
  "lean_uint64_dec_lt",
  "lean_uint64_of_nat",
  "lean_uint64_of_nat_mk",
  "lean_uint64_once",
  "lean_uint64_to_nat",
  "lean_unbox",
  "lean_unbox_float",
  "lean_unbox_float32",
  "lean_unbox_uint32",
  "lean_unbox_uint64",
  "lean_unbox_usize",
  "lean_unsigned_to_nat",
  "lean_usize_once",
  "lean_finalize_task_manager",
  "lean_internal_panic_unreachable",
]);

type FnOccurrence = {
  file: string;
  startLine: number;
  endLine: number;
  text: string;
};

type OccurrenceKind = "body" | "decl";

type Occurrence = FnOccurrence & {
  kind: OccurrenceKind;
};

type Destination = {
  targetDir: string;
  moduleFile: string;
};

function usage(): never {
  console.error("Usage: move_rust_fn_to_leanh_l1.ts <function_name>");
  process.exit(1);
}

function getDestination(fnName: string): Destination {
  const isEmitted = emittedFunctions.has(fnName);
  return isEmitted
    ? {
        targetDir: path.join(workRoot, "leanh_l1/src/emitted"),
        moduleFile: path.join(workRoot, "leanh_l1/src/emitted.rs"),
      }
    : {
        targetDir: path.join(workRoot, "leanh_l1/src/priv"),
        moduleFile: path.join(workRoot, "leanh_l1/src/priv.rs"),
    };
}

function isFfiPath(file: string): boolean {
  return file.includes(`${path.sep}src${path.sep}ffi${path.sep}`);
}

function isRustFile(file: string): boolean {
  return file.endsWith(".rs") || file.endsWith(".rs_");
}

function stripRustComments(text: string): string {
  let out = "";
  let i = 0;
  while (i < text.length) {
    const ch = text[i];
    const next = text[i + 1];

    if (ch === "/" && next === "/") {
      i += 2;
      while (i < text.length && text[i] !== "\n") i++;
      continue;
    }

    if (ch === "/" && next === "*") {
      i += 2;
      let depth = 1;
      while (i < text.length && depth > 0) {
        if (text[i] === "/" && text[i + 1] === "*") {
          depth++;
          i += 2;
          continue;
        }
        if (text[i] === "*" && text[i + 1] === "/") {
          depth--;
          i += 2;
          continue;
        }
        i++;
      }
      continue;
    }

    if (ch === "r") {
      let hashCount = 0;
      let j = i + 1;
      while (text[j] === "#") {
        hashCount++;
        j++;
      }
      if (text[j] === '"') {
        let k = j + 1;
        while (k < text.length) {
          if (text[k] === '"' && text.slice(k + 1, k + 1 + hashCount) === "#".repeat(hashCount)) {
            out += text.slice(i, k + 1 + hashCount);
            i = k + 1 + hashCount;
            break;
          }
          k++;
        }
        if (k >= text.length) {
          out += text.slice(i);
          i = text.length;
        }
        continue;
      }
    }

    if (ch === '"') {
      out += ch;
      i++;
      while (i < text.length) {
        out += text[i];
        if (text[i] === "\\" && i + 1 < text.length) {
          out += text[i + 1];
          i += 2;
          continue;
        }
        if (text[i] === '"') {
          i++;
          break;
        }
        i++;
      }
      continue;
    }

    if (ch === "'") {
      out += ch;
      i++;
      while (i < text.length) {
        out += text[i];
        if (text[i] === "\\" && i + 1 < text.length) {
          out += text[i + 1];
          i += 2;
          continue;
        }
        if (text[i] === "'") {
          i++;
          break;
        }
        i++;
      }
      continue;
    }

    out += ch;
    i++;
  }
  return out;
}

function normalizeBlock(text: string): string {
  return stripRustComments(text).replace(/\s+/g, " ").trim();
}

function isPreambleLine(line: string): boolean {
  return /^\s*$/.test(line) || /^\s*#\!?\[/.test(line) || /^\s*\/{2}/.test(line) || /^\s*\/\*/.test(line) || /^\s*\*/.test(line);
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

function findFunctionBodies(text: string, fnName: string): FnOccurrence[] {
  const lines = text.split(/\r?\n/);
  const occurrences: FnOccurrence[] = [];
  const fnRegex = new RegExp(
    String.raw`^\s*(?:pub(?:\s*\([^)]+\))?\s+)?(?:unsafe\s+)?(?:extern\s+"[A-Za-z0-9_-]+"\s+)?fn\s+${fnName}\b`,
  );

  for (let i = 0; i < lines.length; i++) {
    if (!fnRegex.test(lines[i])) continue;

    let start = i;
    while (start > 0 && isPreambleLine(lines[start - 1])) start--;

    let sawOpen = false;
    let sawSemicolon = false;
    let openLine = -1;
    let openCol = -1;
    for (let j = i; j < lines.length; j++) {
      const line = lines[j];
      for (let k = 0; k < line.length; k++) {
        const ch = line[k];
        if (ch === "{") {
          sawOpen = true;
          openLine = j;
          openCol = k;
          break;
        }
        if (ch === ";") {
          sawSemicolon = true;
          break;
        }
      }
      if (sawOpen || sawSemicolon) break;
    }
    if (!sawOpen || sawSemicolon) continue;

    let braceDepth = 0;
    let end = openLine;
    for (let j = openLine; j < lines.length; j++) {
      const line = lines[j];
      const startCol = j === openLine ? openCol : 0;
      for (let k = startCol; k < line.length; k++) {
        const ch = line[k];
        if (ch === "{") {
          braceDepth++;
        } else if (ch === "}") {
          braceDepth--;
        }
      }
      end = j;
      if (braceDepth === 0) break;
    }
    if (braceDepth !== 0) continue;

    occurrences.push({
      file: "",
      startLine: start + 1,
      endLine: end + 1,
      text: lines.slice(start, end + 1).join("\n"),
    });
  }

  return occurrences;
}

function findExternDeclarations(text: string, fnName: string): FnOccurrence[] {
  const lines = text.split(/\r?\n/);
  const occurrences: FnOccurrence[] = [];
  const fnRegex = new RegExp(
    String.raw`^\s*(?:pub(?:\s*\([^)]+\))?\s+)?(?:unsafe\s+)?(?:extern\s+"[A-Za-z0-9_-]+"\s+)?fn\s+${fnName}\b`,
  );

  for (let i = 0; i < lines.length; i++) {
    if (!fnRegex.test(lines[i])) continue;

    let sawOpen = false;
    let semicolonLine = -1;
    for (let j = i; j < lines.length; j++) {
      for (const ch of lines[j]) {
        if (ch === "{") {
          sawOpen = true;
          break;
        }
        if (ch === ";") {
          semicolonLine = j;
          break;
        }
      }
      if (sawOpen || semicolonLine !== -1) break;
    }
    if (sawOpen || semicolonLine === -1) continue;

    let start = i;
    while (start > 0 && isPreambleLine(lines[start - 1])) start--;

    occurrences.push({
      file: "",
      startLine: start + 1,
      endLine: semicolonLine + 1,
      text: lines.slice(start, semicolonLine + 1).join("\n"),
    });
  }

  return occurrences;
}

async function findOccurrences(
  root: string,
  fnName: string,
  kind: OccurrenceKind,
  ignoreDir: string,
): Promise<FnOccurrence[]> {
  const files = await listRustFiles(root);
  const result: FnOccurrence[] = [];
  for (const file of files) {
    if (path.resolve(file).startsWith(path.resolve(ignoreDir))) continue;
    if (kind === "body" && isFfiPath(file)) continue;
    if (kind === "decl" && isFfiPath(file)) continue;
    const text = await fs.readFile(file, "utf8");
    const occs = kind === "body" ? findFunctionBodies(text, fnName) : findExternDeclarations(text, fnName);
    for (const occ of occs) {
      occ.file = file;
      result.push(occ);
    }
  }
  return result;
}

async function printOccurrences(label: string, occs: FnOccurrence[]) {
  const prefix = occs.length === 0 ? `${red}${label}: 0${reset}` : `\n${label}: ${occs.length}`;
  console.log(prefix);
  for (const occ of occs) console.log(`- ${path.relative(lean4Root, occ.file)}:${occ.startLine}-${occ.endLine}`);
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

async function main() {
  const args = process.argv.slice(2);
  const fnName = args.filter((arg) => arg !== "--write")[0];
  if (!fnName) usage();

  const destination = getDestination(fnName);

  const currentBodyOccs = await findOccurrences(workRoot, fnName, "body", destination.targetDir);
  const currentDeclOccs = await findOccurrences(workRoot, fnName, "decl", destination.targetDir);
  const originalOccs = await findOccurrences(sourceRoot, fnName, "body", destination.targetDir);

  await printOccurrences("Current tree bodies", currentBodyOccs);
  await printOccurrences("Current tree decls", currentDeclOccs);
  await printOccurrences("Original tree", originalOccs);

  if (currentBodyOccs.length === 0 && currentDeclOccs.length === 0) {
    console.error(`${red}warning:${reset} no current-tree implementation found for ${fnName} in ${workRoot}`);
    return;
  }

  if (originalOccs.length === 0) {
    console.error(`${red}warning:${reset} no original implementation found for ${fnName} in ${sourceRoot}`);
  }

  const sourceOccs = originalOccs.length > 0 ? originalOccs : currentBodyOccs;
  const referenceNorm = normalizeBlock(sourceOccs[0].text);
  const sameShapeOccs = [...originalOccs, ...currentBodyOccs].filter((occ) => normalizeBlock(occ.text) === referenceNorm);
  const distinctBodies = groupDistinctBodies([...originalOccs, ...currentBodyOccs]);
  console.log(`\nDestination: ${path.relative(lean4Root, destination.targetDir)}`);
  console.log(`Distinct bodies: ${distinctBodies.length}`);
  for (const [idx, group] of distinctBodies.entries()) {
    console.log(`- body #${idx + 1}: ${group.sources.length} occurrence(s)`);
    for (const src of group.sources) {
      console.log(`  - ${src.file}:${src.startLine}-${src.endLine}`);
    }
  }

  const targetPath = path.join(destination.targetDir, `${fnName}.rs_`);
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

  const finalPath = path.join(destination.targetDir, `${fnName}.rs`);
  const finalExists = await fs.stat(finalPath).then((s) => s.isFile()).catch(() => false);
  if (!finalExists) {
    await fs.rename(targetPath, finalPath);
  }

  const libText = await fs.readFile(destination.moduleFile, "utf8");
  const modLine = `pub mod ${fnName};`;
  if (!new RegExp(String.raw`^\s*pub\s+mod\s+${fnName};\s*$`, "m").test(libText)) {
    const lines = libText.split(/\r?\n/);
    let insertAt = lines.length;
    while (insertAt > 0 && /^\s*$/.test(lines[insertAt - 1])) insertAt--;
    lines.splice(insertAt, 0, modLine);
    await fs.writeFile(destination.moduleFile, lines.join("\n") + "\n", "utf8");
  }

  for (const occ of currentBodyOccs) {
    if (path.resolve(occ.file).startsWith(path.resolve(destination.targetDir))) continue;
    if (isFfiPath(occ.file)) continue;
    const text = await fs.readFile(occ.file, "utf8");
    const updated = removeBlock(text, occ);
    await fs.writeFile(occ.file, updated, "utf8");
  }

  for (const occ of currentDeclOccs) {
    if (path.resolve(occ.file).startsWith(path.resolve(destination.targetDir))) continue;
    if (isFfiPath(occ.file)) continue;
    const text = await fs.readFile(occ.file, "utf8");
    const updated = removeBlock(text, occ);
    await fs.writeFile(occ.file, updated, "utf8");
  }

  console.log(
    `\nWrote ${fnName} into ${path.relative(lean4Root, targetPath)} and removed current-tree bodies/declarations outside leanh_l1.`,
  );
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
