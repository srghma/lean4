import fs from "node:fs/promises";
import path from "node:path";
import { spawn } from "node:child_process";

export const lean4Root = "/home/srghma/projects/lean4";
export const sourceRoot = "/home/srghma/projects/lean4-rust/src/rust/lean_runtime/src";
export const workRoot = path.join(lean4Root, "src/rust");
export const red = "\x1b[31m";
export const reset = "\x1b[0m";

export type FnOccurrence = {
  file: string;
  startLine: number;
  endLine: number;
  text: string;
};

export type OccurrenceKind = "body" | "decl";

export type BodyGroup = {
  normalized: string;
  text: string;
  sources: { file: string; startLine: number; endLine: number }[];
};

export type Destination = {
  kind?: string;
  targetDir: string;
  moduleFile: string;
  rootModuleFile?: string;
  prelude?: string;
};

export type MoveRustFnConfig = {
  usage: string;
  currentRoots: string[];
  ignoreDir: string;
  getDestination: (sourceOcc: FnOccurrence) => Destination;
  logScriptName: string;
  rustfmtTargets?: (destination: Destination, targetPath: string) => string[];
  generatedFallback?: {
    roots: string[];
    targetDir: string;
    moduleFile: string;
    prelude?: string;
  };
};

export function usage(message: string): never {
  console.error(message);
  process.exit(1);
}

export function isFfiPath(file: string): boolean {
  return file.includes(`${path.sep}src${path.sep}ffi${path.sep}`);
}

export function isRustFile(file: string): boolean {
  return file.endsWith(".rs") || file.endsWith(".rs_");
}

export function stripRustComments(text: string): string {
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

export function normalizeBlock(text: string): string {
  return stripRustComments(text).replace(/\s+/g, " ").trim();
}

export function ensureFnVisibility(text: string): string {
  return text.replace(
    /^(\s*)(?!pub\b)(?=(?:unsafe\s+)?(?:extern\s+"[A-Za-z0-9_-]+"\s+)?fn\b)/m,
    "$1pub(crate) ",
  );
}

function isPreambleLine(line: string): boolean {
  return (
    /^\s*$/.test(line) ||
    /^\s*#\!?\[/.test(line) ||
    /^\s*\/{2}/.test(line) ||
    /^\s*\/\*/.test(line) ||
    /^\s*\*/.test(line)
  );
}

export async function listRustFiles(root: string): Promise<string[]> {
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

export function findFunctionBodies(text: string, fnName: string): FnOccurrence[] {
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
        if (ch === "{") braceDepth++;
        else if (ch === "}") braceDepth--;
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

export function findExternDeclarations(text: string, fnName: string): FnOccurrence[] {
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

export async function findOccurrencesInRoots(
  roots: string[],
  fnName: string,
  kind: OccurrenceKind,
  ignoreDir: string,
): Promise<FnOccurrence[]> {
  const result: FnOccurrence[] = [];
  for (const root of roots) {
    const files = await listRustFiles(root);
    for (const file of files) {
      if (path.resolve(file).startsWith(path.resolve(ignoreDir))) continue;
      if (isFfiPath(file)) continue;
      const text = await fs.readFile(file, "utf8");
      const occs = kind === "body" ? findFunctionBodies(text, fnName) : findExternDeclarations(text, fnName);
      for (const occ of occs) {
        occ.file = file;
        result.push(occ);
      }
    }
  }
  return result;
}

export async function printOccurrences(label: string, occs: FnOccurrence[]) {
  const prefix = occs.length === 0 ? `${red}${label}: 0${reset}` : `\n${label}: ${occs.length}`;
  console.log(prefix);
  for (const occ of occs) {
    console.log(`- ${path.relative(lean4Root, occ.file)}:${occ.startLine}-${occ.endLine}`);
  }
}

export function removeBlock(text: string, occ: FnOccurrence): string {
  const lines = text.split(/\r?\n/);
  const before = lines.slice(0, occ.startLine - 1);
  const after = lines.slice(occ.endLine);
  const merged = [...before, ...after];
  while (merged.length > 0 && merged[merged.length - 1] === "") merged.pop();
  return merged.join("\n") + "\n";
}

export function uniqueBy<T>(items: T[], keyFn: (item: T) => string): T[] {
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

export function groupDistinctBodies(occs: FnOccurrence[]): BodyGroup[] {
  const groups = new Map<string, BodyGroup>();
  for (const occ of occs) {
    const normalized = normalizeBlock(occ.text);
    const existing = groups.get(normalized);
    if (existing) {
      existing.sources.push({
        file: path.relative(lean4Root, occ.file),
        startLine: occ.startLine,
        endLine: occ.endLine,
      });
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

export async function ensureModLine(moduleFile: string, modName: string) {
  const exists = await fs.stat(moduleFile).then((s) => s.isFile()).catch(() => false);
  const text = exists ? await fs.readFile(moduleFile, "utf8") : "";
  if (new RegExp(String.raw`^\s*pub\s+mod\s+${modName};\s*$`, "m").test(text)) return;

  const lines = text === "" ? [] : text.split(/\r?\n/);
  let insertAt = lines.length;
  while (insertAt > 0 && /^\s*$/.test(lines[insertAt - 1])) insertAt--;
  lines.splice(insertAt, 0, `pub mod ${modName};`);
  await fs.writeFile(moduleFile, `${lines.join("\n").replace(/\s*$/, "")}\n`, "utf8");
}

export async function rustfmtFiles(files: string[]) {
  const unique = [...new Set(files.map((file) => path.resolve(file)))];
  if (unique.length === 0) return;
  await new Promise<void>((resolve) => {
    const child = spawn("rustfmt", unique, {
      cwd: lean4Root,
      stdio: "inherit",
    });
    child.on("error", (err) => {
      console.error(`${red}warning:${reset} rustfmt failed to start: ${String(err)}`);
      resolve();
    });
    child.on("exit", (code) => {
      if (code !== 0) {
        console.error(`${red}warning:${reset} rustfmt failed with exit code ${code}`);
      }
      resolve();
    });
  });
}

async function appendBodiesToTarget(
  fnName: string,
  destination: Destination,
  distinctBodies: BodyGroup[],
  logScriptName: string,
) {
  await fs.mkdir(destination.targetDir, { recursive: true });
  const targetPath = path.join(destination.targetDir, `${fnName}.rs`);
  const targetExists = await fs.stat(targetPath).then((s) => s.isFile()).catch(() => false);
  const targetText = targetExists ? await fs.readFile(targetPath, "utf8") : "";

  const appendedBodies = distinctBodies
    .map((group) => {
      const files = uniqueBy(
        group.sources.map((src) => `${src.file}:${src.startLine}-${src.endLine}`),
        (x) => x,
      ).join(" and from ");
      return [
        `// appended by ${logScriptName} from ${files}`,
        ensureFnVisibility(group.text),
        "",
      ].join("\n");
    })
    .join("\n");

  let nextText = targetText.replace(/\s*$/, "");
  if (destination.prelude) {
    const prelude = destination.prelude.trimEnd();
    if (nextText === "") {
      nextText = `${prelude}\n`;
    } else if (!nextText.includes(prelude)) {
      nextText = `${prelude}\n\n${nextText}`;
    }
  }
  nextText = [nextText, "", appendedBodies, ""].join("\n");
  await fs.writeFile(targetPath, nextText, "utf8");

  await ensureModLine(destination.moduleFile, fnName);
  if (destination.rootModuleFile) {
    const moduleName = path.basename(destination.moduleFile, ".rs");
    await ensureModLine(destination.rootModuleFile, moduleName);
  }

  return targetPath;
}

async function tryGeneratedFallback(fnName: string, config: MoveRustFnConfig): Promise<boolean> {
  if (!config.generatedFallback) return false;
  const generatedOccs = await findOccurrencesInRoots(
    config.generatedFallback.roots,
    fnName,
    "body",
    config.ignoreDir,
  );
  if (generatedOccs.length === 0) return false;

  await printOccurrences("Generated fallback", generatedOccs);
  const distinctBodies = groupDistinctBodies(generatedOccs);
  const destination: Destination = {
    targetDir: config.generatedFallback.targetDir,
    moduleFile: config.generatedFallback.moduleFile,
    prelude: config.generatedFallback.prelude ?? "",
  };
  const targetPath = await appendBodiesToTarget(fnName, destination, distinctBodies, config.logScriptName);
  const rustfmtTargets = config.rustfmtTargets
    ? config.rustfmtTargets(destination, targetPath)
    : [destination.moduleFile, targetPath];
  await rustfmtFiles(rustfmtTargets);
  console.log(`\nWrote ${fnName} into ${path.relative(lean4Root, targetPath)} from generated fallback.`);
  return true;
}

export async function moveRustFn(fnName: string, config: MoveRustFnConfig) {
  const originalOccs = await findOccurrencesInRoots([sourceRoot], fnName, "body", config.ignoreDir);
  const currentBodyOccs = await findOccurrencesInRoots(
    config.currentRoots,
    fnName,
    "body",
    config.ignoreDir,
  );
  const currentDeclOccs = await findOccurrencesInRoots(
    config.currentRoots,
    fnName,
    "decl",
    config.ignoreDir,
  );

  await printOccurrences("Current tree bodies", currentBodyOccs);
  await printOccurrences("Current tree decls", currentDeclOccs);
  await printOccurrences("Original tree", originalOccs);

  if (currentBodyOccs.length === 0 && currentDeclOccs.length === 0 && originalOccs.length === 0) {
    const usedFallback = await tryGeneratedFallback(fnName, config);
    if (!usedFallback) {
      console.error(`${red}warning:${reset} no implementation or declaration found for ${fnName}`);
    }
    return;
  }

  const sourceOcc = currentBodyOccs[0] ?? originalOccs[0] ?? currentDeclOccs[0];
  if (!sourceOcc) throw new Error(`could not determine destination for ${fnName}`);

  const destination = config.getDestination(sourceOcc);
  const distinctBodies = groupDistinctBodies([...originalOccs, ...currentBodyOccs]);

  console.log(`\nDestination: ${path.relative(lean4Root, destination.targetDir)}`);
  console.log(`Distinct bodies: ${distinctBodies.length}`);
  for (const [idx, group] of distinctBodies.entries()) {
    console.log(`- body #${idx + 1}: ${group.sources.length} occurrence(s)`);
    for (const src of group.sources) {
      console.log(`  - ${src.file}:${src.startLine}-${src.endLine}`);
    }
  }

  const targetPath = await appendBodiesToTarget(fnName, destination, distinctBodies, config.logScriptName);

  for (const occ of currentBodyOccs) {
    if (path.resolve(occ.file).startsWith(path.resolve(config.ignoreDir))) continue;
    const text = await fs.readFile(occ.file, "utf8");
    await fs.writeFile(occ.file, removeBlock(text, occ), "utf8");
  }

  for (const occ of currentDeclOccs) {
    if (path.resolve(occ.file).startsWith(path.resolve(config.ignoreDir))) continue;
    const text = await fs.readFile(occ.file, "utf8");
    await fs.writeFile(occ.file, removeBlock(text, occ), "utf8");
  }

  const rustfmtTargets = config.rustfmtTargets
    ? config.rustfmtTargets(destination, targetPath)
    : [destination.moduleFile, targetPath];
  await rustfmtFiles(rustfmtTargets);

  console.log(
    `\nWrote ${fnName} into ${path.relative(lean4Root, targetPath)} and removed current-tree bodies/declarations outside ${path.relative(lean4Root, config.ignoreDir)}.`,
  );
}
