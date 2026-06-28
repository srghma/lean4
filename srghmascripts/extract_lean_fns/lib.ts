import fs from "node:fs/promises";
import { glob } from "node:fs/promises";
import { existsSync, statSync } from "node:fs";
import path from "node:path";

export interface LeanhFunction {
  readonly name: string;
  readonly disabled: boolean;
  readonly lineNum: number;
}

export interface FileReport {
  readonly filePath: string;
  readonly found: readonly string[];
  readonly localDefinitions: readonly string[];
}

export interface FnStatusReport {
  readonly name: string;
  readonly status: "implemented" | "disabled" | "not_implemented";
  readonly emoji: string;
}

/**
 * Replaces Rust comment blocks and string literal contents with spaces
 * to isolate active function calls and declarations.
 */
export function stripRustCommentsAndStrings(content: string): string {
  let result = "";
  let i = 0;
  let insideBlockComment = false;
  let insideLineComment = false;
  let insideString = false;

  while (i < content.length) {
    const char = content[i];
    const nextChar = content[i + 1] || "";

    if (insideLineComment) {
      if (char === "\n") {
        insideLineComment = false;
        result += "\n";
      } else {
        result += " ";
      }
      i++;
    } else if (insideBlockComment) {
      if (char === "*" && nextChar === "/") {
        insideBlockComment = false;
        result += "  ";
        i += 2;
      } else {
        result += char === "\n" ? "\n" : " ";
        i++;
      }
    } else if (insideString) {
      if (char === "\\") {
        result += "  ";
        i += 2;
      } else if (char === '"') {
        insideString = false;
        result += '"';
        i++;
      } else {
        result += " ";
        i++;
      }
    } else {
      if (char === "/" && nextChar === "/") {
        insideLineComment = true;
        result += "  ";
        i += 2;
      } else if (char === "/" && nextChar === "*") {
        insideBlockComment = true;
        result += "  ";
        i += 2;
      } else if (char === '"') {
        insideString = true;
        result += '"';
        i++;
      } else {
        result += char;
        i++;
      }
    }
  }
  return result;
}

/**
 * Extracts and returns code fragments wrapped strictly inside curly braces
 */
export function extractBlockContents(content: string): string {
  let nestingLevel = 0;
  let blockContent = "";

  for (let i = 0; i < content.length; i++) {
    const char = content[i];
    if (char === "{") {
      if (nestingLevel > 0) {
        blockContent += char;
      }
      nestingLevel++;
    } else if (char === "}") {
      nestingLevel--;
      if (nestingLevel > 0) {
        blockContent += char;
      }
    } else {
      if (nestingLevel > 0) {
        blockContent += char;
      }
    }
  }
  return blockContent;
}

/**
 * Regex matches all alphanumeric symbols prefixed with lean_
 */
export function findLeanFns(text: string): readonly string[] {
  const matches = text.matchAll(/\blean_[a-zA-Z0-9_]+\b/g);
  return Array.from(matches, match => match[0]);
}

/**
 * Finds lean_* function definitions in a Rust source file.
 */
export function findLeanFunctionDefinitions(text: string): readonly string[] {
  const matches = text.matchAll(/(?:pub\s+)?(?:unsafe\s+)?fn\s+(lean_[a-zA-Z0-9_]+)\b/g);
  return Array.from(new Set(Array.from(matches, match => match[1]))).sort();
}

/**
 * Calculates 1-based line number for an index
 */
export function getLineNumber(content: string, index: number): number {
  let line = 1;
  for (let i = 0; i < index && i < content.length; i++) {
    if (content[i] === "\n") line++;
  }
  return line;
}

/**
 * Parses function declarations in leanh.rs to determine disabled states (cfg(false))
 */
export function parseLeanhDefinitions(content: string): Map<string, LeanhFunction> {
  const map = new Map<string, LeanhFunction>();

  // Group 1 matches #[cfg(false)] if present
  // Group 2 matches the actual function identifier
  const fnRegex = /(#\[cfg\(false\)\]\s*)?(?:#\[[^\]]+\]\s*)*(?:pub\s+)?(?:unsafe\s+)?fn\s+(lean_[a-zA-Z0-9_]+)\b/g;

  for (const match of content.matchAll(fnRegex)) {
    const index = match.index!;
    const disabled = match[1] !== undefined;
    const name = match[2];
    const lineNum = getLineNumber(content, index);

    map.set(name, { name, disabled, lineNum });
  }

  // leanh.rs may define families of public lean_* functions through macros,
  // e.g. define_uint_family!(u8, lean_uint8_of_nat, ...). The extractor is a
  // static text checker, so record concrete lean_* names passed to macro calls
  // as active definitions too.
  const macroCallRegex =
    /(#\[cfg\(false\)\]\s*)?(?:#\[[^\]]+\]\s*)*[A-Za-z_][A-Za-z0-9_]*!\s*\(([^;{}]*)\)\s*;/gs;

  for (const match of content.matchAll(macroCallRegex)) {
    const index = match.index!;
    const disabled = match[1] !== undefined;
    const args = match[2];
    const lineNum = getLineNumber(content, index);

    for (const name of findLeanFns(args)) {
      if (!map.has(name)) {
        map.set(name, { name, disabled, lineNum });
      }
    }
  }

  return map;
}

/**
 * Classifies a target used lean_ function against the leanh definitions map
 */
export function classifyLeanFn(fnName: string, leanhMap: Map<string, LeanhFunction>): FnStatusReport {
  const def = leanhMap.get(fnName);
  if (!def) {
    return { name: fnName, status: "not_implemented", emoji: "❌" };
  }
  if (def.disabled) {
    return { name: fnName, status: "disabled", emoji: "⚠️" };
  }
  return { name: fnName, status: "implemented", emoji: "" };
}

/**
 * Resolves glob search patterns and targets using node:fs/promises glob
 */
export async function resolveTargetFiles(
  patterns: readonly string[],
  excludePatterns: readonly string[]
): Promise<readonly string[]> {
  const globPromises = patterns.map(async (pattern) => {
    try {
      const stats = existsSync(pattern) ? statSync(pattern) : null;
      if (stats?.isDirectory()) {
        const dirPattern = path.join(pattern, "**/*.rs");
        return await Array.fromAsync(glob(dirPattern, { exclude: excludePatterns }));
      }
      return await Array.fromAsync(glob(pattern, { exclude: excludePatterns }));
    } catch {
      return [];
    }
  });

  const results = await Promise.all(globPromises);
  const flattened = results.flat().map(p => path.resolve(p));

  return Array.from(new Set(flattened)).filter(f => f.endsWith(".rs"));
}

/**
 * Parses and processes a list of file targets into completed FileReport objects
 */
export async function processFiles(
  filePaths: readonly string[]
): Promise<readonly FileReport[]> {
  const reports = await Promise.all(
    filePaths.map(async (filePath) => {
      const content = await fs.readFile(filePath, "utf8");
      const stripped = stripRustCommentsAndStrings(content);
      const bodyOnly = extractBlockContents(stripped);
      const found = Array.from(new Set(findLeanFns(bodyOnly))).sort();
      const localDefinitions = findLeanFunctionDefinitions(stripped);
      return { filePath, found, localDefinitions };
    })
  );
  return reports.filter(r => r.found.length > 0);
}

/**
 * Identifies active functions inside leanh.rs that are completely unused by the scanned codebase
 */
export function getFnsToDisable(
  leanhMap: Map<string, LeanhFunction>,
  usedFns: ReadonlySet<string>
): readonly string[] {
  return Array.from(leanhMap.values())
    .filter(def => !def.disabled && !usedFns.has(def.name))
    .map(def => def.name)
    .sort();
}
