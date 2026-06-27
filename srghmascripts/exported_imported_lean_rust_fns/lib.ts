export interface LeanOccurrence {
  type: "extern" | "export";
  symbolName: string;
  leanName: string;
  lineNum: number;
}

export interface RustSearchResult {
  filePath: string;
  lineNum: number;
  isDefinition: boolean;
  hasBody: boolean;
  snippet: string;
}

export interface ExportClassification {
  status: "correct" | "wrong_import" | "defined_in_rust" | "extern_c";
  snippet: string;
  currentImport?: string;
}

export const escapeRegExp = (str: string): string =>
  str.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

/**
 * Strips comments from Lean source code while maintaining line breaks and offsets
 */
export function stripLeanComments(content: string): string {
  let result = "";
  let i = 0;
  let insideBlockComment = 0;
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
    } else if (insideBlockComment > 0) {
      if (char === "/" && nextChar === "-") {
        insideBlockComment++;
        result += "  ";
        i += 2;
      } else if (char === "-" && nextChar === "/") {
        insideBlockComment--;
        result += "  ";
        i += 2;
      } else {
        result += char === "\n" ? "\n" : " ";
        i++;
      }
    } else if (insideString) {
      if (char === "\\") {
        result += char + nextChar;
        i += 2;
      } else if (char === '"') {
        insideString = false;
        result += char;
        i++;
      } else {
        result += char;
        i++;
      }
    } else {
      if (char === "-" && nextChar === "-") {
        insideLineComment = true;
        result += "  ";
        i += 2;
      } else if (char === "/" && nextChar === "-") {
        insideBlockComment = 1;
        result += "  ";
        i += 2;
      } else if (char === '"') {
        insideString = true;
        result += char;
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
 * Strips comments from Rust source code while maintaining line counts
 */
export function stripRustComments(content: string): string {
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
        result += char + nextChar;
        i += 2;
      } else if (char === '"') {
        insideString = false;
        result += char;
        i++;
      } else {
        result += char;
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
        result += char;
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
 * Calculates 1-based line number for a character index
 */
export function getLineNumber(content: string, index: number): number {
  let line = 1;
  for (let i = 0; i < index && i < content.length; i++) {
    if (content[i] === "\n") line++;
  }
  return line;
}

/**
 * Maps a Lean file path to the expected correct Rust import path
 */
export function getCorrectRustUsePath(leanFilePath: string, symbolName: string): string {
  let relative = leanFilePath;
  const srcIndex = leanFilePath.indexOf("/src/");
  if (srcIndex !== -1) {
    relative = leanFilePath.substring(srcIndex + 5);
  } else if (leanFilePath.startsWith("src/")) {
    relative = leanFilePath.substring(4);
  }

  relative = relative.replace(/\.lean$/, "");
  const parts = relative.split("/").filter(Boolean);
  return `crate::${parts.join("::")}::${symbolName}`;
}

/**
 * Extracts declared lean identifier after an attribute block
 */
export function findLeanName(textAfter: string): string {
  const match = textAfter.match(/\b(?:def|opaque|theorem|axiom|abbrev|instance|structure|class|constant)\s+([a-zA-Z0-9._']+)/);
  if (match) return match[1];
  const fallback = textAfter.trim().match(/^([a-zA-Z0-9._']+)/);
  return fallback ? fallback[1] : "unknown";
}

/**
 * Determines whether a function signature contains an active block body
 */
export function checkHasBody(textAfter: string): boolean {
  const braceIndex = textAfter.indexOf("{");
  const semiIndex = textAfter.indexOf(";");
  return braceIndex !== -1 && (semiIndex === -1 || braceIndex < semiIndex);
}

/**
 * Generator extracting extern and export decorators from Lean code
 */
export function* scanLeanFile(content: string): Generator<LeanOccurrence> {
  const stripped = stripLeanComments(content);

  const attrExternRegex = /\battribute\s+\[\s*extern\s+"([^"]+)"\s*\]\s*([a-zA-Z0-9._']+)/g;
  for (const match of stripped.matchAll(attrExternRegex)) {
    yield {
      type: "extern",
      symbolName: match[1],
      leanName: match[2],
      lineNum: getLineNumber(stripped, match.index!),
    };
  }

  const decoratorExternRegex = /@\[([^\]]*\bextern\s+"([^"]+)"[^\]]*)\]/g;
  for (const match of stripped.matchAll(decoratorExternRegex)) {
    const symbolName = match[2];
    const indexAfterClose = match.index! + match[0].length;
    const textAfter = stripped.substring(indexAfterClose, indexAfterClose + 300);
    yield {
      type: "extern",
      symbolName,
      leanName: findLeanName(textAfter),
      lineNum: getLineNumber(stripped, match.index!),
    };
  }

  const decoratorExportRegex = /@\[([^\]]*\bexport\s+([a-zA-Z0-9_]+)[^\]]*)\]/g;
  for (const match of stripped.matchAll(decoratorExportRegex)) {
    const symbolName = match[2];
    const indexAfterClose = match.index! + match[0].length;
    const textAfter = stripped.substring(indexAfterClose, indexAfterClose + 300);
    yield {
      type: "export",
      symbolName,
      leanName: findLeanName(textAfter),
      lineNum: getLineNumber(stripped, match.index!),
    };
  }
}

/**
 * Searches loaded Rust content for target symbols
 */
export function* findSymbolsInRust(
  filePath: string,
  content: string,
  targetSymbols: Set<string>
): Generator<{ symbol: string; result: RustSearchResult }> {
  const stripped = stripRustComments(content);
  const originalLines = content.split("\n");

  for (const symbol of targetSymbols) {
    if (!stripped.includes(symbol)) continue;

    const regex = new RegExp(`\\b${escapeRegExp(symbol)}\\b`, "g");
    for (const match of stripped.matchAll(regex)) {
      const index = match.index!;
      const lineNum = getLineNumber(stripped, index);
      const originalLine = originalLines[lineNum - 1] || "";

      const preContext = stripped.substring(Math.max(0, index - 30), index);
      const isDefinition = /\bfn\s+$/.test(preContext) || /\bfn\s*$/.test(preContext);
      const hasBody = isDefinition && checkHasBody(stripped.substring(index + symbol.length));

      yield {
        symbol,
        result: {
          filePath,
          lineNum,
          isDefinition,
          hasBody,
          snippet: originalLine.trim(),
        },
      };
    }
  }
}

/**
 * Classifies Rust occurrences of an exported symbol into the 4 validation cases
 */
export function classifyRustLine(
  line: string,
  symbolName: string,
  correctUsePath: string,
  hasBody: boolean,
  isDefinition: boolean
): ExportClassification {
  const trimmed = line.trim();

  if (isDefinition) {
    if (hasBody) {
      return { status: "defined_in_rust", snippet: trimmed };
    } else {
      return { status: "extern_c", snippet: trimmed };
    }
  }

  const isUse = /\buse\s+/.test(trimmed) && trimmed.includes(symbolName);
  if (isUse) {
    const cleanUse = trimmed.replace(/^use\s+/, "").replace(/;$/, "").trim();
    const expectedWithCrate = correctUsePath;
    const expectedNoCrate = correctUsePath.replace(/^crate::/, "");

    if (cleanUse === expectedWithCrate || cleanUse === expectedNoCrate) {
      return { status: "correct", snippet: trimmed };
    } else {
      return { status: "wrong_import", snippet: trimmed, currentImport: trimmed };
    }
  }

  return { status: "wrong_import", snippet: trimmed, currentImport: trimmed };
}
