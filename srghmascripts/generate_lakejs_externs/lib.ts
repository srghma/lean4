import fs from "node:fs/promises";
import path from "node:path";
import { glob } from "node:fs/promises";
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

export interface ExternFuncEntry {
  externIdent: string;
  body: string;
  pos?: number;
}

export type FileFunctions = Record<string, ExternFuncEntry>;

export interface DirNode {
  kind: "dir";
  dirname: string;
  children: Map<string, TreeNode>;
}

export interface LeafNode {
  kind: "leaf";
  filename: string;
  relPath: string; // root-relative path (e.g. "Init/Prelude.lean")
  moduleName: string; // e.g. "Init.Prelude"
  imports: string[];
  functions: FileFunctions;
}

export type TreeNode = DirNode | LeafNode;

const TOP_LEVEL_KEYWORDS =
  /^(?:def|opaque|abbrev|instance|axiom|constant|theorem|example|inductive|structure|class|namespace|section|end|variable|open|export|import|set_option|attribute|builtin_initialize|initialize|macro|macro_rules|syntax|notation|elab|elab_rules|register_builtin_option|deriving|private|protected|unsafe|partial|noncomputable|scoped|local)\b/;

/**
 * Extracts the declared Lean function name from the declaration header.
 */
export function extractFuncName(declText: string): string {
  const match = declText.match(
    /^(?:(?:private|protected|unsafe|partial|noncomputable|scoped|local|builtin_\w+)\s+)*(?:def|opaque|abbrev|instance|axiom|constant|theorem|example|structure|class|inductive)\s+([A-Za-z0-9_.'’]+)/
  );
  if (match) return match[1]!;

  if (/^(?:(?:private|protected|unsafe|partial|noncomputable|scoped|local)\s+)*instance\b/.test(declText)) {
    return "inst";
  }

  const fallback = declText.trim().match(/^([A-Za-z0-9_.'’]+)/);
  return fallback ? fallback[1]! : "unknown";
}

/**
 * Parses all @[extern] and attribute [extern] declarations from a Lean file.
 * Returns an object where key is name of func, value is (name of extern identificator, body of func).
 */
export function parseFileExterns(content: string): FileFunctions {
  const functions: FileFunctions = {};

  // 1. @[... extern "ident" ...]
  const externRegex = /@\[([^\]]*\bextern\s+"([^"]+)"[^\]]*)\]/g;
  let match: RegExpExecArray | null;
  while ((match = externRegex.exec(content)) !== null) {
    const externIdent = match[2]!;
    let declStart = match.index + match[0].length;
    while (declStart < content.length && /\s/.test(content[declStart]!)) declStart++;

    const lines = content.slice(declStart).split("\n");
    const declLines: string[] = [];
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i]!;
      if (i > 0 && line.length > 0 && !line.startsWith(" ") && !line.startsWith("\t")) {
        if (line.startsWith("@") || line.startsWith("/-") || line.startsWith("--") || TOP_LEVEL_KEYWORDS.test(line)) {
          break;
        }
      }
      declLines.push(line);
    }
    while (declLines.length > 0 && declLines[declLines.length - 1]!.trim() === "") {
      declLines.pop();
    }
    const body = declLines.join("\n");
    let funcName = extractFuncName(body);
    if (funcName === "unknown" || funcName === "inst") {
      funcName = `${funcName}_${externIdent}`;
    }
    functions[funcName] = { externIdent, body, pos: match.index };
  }

  // 2. attribute [... extern "ident" ...] FuncName
  const attrRegex = /\battribute\s+\[([^\]]*\bextern\s+"([^"]+)"[^\]]*)\]\s*([A-Za-z0-9_.'’]+)/g;
  while ((match = attrRegex.exec(content)) !== null) {
    const externIdent = match[2]!;
    const funcName = match[3]!;
    const body = match[0]!;
    functions[funcName] = { externIdent, body, pos: match.index };
  }

  return functions;
}

/**
 * Extracts imported module names from a Lean file.
 */
export function extractImports(content: string): string[] {
  const stripped = stripLeanComments(content);
  const imports: string[] = [];
  const importRegex = /^\s*(?:(?:public|private|meta|all_submodules)\s+)*import(?:\s+all)?\s+([A-Za-z0-9_.]+)/gm;
  let m: RegExpExecArray | null;
  while ((m = importRegex.exec(stripped)) !== null) {
    imports.push(m[1]!);
  }
  return imports;
}

/**
 * Builds a hierarchical directory/file tree from scanned file data.
 * Node is dirname, Leaf is filename.ext + info about imports + body of func.
 */
export function buildScanTree(
  files: Array<{
    relPath: string; // e.g. "Init/Data/Nat/Basic.lean"
    imports: string[];
    functions: FileFunctions;
  }>
): DirNode {
  const root: DirNode = { kind: "dir", dirname: "", children: new Map() };

  for (const file of files) {
    const segments = file.relPath.split(path.sep).join("/").split("/");
    let currDir = root;

    for (let i = 0; i < segments.length - 1; i++) {
      const seg = segments[i]!;
      if (!currDir.children.has(seg)) {
        currDir.children.set(seg, {
          kind: "dir",
          dirname: seg,
          children: new Map(),
        });
      }
      currDir = currDir.children.get(seg)! as DirNode;
    }

    const filename = segments[segments.length - 1]!;
    const moduleName = file.relPath.replace(/\.lean$/, "").split("/").join(".");
    currDir.children.set(filename, {
      kind: "leaf",
      filename,
      relPath: file.relPath,
      moduleName,
      imports: file.imports,
      functions: file.functions,
    });
  }

  return root;
}

/**
 * Recursively collects all leaves from a directory tree.
 */
export function collectLeaves(node: TreeNode): LeafNode[] {
  if (node.kind === "leaf") return [node];
  const leaves: LeafNode[] = [];
  for (const child of node.children.values()) {
    leaves.push(...collectLeaves(child));
  }
  return leaves;
}

/**
 * Transforms a tree of scanned files into an Array<[RootRelativePath, FileFunctions]>
 * sorted topologically (top is less imported e.g. Prelude.lean, bottom is most imported).
 */
export function treeToTopoSortedArray(
  tree: DirNode
): Array<[string, FileFunctions]> {
  const leaves = collectLeaves(tree);

  const moduleToLeaf = new Map<string, LeafNode>();
  const fileToLeaf = new Map<string, LeafNode>();
  for (const leaf of leaves) {
    moduleToLeaf.set(leaf.moduleName, leaf);
    fileToLeaf.set(leaf.relPath, leaf);
  }

  const prereqs = new Map<string, Set<string>>();
  const dependents = new Map<string, Set<string>>();

  for (const leaf of leaves) {
    const deps = new Set<string>();
    for (const imp of leaf.imports) {
      if (moduleToLeaf.has(imp)) {
        deps.add(moduleToLeaf.get(imp)!.relPath);
      }
    }
    prereqs.set(leaf.relPath, deps);
    if (!dependents.has(leaf.relPath)) {
      dependents.set(leaf.relPath, new Set());
    }
    for (const dep of deps) {
      if (!dependents.has(dep)) {
        dependents.set(dep, new Set());
      }
      dependents.get(dep)!.add(leaf.relPath);
    }
  }

  const inDegree = new Map<string, number>();
  for (const [file, reqs] of prereqs.entries()) {
    inDegree.set(file, reqs.size);
  }

  const compareFiles = (a: string, b: string) => {
    const aIsPrelude = a.endsWith("Prelude.lean");
    const bIsPrelude = b.endsWith("Prelude.lean");
    if (aIsPrelude && !bIsPrelude) return -1;
    if (!aIsPrelude && bIsPrelude) return 1;

    const aDepCount = dependents.get(a)?.size ?? 0;
    const bDepCount = dependents.get(b)?.size ?? 0;
    if (aDepCount !== bDepCount) return bDepCount - aDepCount;

    return a.localeCompare(b);
  };

  const queue: string[] = [];
  for (const [file, deg] of inDegree.entries()) {
    if (deg === 0) queue.push(file);
  }
  queue.sort(compareFiles);

  const sortedFiles: string[] = [];
  while (queue.length > 0) {
    const curr = queue.shift()!;
    sortedFiles.push(curr);
    for (const next of dependents.get(curr) || []) {
      const d = inDegree.get(next)! - 1;
      inDegree.set(next, d);
      if (d === 0) {
        queue.push(next);
        queue.sort(compareFiles);
      }
    }
  }

  if (sortedFiles.length < leaves.length) {
    const visited = new Set(sortedFiles);
    for (const leaf of leaves) {
      if (!visited.has(leaf.relPath)) {
        sortedFiles.push(leaf.relPath);
      }
    }
  }

  return sortedFiles.map((relPath) => {
    const leaf = fileToLeaf.get(relPath)!;
    return [leaf.relPath, leaf.functions];
  });
}

function matchBraces(text: string, openIdx: number): string | null {
  let depth = 0;
  for (let i = openIdx; i < text.length; i++) {
    if (text[i] === "{") depth++;
    else if (text[i] === "}") {
      depth--;
      if (depth === 0) return text.slice(openIdx, i + 1);
    }
  }
  return null;
}

/**
 * Loads all C/C++ function definitions from runtime and kernel source files.
 */
export async function loadCppDefinitions(srcDir: string): Promise<Map<string, string>> {
  const cppDefs = new Map<string, string>();
  for await (const file of glob(`${srcDir}/{include,runtime,kernel}/**/*.{h,cpp,c}`)) {
    const content = await fs.readFile(file, "utf8");
    const re = /\b(lean_\w+)\s*\(/g;
    let m: RegExpExecArray | null;
    while ((m = re.exec(content)) !== null) {
      const fnName = m[1]!;
      const nameIdx = m.index;
      let sigStart = nameIdx;
      while (sigStart > 0 && !";{}\n\r".includes(content[sigStart - 1]!)) {
        sigStart--;
      }
      const prefix = content.slice(sigStart, nameIdx).trim();
      if (!prefix || /^(?:return|if|while|for|else|switch|case|sizeof|new|delete|typedef|using)\b/.test(prefix)) {
        continue;
      }
      const parenOpen = nameIdx + fnName.length + (m[0].length - fnName.length - 1);
      let parenDepth = 0;
      let parenClose = -1;
      for (let i = parenOpen; i < content.length; i++) {
        if (content[i] === "(") parenDepth++;
        else if (content[i] === ")") {
          parenDepth--;
          if (parenDepth === 0) {
            parenClose = i;
            break;
          }
        }
      }
      if (parenClose === -1) continue;

      let k = parenClose + 1;
      while (k < content.length && /\s/.test(content[k]!)) k++;
      const tailMatch = content.slice(k, k + 60).match(/^(?:const|noexcept(?:\([^)]*\))?|LEAN_[A-Z_]+|\s+)+/);
      if (tailMatch) k += tailMatch[0].length;
      while (k < content.length && /\s/.test(content[k]!)) k++;

      if (content[k] === "{") {
        const bodyWithBraces = matchBraces(content, k);
        if (bodyWithBraces) {
          const full = content.slice(sigStart, k) + bodyWithBraces;
          if (!cppDefs.has(fnName) || full.length > (cppDefs.get(fnName)?.length ?? 0)) {
            cppDefs.set(fnName, full.trim());
          }
        }
      }
    }
  }
  return cppDefs;
}

/**
 * Loads existing LakeJs JS implementations from already written files.
 */
export async function loadExistingLakeJsImplementations(
  dir: string
): Promise<{ byModule: Map<string, Map<string, string>>; global: Map<string, string> }> {
  const byModule = new Map<string, Map<string, string>>();
  const global = new Map<string, string>();

  for await (const file of glob(`${dir}/**/*.lean`)) {
    const rel = path.relative(dir, file);
    if (!rel.includes("/")) continue; // skip top-level Init.lean, Std.lean, Lean.lean

    const content = await fs.readFile(file, "utf8");
    const fileMap = new Map<string, string>();

    const re = /^def\s+(lean_\w+)\s*:=\s*/gm;
    let m: RegExpExecArray | null;
    while ((m = re.exec(content)) !== null) {
      const ident = m[1]!;
      const afterAssign = m.index + m[0].length;
      let endIdx = afterAssign;
      if (content.startsWith("[", afterAssign)) {
        let depth = 0;
        for (let i = afterAssign; i < content.length; i++) {
          if (content[i] === "[") depth++;
          else if (content[i] === "]") {
            depth--;
            if (depth === 0) {
              endIdx = i + 1;
              break;
            }
          }
        }
      } else {
        const nextNl = content.indexOf("\n", afterAssign);
        endIdx = nextNl !== -1 ? nextNl : content.length;
      }
      let impl = content.slice(afterAssign, endIdx).trim();
      if (impl.startsWith("[JS|")) {
        impl = "[JS_EXPR|" + impl.slice(4);
      }
      fileMap.set(ident, impl);
      if (!global.has(ident)) {
        global.set(ident, impl);
      }
    }
    byModule.set(rel, fileMap);
  }

  return { byModule, global };
}

/**
 * Formats a block of code (Lean or C++) commented out with `-- `.
 */
function formatCommentedCodeBlock(lang: string, code: string): string[] {
  const lines: string[] = [`-- \`\`\`${lang}`];
  for (const l of code.split("\n")) {
    lines.push(`-- ${l}`);
  }
  lines.push(`-- \`\`\``);
  return lines;
}

/**
 * Generates the LakeJs Lean file content with Lean & C++ implementations commented above each definition.
 */
export function generateLakeJsContent(
  sortedArray: Array<[string, FileFunctions]>,
  cppDefs: Map<string, string> = new Map(),
  existingImpls: { byModule: Map<string, Map<string, string>>; global: Map<string, string> } = {
    byModule: new Map(),
    global: new Map(),
  }
): string {
  const lines: string[] = ["import LakeJs.Js", ""];
  const seenExterns = new Set<string>();

  for (const [relPath, functions] of sortedArray) {
    const entries = Object.entries(functions);
    if (entries.length === 0) continue;

    // Order entries by their original position in file
    entries.sort((a, b) => (a[1].pos ?? 0) - (b[1].pos ?? 0));

    // Group by externIdent in order of first appearance
    const groupedByExtern = new Map<string, Array<{ funcName: string; body: string; pos: number }>>();
    for (const [funcName, entry] of entries) {
      if (!groupedByExtern.has(entry.externIdent)) {
        groupedByExtern.set(entry.externIdent, []);
      }
      groupedByExtern.get(entry.externIdent)!.push({
        funcName,
        body: entry.body,
        pos: entry.pos ?? 0,
      });
    }

    const moduleName = relPath.replace(/\.lean$/, "").split("/").join(".");
    lines.push("-- ============");
    lines.push(`-- ${moduleName}`);
    lines.push("-- ============");
    lines.push("");

    const moduleExistingMap = existingImpls.byModule.get(relPath);

    for (const [externIdent, decls] of groupedByExtern.entries()) {
      const isDuplicate = seenExterns.has(externIdent);

      // Print all Lean + C++ pairs for this extern
      for (let i = 0; i < decls.length; i++) {
        if (i > 0) {
          lines.push("--");
        }
        const decl = decls[i]!;
        lines.push(...formatCommentedCodeBlock("lean", decl.body));
        lines.push("--");

        const cppImpl = cppDefs.get(externIdent);
        if (cppImpl) {
          lines.push(...formatCommentedCodeBlock("cpp", cppImpl));
        } else {
          lines.push("-- ```cpp");
          lines.push("-- // (no C++ implementation found)");
          lines.push("-- ```");
        }
      }

      // Determine implementation expression
      let impl =
        moduleExistingMap?.get(externIdent) ??
        existingImpls.global.get(externIdent);

      if (!impl) {
        impl = `[JS_EXPR|throw new Error("${externIdent} is not implemented")]`;
      }

      if (isDuplicate) {
        lines.push(`-- duplicate of ${externIdent}:`);
        lines.push(`-- def ${externIdent} := ${impl}`);
        lines.push("");
      } else {
        seenExterns.add(externIdent);
        lines.push(`def ${externIdent} := ${impl}`);
        lines.push("");
      }
    }
  }

  return lines.join("\n");
}
