/**
 * Borrow-annotation consistency between CPP (`b_lean_obj_arg`) and Lean (`@&`).
 *
 * Reuses the comment strippers / helpers from the sibling audit script.
 * The CPP `*lean_obj_arg` typedefs are all `lean_object *` at the ABI level; they only
 * *document* the calling convention (owned vs borrowed). This library extracts that
 * documentation from the C headers and the `@&` markers from Lean and diffs them.
 */

import {
  stripLeanComments,
  stripRustComments, // C uses the same `//` and block comment syntax as Rust
  getLineNumber,
} from "../exported_imported_lean_rust_fns/lib";

// ─────────────────────────────────────────────────────────────────────────────
// Types
// ─────────────────────────────────────────────────────────────────────────────

/** How a C parameter/return type documents ownership. */
export type CppArgKind = "b" | "u" | "owned" | "other";

export interface CppArg {
  /** Normalized type text with the parameter name stripped (e.g. `b_lean_obj_arg`, `unsigned`). */
  raw: string;
  kind: CppArgKind;
}

export interface CppFn {
  fnName: string;
  returnType: string; // normalized
  returnBorrowed: boolean; // returns b_lean_obj_res
  args: CppArg[];
  hasBody: boolean; // definition (`{`) vs re-export/declaration (`;`)
  filePath: string; // repo-relative
  lineNum: number;
}

/** Per Lean runtime value parameter: Borrowed (`@&`) or Not. */
export type LeanBorrow = "B" | "N";

export interface LeanExtern {
  symbolName: string; // the C symbol from @[extern "..."]
  leanName: string;
  params: LeanBorrow[]; // runtime value params, in order, after dropping erased type/prop args
  parseOk: boolean; // false => attribute-form / could not parse the signature
  filePath: string;
  lineNum: number;
  rawSig: string; // the captured signature text (for reporting)
}

// ─────────────────────────────────────────────────────────────────────────────
// Small bracket-aware helpers
// ─────────────────────────────────────────────────────────────────────────────

/** Split `s` on top-level occurrences of `sep` (a literal string), ignoring bracketed regions. */
export function splitTopLevel(s: string, sep: string, brackets: Record<string, string>): string[] {
  const closers = new Set(Object.values(brackets));
  const parts: string[] = [];
  const stack: string[] = [];
  let cur = "";
  let i = 0;
  while (i < s.length) {
    const ch = s[i]!;
    if (stack.length === 0 && s.startsWith(sep, i)) {
      parts.push(cur);
      cur = "";
      i += sep.length;
      continue;
    }
    if (brackets[ch]) {
      stack.push(brackets[ch]!);
      cur += ch;
    } else if (closers.has(ch)) {
      if (stack[stack.length - 1] === ch) stack.pop();
      cur += ch;
    } else {
      cur += ch;
    }
    i++;
  }
  parts.push(cur);
  return parts;
}

/** Index (depth-0) of the first `needle` not followed by any char in `notFollowedBy`. */
function indexOfTopLevel(
  s: string,
  needle: string,
  brackets: Record<string, string>,
  notFollowedBy = "",
): number {
  const closers = new Set(Object.values(brackets));
  const stack: string[] = [];
  let i = 0;
  while (i < s.length) {
    const ch = s[i]!;
    if (stack.length === 0 && s.startsWith(needle, i)) {
      const next = s[i + needle.length] ?? "";
      if (!notFollowedBy.includes(next)) return i;
    }
    if (brackets[ch]) stack.push(brackets[ch]!);
    else if (closers.has(ch)) {
      if (stack[stack.length - 1] === ch) stack.pop();
    }
    i++;
  }
  return -1;
}

/** Top-level bracket groups in order, each `{ open, inner }`. Bare (non-bracket) text is ignored. */
function topLevelGroups(s: string, brackets: Record<string, string>): { open: string; inner: string }[] {
  const groups: { open: string; inner: string }[] = [];
  const closerOf = brackets;
  let i = 0;
  while (i < s.length) {
    const ch = s[i]!;
    if (closerOf[ch]) {
      const close = closerOf[ch]!;
      // find matching close (nested, same bracket family only need this bracket)
      const stack: string[] = [close];
      let j = i + 1;
      while (j < s.length && stack.length) {
        const cj = s[j]!;
        if (brackets[cj]) stack.push(brackets[cj]!);
        else if (Object.values(brackets).includes(cj)) {
          if (stack[stack.length - 1] === cj) stack.pop();
        }
        j++;
      }
      groups.push({ open: ch, inner: s.slice(i + 1, j - 1) });
      i = j;
    } else {
      i++;
    }
  }
  return groups;
}

export function normalizeType(s: string): string {
  return s
    .replace(/\s+/g, " ")
    .replace(/\s*([*&])\s*/g, "$1")
    .trim();
}

// ─────────────────────────────────────────────────────────────────────────────
// CPP parsing
// ─────────────────────────────────────────────────────────────────────────────

const CPP_BRACKETS: Record<string, string> = { "(": ")", "[": "]", "{": "}", "<": ">" };

const CPP_QUALIFIERS = new Set([
  "static",
  "inline",
  "extern",
  "LEAN_EXPORT",
  "LEAN_EXPORT_WEAK",
  "LEAN_ALWAYS_INLINE",
  "LEAN_ALWAYS_INLINE_FLATTEN",
  "constexpr",
  "virtual",
  "explicit",
  "friend",
  "noexcept",
  "LEAN_NORETURN",
]);

// The runtime uses both the `lean_`-prefixed C typedefs (lean.h) and the shorter
// `namespace lean` aliases (object.h: `typedef object * b_obj_arg;` etc.).
export function classifyCppType(raw: string): CppArgKind {
  if (/\b(?:b_lean_obj_res|b_lean_obj_arg|b_obj_res|b_obj_arg)\b/.test(raw)) return "b";
  if (/\b(?:u_lean_obj_arg|u_obj_arg)\b/.test(raw)) return "u";
  if (/\b(?:lean_obj_res|lean_obj_arg|obj_res|obj_arg)\b/.test(raw)) return "owned";
  return "other";
}

/** Strip the trailing parameter name from a C parameter, returning the (normalized) type. */
function cppParamType(part: string): string {
  const p = part.trim().replace(/=.*$/, "").trim(); // drop rare defaults
  const m = p.match(/^(.*?)(\b[A-Za-z_]\w*)\s*$/);
  if (m && m[1]!.trim()) return normalizeType(m[1]!);
  return normalizeType(p);
}

function splitCppArgs(inner: string): CppArg[] {
  const args: CppArg[] = [];
  for (const partRaw of splitTopLevel(inner, ",", CPP_BRACKETS)) {
    const part = partRaw.trim();
    if (!part || part === "void") continue;
    args.push({ raw: cppParamType(part), kind: classifyCppType(part) });
  }
  return args;
}

/** Blank out preprocessor directives (and `\`-continued lines), preserving offsets. */
function stripPreprocessor(s: string): string {
  const lines = s.split("\n");
  let cont = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    if (cont || /^\s*#/.test(line)) {
      cont = /\\\s*$/.test(line);
      lines[i] = " ".repeat(line.length);
    }
  }
  return lines.join("\n");
}

/** Match the `(` at `openIdx`, returning [innerText, indexAfterClose]. Counts `()` only. */
function matchParens(text: string, openIdx: number): [string, number] {
  let depth = 0;
  for (let i = openIdx; i < text.length; i++) {
    const c = text[i];
    if (c === "(") depth++;
    else if (c === ")") {
      depth--;
      if (depth === 0) return [text.slice(openIdx + 1, i), i + 1];
    }
  }
  return [text.slice(openIdx + 1), text.length];
}

/**
 * Parse every C function *declaration or definition* whose name starts with `lean_`.
 * Distinguishes decl/def by the trailing `;` vs `{`. Ignores calls and expressions.
 */
export function parseCppFunctions(content: string, filePath: string): CppFn[] {
  const text = stripPreprocessor(stripRustComments(content));
  const out: CppFn[] = [];
  const nameRe = /\blean_\w+/g;
  let m: RegExpExecArray | null;
  while ((m = nameRe.exec(text))) {
    const nameStart = m.index;
    const fnName = m[0];

    // Require `(` right after the name (only whitespace allowed between).
    let k = nameStart + fnName.length;
    while (k < text.length && /\s/.test(text[k]!)) k++;
    if (text[k] !== "(") continue;

    // Backward scan to the nearest statement boundary to isolate the return type / qualifiers.
    let j = nameStart - 1;
    while (j >= 0 && !";{}".includes(text[j]!)) j--;
    const prefixRaw = text.slice(j + 1, nameStart);

    // Reject calls / expressions: a return type never contains these.
    // (`<`/`>` would be a comparison here — `lean_` C-ABI fns have no templated returns.)
    if (/[=()<>,]/.test(prefixRaw)) continue;
    if (/\b(return|if|while|for|else|switch|case|sizeof|new|delete|typedef|using)\b/.test(prefixRaw)) continue;

    const prefix = prefixRaw
      .replace(/\btemplate\s*<[^>]*>/g, " ")
      .replace(/"C"/g, " ")
      .split(/\s+/)
      .filter((t) => t && !CPP_QUALIFIERS.has(t))
      .join(" ")
      .trim();
    if (!prefix) continue; // no return type => this was a statement-level call

    const [inner, afterIdx] = matchParens(text, k);

    // Skip trailing specifiers, then require `{` (definition) or `;` (declaration).
    const tail = text.slice(afterIdx, afterIdx + 60);
    const tm = tail.match(/^\s*(?:const\s+|noexcept\s*(?:\([^)]*\))?\s*|override\s+|LEAN_[A-Z_]+\s+)*/);
    const bodyIdx = afterIdx + (tm ? tm[0].length : 0);
    const bodyChar = text[bodyIdx];
    if (bodyChar !== "{" && bodyChar !== ";") continue;

    out.push({
      fnName,
      returnType: normalizeType(prefix),
      returnBorrowed: /\b(?:b_lean_obj_res|b_obj_res)\b/.test(prefix),
      args: splitCppArgs(inner),
      hasBody: bodyChar === "{",
      filePath,
      lineNum: getLineNumber(text, nameStart),
    });
  }
  return out;
}

// ─────────────────────────────────────────────────────────────────────────────
// Lean parsing
// ─────────────────────────────────────────────────────────────────────────────

const LEAN_BRACKETS: Record<string, string> = { "(": ")", "[": "]", "{": "}", "⦃": "⦄" };

const LEAN_KEYWORDS = "def|opaque|abbrev|instance|axiom|constant|theorem|example";
const LEAN_MODIFIER = /^\s*(?:@\[[^\]]*\]\s*|private\s+|protected\s+|unsafe\s+|partial\s+|noncomputable\s+|scoped\s+|local\s+|builtin_\w+\s+)*/;

function isTypeSort(t: string): boolean {
  const s = t.trim().replace(/^@&\s*/, "");
  return /^(Type|Sort|Prop)\b/.test(s) || s === "" ;
}

function isBorrowed(typeText: string): boolean {
  return /^@&/.test(typeText.trim());
}

interface LeanParam {
  borrowed: boolean;
  erased: boolean;
}

/** Turn one bracket group (or its arrow-component equivalent) into ordered params. */
function groupToParams(open: string, inner: string): LeanParam[] {
  if (open === "[") {
    // instance/dictionary argument — a runtime value, rarely borrowed
    const t = inner.includes(":") ? inner.slice(inner.indexOf(":") + 1) : inner;
    return [{ borrowed: isBorrowed(t), erased: false }];
  }
  const colon = indexOfTopLevel(inner, ":", LEAN_BRACKETS, "=");
  if (colon === -1) {
    if (open === "{" || open === "⦃") return []; // `{α}` implicit type shorthand → erased
    // `(@& String)` style parenthesized type → one anonymous param
    return [{ borrowed: isBorrowed(inner), erased: isTypeSort(inner) }];
  }
  const names = inner.slice(0, colon).trim().split(/\s+/).filter(Boolean);
  const type = inner.slice(colon + 1);
  const borrowed = isBorrowed(type);
  const erased = isTypeSort(type);
  const count = Math.max(1, names.length);
  return Array.from({ length: count }, () => ({ borrowed, erased }));
}

/** Split a `→`-chain into components; last is the return type. */
function arrowComponents(typeSection: string): string[] {
  const normalized = typeSection.replace(/->/g, "→");
  return splitTopLevel(normalized, "→", LEAN_BRACKETS);
}

/** Parse one arrow component (a param position from the type ascription) into params. */
function arrowComponentToParams(comp: string): LeanParam[] {
  const c = comp.trim();
  if (!c) return [];
  const groups = topLevelGroups(c, LEAN_BRACKETS);
  // Full-wrap binder/type like `(n : Nat)`, `(@& String)`, `{α : Type}`, `[Monad m]`
  if (groups.length === 1 && `${groups[0]!.open}${groups[0]!.inner}`.length + 1 === c.length) {
    return groupToParams(groups[0]!.open, groups[0]!.inner);
  }
  // Bare type expression (possibly a type application) → one anonymous param
  return [{ borrowed: isBorrowed(c), erased: isTypeSort(c) }];
}

/** Capture the signature text following a declaration name, up to the body/next decl. */
function captureSignature(textAfterName: string): string {
  const window = textAfterName.slice(0, 2500);
  const assign = indexOfTopLevel(window, ":=", LEAN_BRACKETS);
  const whereM = findTopLevelWhere(window);
  const nextDecl = findNextDecl(window);
  const ends = [assign, whereM, nextDecl].filter((x) => x >= 0);
  const end = ends.length ? Math.min(...ends) : window.length;
  return window.slice(0, end).trim();
}

function findTopLevelWhere(s: string): number {
  const closers = new Set(Object.values(LEAN_BRACKETS));
  const stack: string[] = [];
  for (let i = 0; i < s.length; i++) {
    const ch = s[i]!;
    if (stack.length === 0 && /\bwhere\b/.test(s.slice(i, i + 6)) && s.startsWith("where", i)) {
      const before = s[i - 1] ?? " ";
      const after = s[i + 5] ?? " ";
      if (/\s/.test(before) && /[\s]/.test(after)) return i;
    }
    if (LEAN_BRACKETS[ch]) stack.push(LEAN_BRACKETS[ch]!);
    else if (closers.has(ch)) {
      if (stack[stack.length - 1] === ch) stack.pop();
    }
  }
  return -1;
}

/** A newline followed (after optional spaces) by a new top-level declaration ends a body-less sig. */
function findNextDecl(s: string): number {
  const extra =
    "structure|class|inductive|end|namespace|section|variable|open|import|mutual|deriving|" +
    "unsafe|partial|noncomputable|private|protected|scoped|local|set_option|attribute|" +
    "builtin_initialize|initialize|macro|macro_rules|elab|elab_rules|syntax|notation|register_builtin_option";
  const re = new RegExp(`\\n[ \\t]*(?:@\\[|/-|(?:${LEAN_KEYWORDS}|${extra})\\b)`);
  const m = re.exec(s);
  return m ? m.index : -1;
}

/** Parse the signature that follows a matched `@[extern "sym"]`. */
export function parseLeanExternSignature(
  textAfterAttr: string,
  symbolName: string,
  filePath: string,
  lineNum: number,
): LeanExtern {
  const base: LeanExtern = { symbolName, leanName: "unknown", params: [], parseOk: false, filePath, lineNum, rawSig: "" };

  const modMatch = textAfterAttr.match(LEAN_MODIFIER);
  const afterMods = textAfterAttr.slice(modMatch ? modMatch[0].length : 0);
  const declMatch = afterMods.match(new RegExp(`^(?:${LEAN_KEYWORDS})\\s+([A-Za-z0-9_.'’]+)`));
  if (!declMatch) return base; // e.g. attribute-form or macro — cannot parse args here

  const leanName = declMatch[1]!;
  const sig = captureSignature(afterMods.slice(declMatch[0].length));

  // Split binders (before ascription `:`) from the type ascription (arrow chain).
  const colon = indexOfTopLevel(sig, ":", LEAN_BRACKETS, "=");
  const binderSection = colon === -1 ? sig : sig.slice(0, colon);
  const typeSection = colon === -1 ? "" : sig.slice(colon + 1);

  const params: LeanParam[] = [];
  for (const g of topLevelGroups(binderSection, LEAN_BRACKETS)) {
    params.push(...groupToParams(g.open, g.inner));
  }
  if (typeSection.trim()) {
    const comps = arrowComponents(typeSection);
    // last component is the true return type
    for (let i = 0; i < comps.length - 1; i++) {
      params.push(...arrowComponentToParams(comps[i]!));
    }
  }

  const runtime = params.filter((p) => !p.erased);
  return {
    symbolName,
    leanName,
    params: runtime.map((p) => (p.borrowed ? "B" : "N")),
    parseOk: true,
    filePath,
    lineNum,
    rawSig: sig.replace(/\s+/g, " ").trim(),
  };
}

/**
 * Scan a Lean file for `@[extern "sym"]`-decorated declarations and parse their signatures.
 * Also records `attribute [extern "sym"] Name` forms as unparseable (args live elsewhere).
 */
export function parseLeanExterns(content: string, filePath: string): LeanExtern[] {
  const stripped = stripLeanComments(content);
  const out: LeanExtern[] = [];

  // Inline `@[... extern "sym" ...]` on a declaration.
  const decoRe = /@\[([^\]]*\bextern\s+"([^"]+)"[^\]]*)\]/g;
  let m: RegExpExecArray | null;
  while ((m = decoRe.exec(stripped))) {
    const symbolName = m[2]!;
    const after = stripped.slice(m.index + m[0].length);
    const lineNum = getLineNumber(stripped, m.index);
    out.push(parseLeanExternSignature(after, symbolName, filePath, lineNum));
  }

  // Detached `attribute [extern "sym"] Name` — signature is elsewhere; record as unparsed.
  const attrRe = /\battribute\s+\[([^\]]*\bextern\s+"([^"]+)"[^\]]*)\]\s*([A-Za-z0-9_.'’]+)/g;
  while ((m = attrRe.exec(stripped))) {
    out.push({
      symbolName: m[2]!,
      leanName: m[3]!,
      params: [],
      parseOk: false,
      filePath,
      lineNum: getLineNumber(stripped, m.index),
      rawSig: `attribute [extern "${m[2]}"] ${m[3]}`,
    });
  }

  return out;
}

// ─────────────────────────────────────────────────────────────────────────────
// Canonicalization & comparison
// ─────────────────────────────────────────────────────────────────────────────

/** Among all CPP entries for a symbol, choose the one carrying the most borrow documentation. */
export function pickCanonicalCppFn(entries: CppFn[]): CppFn {
  const richness = (f: CppFn) => f.args.filter((a) => a.kind !== "other").length + (f.returnBorrowed ? 1 : 0);
  return [...entries].sort((a, b) => {
    const dr = richness(b) - richness(a);
    if (dr) return dr;
    const ha = a.filePath.endsWith(".h") ? 1 : 0;
    const hb = b.filePath.endsWith(".h") ? 1 : 0;
    return hb - ha;
  })[0]!;
}

/**
 * Collapse ABI-synonyms so type-level drift ignores spelling differences:
 *   - the borrow/owned typedefs (`*_obj_arg`, `*_obj_res`) are all `object *`
 *   - `obj` / `object` / `lean_object` are the same base type
 *   - `uint8`/`uint16`/... alias the `_t` forms
 */
function objNorm(t: string): string {
  let n = normalizeType(t).replace(/^const\s*/, "");
  // Whole-type object-pointer typedefs → a single object pointer.
  n = n.replace(
    /^(?:lean_obj_arg|b_lean_obj_arg|u_lean_obj_arg|lean_obj_res|b_lean_obj_res|obj_arg|b_obj_arg|u_obj_arg|obj_res|b_obj_res)$/,
    "object*",
  );
  // Base object spellings (keeps any trailing `*`s: `obj**` ≡ `lean_object**`).
  n = n.replace(/\b(?:lean_object|object|obj)\b/g, "object");
  // Elaborated type specifiers are cosmetic.
  n = n.replace(/\b(?:struct|union|enum)\s+/g, "");
  // Integer typedef aliases (int.h) and the platform-width spellings the runtime treats as equal.
  n = n.replace(/\b(u?int)(8|16|32|64)\b/g, "$1$2_t");
  n = n.replace(/\busize\b/g, "size_t").replace(/\bisize\b/g, "ptrdiff_t");
  n = n.replace(/\bunsigned int\b/g, "uint32_t").replace(/\bunsigned\b/g, "uint32_t");
  return n;
}

function typeLevelSig(fn: CppFn): string {
  return `${objNorm(fn.returnType)}(${fn.args.map((a) => objNorm(a.raw)).join(",")})`;
}

export interface CppDrift {
  fnName: string;
  variants: { sig: string; entries: CppFn[] }[];
}

/** Point 3: same C name whose *type-level* signature disagrees between occurrences. */
export function findCppSignatureDrift(fns: CppFn[]): CppDrift[] {
  const byName = new Map<string, CppFn[]>();
  for (const f of fns) {
    const list = byName.get(f.fnName) ?? [];
    list.push(f);
    byName.set(f.fnName, list);
  }
  const drift: CppDrift[] = [];
  for (const [fnName, entries] of byName) {
    if (entries.length < 2) continue;
    const variantMap = new Map<string, CppFn[]>();
    for (const e of entries) {
      const sig = typeLevelSig(e);
      const l = variantMap.get(sig) ?? [];
      l.push(e);
      variantMap.set(sig, l);
    }
    if (variantMap.size > 1) {
      drift.push({ fnName, variants: [...variantMap].map(([sig, es]) => ({ sig, entries: es })) });
    }
  }
  return drift.sort((a, b) => a.fnName.localeCompare(b.fnName));
}

export interface Finding {
  position: number;
  direction: "cpp_borrowed_lean_not" | "lean_borrowed_cpp_not";
  cppArg: CppArg;
  leanBorrow: LeanBorrow;
  confidence: "high" | "low";
}

export interface Comparison {
  symbolName: string;
  cpp: CppFn;
  lean: LeanExtern;
  arityMatch: boolean;
  cppArity: number;
  leanArity: number;
  findings: Finding[];
}

/** Positional borrow comparison over the common prefix of the two argument lists. */
export function compareBorrow(symbolName: string, cpp: CppFn, lean: LeanExtern): Comparison {
  const arityMatch = cpp.args.length === lean.params.length;
  const n = Math.min(cpp.args.length, lean.params.length);
  const findings: Finding[] = [];
  for (let i = 0; i < n; i++) {
    const cb = cpp.args[i]!.kind === "b";
    const lb = lean.params[i] === "B";
    if (cb === lb) continue;
    findings.push({
      position: i,
      direction: cb ? "cpp_borrowed_lean_not" : "lean_borrowed_cpp_not",
      cppArg: cpp.args[i]!,
      leanBorrow: lean.params[i]!,
      confidence: arityMatch ? "high" : "low",
    });
  }
  return { symbolName, cpp, lean, arityMatch, cppArity: cpp.args.length, leanArity: lean.params.length, findings };
}
