#!/usr/bin/env bun

import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

// ──────────────────────────────────────────────────────────────────────────────
// Configuration: where to find each class
// ──────────────────────────────────────────────────────────────────────────────


const MATHLIB = `${process.env.HOME}/projects/PLFaLean/.lake/packages/mathlib/Mathlib`;
const BATTERIES = `${process.env.HOME}/projects/PLFaLean/.lake/packages/batteries/Batteries`;
const LEAN_STD = `${process.env.HOME}/.elan/toolchains/leanprover--lean4---v4.31.0-rc1/src/lean/Std`;
const LEAN_INIT = `${process.env.HOME}/.elan/toolchains/leanprover--lean4---v4.31.0-rc1/src/lean/Init`;

const mathlibdoclink = "https://leanprover-community.github.io/mathlib4_docs"

// Maps class name → { file path (absolute), docs URL anchor }
const CLASS_LOCATIONS: Record<string, { file: string; docsUrl: string }> = {
    "Irrefl": {
        file: `${LEAN_INIT}/Core.lean`,
        docsUrl: `${mathlibdoclink}/Init/Core.html#Std.Irrefl`,
    },
    "Refl": {
        file: `${LEAN_INIT}/Core.lean`,
        docsUrl: `${mathlibdoclink}/Init/Core.html#Std.Refl`,
    },
    "Symm": {
        file: `${LEAN_INIT}/Core.lean`,
        docsUrl: `${mathlibdoclink}/Init/Core.html#Std.Symm`,
    },
    "Asymm": {
        file: `${LEAN_INIT}/Core.lean`,
        docsUrl: `${mathlibdoclink}/Init/Core.html#Std.Asymm`,
    },
    "Antisymm": {
        file: `${LEAN_INIT}/Core.lean`,
        docsUrl: `${mathlibdoclink}/Init/Core.html#Std.Antisymm`,
    },
    "Total": {
        file: `${LEAN_INIT}/Core.lean`,
        docsUrl: `${mathlibdoclink}/Init/Core.html#Std.Total`,
    },
    "Trichotomous": {
        file: `${LEAN_INIT}/Core.lean`,
        docsUrl: `${mathlibdoclink}/Init/Core.html#Std.Trichotomous`,
    },
    // Mathlib unbundled classes
    IsTrans: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsTrans`,
    },
    IsPreorder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsPreorder`,
    },
    IsPartialOrder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsPartialOrder`,
    },
    IsLinearOrder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsLinearOrder`,
    },
    IsEquiv: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsEquiv`,
    },
    IsStrictOrder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsStrictOrder`,
    },
    IsStrictWeakOrder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsStrictWeakOrder`,
    },
    IsStrictTotalOrder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsStrictTotalOrder`,
    },
    WellQuasiOrdered: {
        file: `${MATHLIB}/Order/WellQuasiOrder.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/WellQuasiOrder.html#WellQuasiOrdered`,
    },
    IsWellOrder: {
        file: `${MATHLIB}/Order/RelClasses.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/RelClasses.html#IsWellOrder`,
    },
    // Lattice classes
    Lattice: {
        file: `${MATHLIB}/Order/Lattice.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Lattice.html#Lattice`,
    },
    SemilatticeSup: {
        file: `${MATHLIB}/Order/Lattice.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Lattice.html#SemilatticeSup`,
    },
    SemilatticeInf: {
        file: `${MATHLIB}/Order/Lattice.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Lattice.html#SemilatticeInf`,
    },
    WellFounded: {
        file: `${LEAN_INIT}/WF.lean`,
        docsUrl: `${mathlibdoclink}/Init/WF.html#WellFounded`,
    },
    IsStrictOrder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsStrictOrder`,
    },
    IsStrictWeakOrder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsStrictWeakOrder`,
    },
    IsStrictTotalOrder: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsStrictTotalOrder`,
    },
    IsTrichotomous: {
        file: `${MATHLIB}/Order/Defs/Unbundled.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/Defs/Unbundled.html#IsTrichotomous`,
    },
    IsWellFounded: {
        file: `${MATHLIB}/Order/RelClasses.lean`,
        docsUrl: `${mathlibdoclink}/Mathlib/Order/RelClasses.html#IsWellFounded`,
    },
};

// ──────────────────────────────────────────────────────────────────────────────
// Comment stripping
// ──────────────────────────────────────────────────────────────────────────────

/** Remove all /- ... -/ block comments and -- line comments from Lean source */
function stripComments(src: string): string {
    let result = "";
    let i = 0;
    while (i < src.length) {
        // Block comment /- ... -/  (can be nested)
        if (src[i] === "/" && src[i + 1] === "-") {
            let depth = 1;
            i += 2;
            while (i < src.length && depth > 0) {
                if (src[i] === "/" && src[i + 1] === "-") {
                    depth++;
                    i += 2;
                } else if (src[i] === "-" && src[i + 1] === "/") {
                    depth--;
                    i += 2;
                } else {
                    i++;
                }
            }
            // preserve newlines so line numbers don't shift too badly
            continue;
        }
        // Line comment -- ...
        if (src[i] === "-" && src[i + 1] === "-") {
            while (i < src.length && src[i] !== "\n") i++;
            continue;
        }
        result += src[i];
        i++;
    }
    return result;
}

// ──────────────────────────────────────────────────────────────────────────────
// Extract a class / structure / abbrev definition by name
// ──────────────────────────────────────────────────────────────────────────────

/**
 * Given comment-stripped Lean source, extract the definition block for `name`.
 * Handles `class`, `structure`, `abbrev`, `def` at top level.
 * Returns the raw text (trimmed).
 */
function extractDefinition(stripped: string, name: string): string {
    // We look for lines like:
    //   class Foo ...
    //   structure Foo ...
    //   abbrev Foo ...
    //   def Foo ...
    // possibly with attributes on the preceding line like @[...] or instance ...
    const keywords = ["class", "structure", "abbrev", "def", "inductive"];
    const lines = stripped.split("\n");

    for (let li = 0; li < lines.length; li++) {
        const line = lines[li];
        // Match any of the keywords followed by the exact name, allowing for optional attributes
        const match = line.match(
            new RegExp(`^\\s*(?:@\\[.*?\\]\\s*)?(?:${keywords.join("|")})\\s+(${escapeRegex(name)})\\b`)
        );
        if (!match) continue;

        // Collect the block: we keep going until we find a line at column 0
        // that starts a new top-level declaration (or EOF).
        // Simple heuristic: collect until we see a blank line followed by a
        // top-level keyword, or until a "where" block closes.
        // Actually: just grab lines until we hit a new top-level decl.
        const blockLines: string[] = [];

        // Also grab the @[...] / attribute lines immediately above
        let start = li;
        while (start > 0) {
            const prev = lines[start - 1].trim();
            if (
                prev.startsWith("@[") ||
                prev.startsWith("attribute") ||
                prev === ""
            ) {
                if (prev === "") break; // stop at blank line
                start--;
            } else {
                break;
            }
        }

        // Now collect from start until next top-level decl
        const topLevelRe =
            /^(?:class|structure|abbrev|def|theorem|lemma|instance|section|namespace|end|#|universe|variable|open|import|@\[)/;

        blockLines.push(...lines.slice(start, li + 1));
        let j = li + 1;
        let depth = 0; // track `where` / indented blocks loosely

        // Count open `where` — we stop when we're back at top-level
        // (next non-blank, non-indented line that looks like a new decl)
        while (j < lines.length) {
            const l = lines[j];
            const trimmed = l.trim();
            if (trimmed === "") {
                blockLines.push(l);
                j++;
                // Peek: if next non-blank line is top-level, stop
                let k = j;
                while (k < lines.length && lines[k].trim() === "") k++;
                if (k < lines.length && topLevelRe.test(lines[k].trim())) break;
                continue;
            }
            // Top-level new declaration at column 0
            if (topLevelRe.test(trimmed) && !l.match(/^\s+/)) {
                break;
            }
            blockLines.push(l);
            j++;
        }

        // Remove trailing blank lines
        while (blockLines.length && blockLines[blockLines.length - 1].trim() === "")
            blockLines.pop();

        return blockLines.join("\n").trimEnd();
    }

    throw new Error(`Definition '${name}' not found in source`);
}

function escapeRegex(s: string): string {
    return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

// ──────────────────────────────────────────────────────────────────────────────
// Cache of stripped file contents
// ──────────────────────────────────────────────────────────────────────────────

const fileCache: Map<string, string> = new Map();

function getStripped(filePath: string): string {
    if (fileCache.has(filePath)) return fileCache.get(filePath)!;
    let src: string;
    try {
        src = readFileSync(filePath, "utf8");
    } catch (e) {
        throw new Error(`Cannot read file: ${filePath}\n  ${e}`);
    }
    const stripped = stripComments(src);
    fileCache.set(filePath, stripped);
    return stripped;
}

function getLeanDef(className: string): { code: string; docsUrl: string } {
    const loc = CLASS_LOCATIONS[className];
    if (!loc) throw new Error(`No file location configured for class: ${className}`);
    const stripped = getStripped(loc.file);
    // The simple name (last segment after dot)
    const simpleName = className.split(".").pop()!;
    const code = extractDefinition(stripped, simpleName);
    return { code, docsUrl: loc.docsUrl };
}

// ──────────────────────────────────────────────────────────────────────────────
// HTML helpers
// ──────────────────────────────────────────────────────────────────────────────


const LINK_ALIASES: Record<string, string> = {
    "PartialOrder": `${mathlibdoclink}/Mathlib/Order/Defs/PartialOrder.html#PartialOrder`,
    "Preorder": `${mathlibdoclink}/Mathlib/Order/Defs/PartialOrder.html#Preorder`,
    "LinearOrder": `${mathlibdoclink}/Mathlib/Order/Defs/LinearOrder.html#LinearOrder`,
    "Equivalence": `${mathlibdoclink}/Init/Core.html#Equivalence`,
    "StrictOrder": `${mathlibdoclink}/Mathlib/Order/Defs/PartialOrder.html#StrictOrder`,

    "Std.Irrefl": `${mathlibdoclink}/Init/Core.html#Std.Irrefl`,
    "Std.Refl": `${mathlibdoclink}/Init/Core.html#Std.Refl`,
    "Std.Symm": `${mathlibdoclink}/Init/Core.html#Std.Symm`,
    "Std.Asymm": `${mathlibdoclink}/Init/Core.html#Std.Asymm`,
    "Std.Antisymm": `${mathlibdoclink}/Init/Core.html#Std.Antisymm`,
    "Std.Total": `${mathlibdoclink}/Init/Core.html#Std.Total`,
    "Std.Trichotomous": `${mathlibdoclink}/Init/Core.html#Std.Trichotomous`,
};
for (const [cls, loc] of Object.entries(CLASS_LOCATIONS)) {
    LINK_ALIASES[cls] = loc.docsUrl;
}
function linkifyCode(code: string): string {
    let linked = esc(code);
    const sortedKeys = Object.keys(LINK_ALIASES).sort((a, b) => b.length - a.length);
    const escapedKeys = sortedKeys.map(escapeRegex);
    const regex = new RegExp(`(?<![a-zA-Z0-9_])(${escapedKeys.join("|")})(?![a-zA-Z0-9_])`, "g");

    linked = linked.replace(regex, (match) => {
        const url = LINK_ALIASES[match];
        return `<a href="${url}" target="_blank" class="code-link">${match}</a>`;
    });
    return linked;
}

function esc(s: string): string {
    return s
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;");
}


function renderLeanRef(cls: string, pidPrefix: string): string {
    const { code, docsUrl } = getLeanDef(cls);
    const pid = `${pidPrefix}-${cls.replace(/\./g, "-")}`;
    const linkedCode = linkifyCode(code);

    return `
    <span class="lean-ref">
      <a href="${esc(docsUrl)}" target="_blank" rel="noopener">∀ ${esc(cls)}</a>
      <span class="tooltip-trigger" data-popup="${pid}">▾</span>
    </span>
    <div class="lean-code-container" id="${pid}"><pre><code>${linkedCode}</code></pre></div>
    `;
}

/** Render a header cell with wiki link + ∀ link that shows a tooltip */
function headerCell(
    label: string,
    wikiUrl: string | null,
    classes: string[], // lean class names
    sublabel?: string
): string {
    let inner = wikiUrl ? `<a href="${esc(wikiUrl)}">${esc(label)}</a>` : esc(label);
    if (sublabel) inner += `<br><span class="sublabel">${esc(sublabel)}</span>`;

    for (const cls of classes) {
        inner += `<br>${renderLeanRef(cls, "p")}`;
    }
    return `<th>${inner}</th>`;
}

/** Render a row label cell */
function rowLabelCell(
    label: string,
    wikiUrl: string | null,
    classes: string[]
): string {
    let inner = wikiUrl ? `<a href="${esc(wikiUrl)}">${esc(label)}</a>` : esc(label);

    for (const cls of classes) {
        inner += `<br>${renderLeanRef(cls, "p-row")}`;
    }
    return `<td class="row-label">${inner}</td>`;
}

const YES = `<td class="yes" title="Always holds">✅</td>`;
const NO = `<td class="no" title="Not guaranteed">✗</td>`;

// ──────────────────────────────────────────────────────────────────────────────
// Table data
// ──────────────────────────────────────────────────────────────────────────────

// Row: [label, wikiUrl, leanClasses, sym, antisym, connected, wellfounded, joins, meets, refl, irrefl, asym]
type BoolRow = [
    label: string,
    wikiUrl: string | null,
    leanClasses: string[],
    sym: boolean,
    antisym: boolean,
    connected: boolean,
    wellfounded: boolean,
    joins: boolean,
    meets: boolean,
    refl: boolean,
    irrefl: boolean,
    asym: boolean,
    trichotomous: boolean
];


const ROWS: BoolRow[] = [
    // ----------------------------------------------------------------------------------
    // Anonymous Lean Classes (Red rows, no Wiki mapping)
    // ----------------------------------------------------------------------------------
    ["", null, ["IsTrichotomous"], false, false, false, false, false, false, false, false, false, true],
    ["", null, ["IsWellFounded"], false, false, false, true, false, false, false, false, false, false],
    ["", null, ["IsStrictTotalOrder"], false, true, false, false, false, false, false, true, true, true],
    ["", null, ["IsWellOrder"], false, true, false, true, false, false, false, true, true, true],

    // ----------------------------------------------------------------------------------
    // Wikipedia Table Rows
    // ----------------------------------------------------------------------------------
    [
        "Equivalence relation",
        "https://en.wikipedia.org/wiki/Equivalence_relation",
        ["IsEquiv"],
        true, false, false, false, false, false, true, false, false, false,
    ],
    [
        "Preorder (Quasiorder)",
        "https://en.wikipedia.org/wiki/Preorder",
        ["IsPreorder"],
        false, false, false, false, false, false, true, false, false, false,
    ],
    [
        "Partial order",
        "https://en.wikipedia.org/wiki/Partial_order",
        ["IsPartialOrder"],
        false, true, false, false, false, false, true, false, false, false,
    ],
    [
        "Total preorder",
        "https://en.wikipedia.org/wiki/Total_preorder",
        [], // Used to be IsLinearOrder, which is wrong
        false, false, true, false, false, false, true, false, false, false,
    ],
    [
        "Total order",
        "https://en.wikipedia.org/wiki/Total_order",
        ["IsLinearOrder"],
        false, true, true, false, false, false, true, false, false, false,
    ],
    [
        "Prewellordering",
        "https://en.wikipedia.org/wiki/Prewellordering",
        [],
        false, false, true, true, false, false, true, false, false, false,
    ],
    [
        "Well-quasi-ordering",
        "https://en.wikipedia.org/wiki/Well-quasi-ordering",
        ["WellQuasiOrdered"],
        false, false, false, true, false, false, true, false, false, false,
    ],
    [
        "Well-ordering",
        "https://en.wikipedia.org/wiki/Well-order",
        [], // Lean's IsWellOrder is strict, this is reflexive
        false, true, true, true, false, false, true, false, false, false,
    ],
    [
        "Lattice",
        "https://en.wikipedia.org/wiki/Lattice_(order)",
        ["Lattice"],
        false, true, false, false, true, true, true, false, false, false,
    ],
    [
        "Join-semilattice",
        "https://en.wikipedia.org/wiki/Join-semilattice",
        ["SemilatticeSup"],
        false, true, false, false, true, false, true, false, false, false,
    ],
    [
        "Meet-semilattice",
        "https://en.wikipedia.org/wiki/Meet-semilattice",
        ["SemilatticeInf"],
        false, true, false, false, false, true, true, false, false, false,
    ],
    [
        "Strict partial order",
        "https://en.wikipedia.org/wiki/Strict_partial_order",
        ["IsStrictOrder"],
        false, true, false, false, false, false, false, true, true, false,
    ],
    [
        "Strict weak order",
        "https://en.wikipedia.org/wiki/Weak_ordering#Strict_weak_orderings",
        ["IsStrictWeakOrder"],
        false, true, false, false, false, false, false, true, true, false,
    ],
    [
        "Strict total order",
        "https://en.wikipedia.org/wiki/Strict_total_order",
        [], // Lean's IsStrictTotalOrder uses Trichotomous, not Connected
        false, true, true, false, false, false, false, true, true, false,
    ],
];


// ──────────────────────────────────────────────────────────────────────────────
// Build HTML
// ──────────────────────────────────────────────────────────────────────────────

function buildHTML(): string {
    // Build header row
    const headers: { label: string; wiki: string | null; classes: string[]; sublabel?: string }[] = [
        { label: "Symmetric", wiki: "https://en.wikipedia.org/wiki/Symmetric_relation", classes: ["Symm"] },
        { label: "Antisymmetric", wiki: "https://en.wikipedia.org/wiki/Antisymmetric_relation", classes: ["Antisymm"] },
        { label: "Connected", wiki: "https://en.wikipedia.org/wiki/Connected_relation", classes: ["Total"], sublabel: "Total, Semiconnex" },
        { label: "Well-founded", wiki: "https://en.wikipedia.org/wiki/Well-founded_relation", classes: ["WellFounded"] },
        { label: "Has joins", wiki: "https://en.wikipedia.org/wiki/Join_and_meet", classes: ["SemilatticeSup"] },
        { label: "Has meets", wiki: "https://en.wikipedia.org/wiki/Join_and_meet", classes: ["SemilatticeInf"] },
        { label: "Reflexive", wiki: "https://en.wikipedia.org/wiki/Reflexive_relation", classes: ["Refl"] },
        { label: "Irreflexive", wiki: "https://en.wikipedia.org/wiki/Reflexive_relation#Irreflexive", classes: ["Irrefl"], sublabel: "Anti-reflexive" },
        { label: "Asymmetric", wiki: "https://en.wikipedia.org/wiki/Asymmetric_relation", classes: ["Asymm"] },
    ];

    const headerRow = `
    <tr>
      <th class="row-label-header" style="font-size: 14px; padding-left: 0.2em; padding-right: 0.2em;">
        <a href="https://en.wikipedia.org/wiki/Transitive_relation">Transitive</a>&nbsp;<a href="https://en.wikipedia.org/wiki/Binary_relation">binary relations</a>
      </th>
      ${headers.map((h) => headerCell(h.label, h.wiki, h.classes, h.sublabel)).join("\n      ")}
    </tr>`;

    const defsRow = `
    <tr>
      <th class="row-label-header" style="font-size: 11px;">
        Definitions,<br>for all \\(a,b\\) and \\(S\\neq\\varnothing:\\)
      </th>
      <th>\\(\\begin{aligned}&aRb\\\\\\Rightarrow {}&bRa\\end{aligned}\\)</th>
      <th>\\(\\begin{aligned}aRb\\text{ and }&bRa\\\\\\Rightarrow a={}&b\\end{aligned}\\)</th>
      <th>\\(\\begin{aligned}a\\neq {}&b\\Rightarrow \\\\aRb\\text{ or }&bRa\\end{aligned}\\)</th>
      <th>\\(\\begin{aligned}\\min S\\\\\\text{exists}\\end{aligned}\\)</th>
      <th>\\(\\begin{aligned}a\\vee b\\\\\\text{exists}\\end{aligned}\\)</th>
      <th>\\(\\begin{aligned}a\\wedge b\\\\\\text{exists}\\end{aligned}\\)</th>
      <th>\\(aRa\\)</th>
      <th>\\(\\text{not } aRa\\)</th>
      <th>\\(\\begin{aligned}aRb\\Rightarrow \\\\\\text{not } bRa\\end{aligned}\\)</th>
    </tr>`;

    // Build data rows

    const nodes = [];
    const edges = [];
    const nodeDataMap: any = {};

    const knownCombinations = new Map<number, typeof ROWS[0]>();
    ROWS.forEach((row, rowIndex) => {
        // Skip header row
        const bools = row.slice(3) as boolean[];
        let mask = 0;
        bools.forEach((b, i) => { if (b) mask |= (1 << i); });
        knownCombinations.set(mask, row);
    });

    for (let i = 0; i < 1024; i++) {
        const isSymmetric = (i & (1 << 0)) !== 0;
        const isAntisymm = (i & (1 << 1)) !== 0;
        const isReflexive = (i & (1 << 6)) !== 0;
        const isIrreflexive = (i & (1 << 7)) !== 0;
        const isAsymmetric = (i & (1 << 8)) !== 0;

        const isImpossible = (isReflexive && isIrreflexive) || (isSymmetric && isAsymmetric);

        let color = isImpossible ? '#b8860b' : '#cc0000'; // dark yellow, dark red
        let label = isImpossible ? 'Impossible' : 'Unknown';

        const props = [];
        for(let j=0; j<10; j++) {
            if (i & (1<<j)) props.push(["Symmetric","Antisymmetric","Connected","Well-founded","Has joins","Has meets","Reflexive","Irreflexive","Asymmetric"][j]);
        }

        let leanDefsHtml = "";

        if (knownCombinations.has(i)) {
            const row = knownCombinations.get(i)!;
            color = '#005cc5'; // blue
            label = String(row[0]);

            const classes = row[2] as string[];
            for (const cls of classes) {
                leanDefsHtml += renderLeanRef(cls, `graph-${i}`);
            }
        }

        nodeDataMap[i] = {
            label,
            properties: props,
            leanDefsHtml
        };

        // Node
        nodes.push({
            id: i,
            label: label,
            color: { background: color, border: '#222' },
            font: { color: '#FFF', size: 12 },
            shape: 'box',
            level: props.length // Hierarchical level!
        });

        // Edges (Hasse diagram)
        for (let j = 0; j < 10; j++) {
            if ((i & (1 << j)) === 0) { // j is absent
                const target = i | (1 << j);
                edges.push({ from: i, to: target, arrows: 'to' });
            }
        }
    }

    const dataRows = ROWS.map(([label, wiki, classes, ...bools]) => {
        const cells = bools.map((b) => (b ? YES : NO)).join("");
        return `    <tr>${rowLabelCell(label, wiki, classes)}${cells}</tr>`;
    }).join("\n");

    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>Transitive Binary Relations</title>
    <script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
  <style>
    *, *::before, *::after { box-sizing: border-box; }

    body {
      font-family: system-ui, sans-serif;
      font-size: 14px;
      padding: 2rem;
      background: #0d1117;
      color: #c9d1d9;
    }

    h1 { color: #e6edf3; margin-bottom: 1rem; }

    .note {
      font-size: 12px;
      color: #8b949e;
      margin-bottom: 1.5rem;
      max-width: 800px;
    }

    table {
      border-collapse: collapse;
      width: 100%;
    }

    th, td {
      border: 1px solid #30363d;
      padding: 6px 10px;
      text-align: center;
      vertical-align: middle;
    }

    th {
      background: #161b22;
      color: #e6edf3;
      font-size: 12px;
      position: relative;
    }

    .sublabel {
      font-size: 10px;
      color: #8b949e;
      display: block;
    }

    td.row-label, th.row-label-header {
      text-align: left;
      font-weight: 600;
      white-space: nowrap;
      background: #161b22;
      color: #e6edf3;
      min-width: 180px;
    }

    td.yes  { color: #3fb950; font-size: 16px; }
    td.no   { color: #f85149; font-size: 14px; }

    a { color: #58a6ff; text-decoration: none; }
    a:hover { text-decoration: underline; }

    /* ---- lean-ref inline widget ---- */
    .lean-ref {
      display: inline-block;
      position: relative;
      font-size: 11px;
      vertical-align: middle;
    }

    .lean-ref a {
      color: #d2a8ff;
      font-weight: 700;
      font-size: 13px;
    }

    .tooltip-trigger {
      cursor: pointer;
      color: #8b949e;
      user-select: none;
      margin-left: 1px;
    }
    .tooltip-trigger:hover { color: #c9d1d9; }


    .tabs { margin-bottom: 16px; }
    .tab-btn {
      background: #21262d; border: 1px solid #30363d; color: #c9d1d9;
      padding: 8px 16px; cursor: pointer; border-radius: 6px 6px 0 0;
      margin-right: 4px;
    }
    .tab-btn.active {
      background: #0d1117; border-bottom: 1px solid #0d1117;
    }
    .view-content { display: none; }
    .view-content.active { display: block; }

    /* Graph */
    .vis-network { outline: none; }

    /* lean code container */
    body.inline-mode .tooltip-trigger { display: none; }
    body.inline-mode .lean-code-container {
      display: block;
      margin-top: 8px;
      text-align: left;
      background: #010409;
      border: 1px solid #30363d;
      border-radius: 6px;
      overflow-x: auto;
    }
    body:not(.inline-mode) .lean-code-container {
      display: none;
      position: absolute;
      z-index: 999;
      margin-top: 4px;
      min-width: 420px;
      max-width: 620px;
      background: #010409;
      border: 1px solid #30363d;
      border-radius: 6px;
      box-shadow: 0 8px 24px rgba(0,0,0,0.7);
      text-align: left;
    }
    body:not(.inline-mode) .lean-code-container.active { display: block; }

    .lean-code-container pre {
      margin: 0;
      padding: 10px 12px;
    }
    .lean-code-container code {
      font-family: "JetBrains Mono", "Fira Code", monospace;
      font-size: 11px;
      color: #e6edf3;
      white-space: pre;
    }
    .code-link {
        color: #58a6ff;
        text-decoration: none;
    }
    .code-link:hover {
        text-decoration: underline;
    }
    .inline-code pre {
      margin: 0;
      padding: 8px;
    }
    .inline-code code {
      font-family: "JetBrains Mono", "Fira Code", monospace;
      font-size: 11px;
      color: #e6edf3;
      white-space: pre;
    }
  </style>
</head>
<body>

<h1>Transitive Binary Relations</h1>
<label style="display: flex; align-items: center; gap: 8px; margin-bottom: 1rem; cursor: pointer;">
  <input type="checkbox" id="toggleCodeView" checked />
  Show Lean definitions inline
</label>
<p class="note">
  All relations are implicitly transitive (∀ a b c, aRb → bRc → aRc).
  ✅ = property always holds · ✗ = not guaranteed.<br>
  <strong>∀</strong> links open Mathlib docs. The ▾ toggle shows the Lean definition inline (when inline mode is disabled).
</p>
<p class="note">
  https://en.wikipedia.org/w/index.php?title=Template%3ABinary_relations&action=edit
</p>



<div class="tabs">
  <button id="tab-table" class="tab-btn active">Table View</button>
  <button id="tab-graph" class="tab-btn">Graph View</button>
</div>

<div id="view-table" class="view-content active">
  <table>
    <thead>
  ${headerRow}
  ${defsRow}
    </thead>
    <tbody>
  ${dataRows}
    </tbody>
  </table>
  <div style="text-align:center; font-size: 11px; margin-top: 10px; color: #8b949e; line-height: 1.4;">
    ✅ indicates that the column's property is always true for the row's term (at the very left), while ✗ indicates that the property is not guaranteed<br>
    in general (it might, or might not, hold). For example, that every equivalence relation is symmetric, but not necessarily antisymmetric,<br>
    is indicated by ✅ in the "Symmetric" column and ✗ in the "Antisymmetric" column, respectively.<br>
    All definitions tacitly require the homogeneous relation \(R\) be transitive: for all \(a, b, c,\) if \(aRb\) and \(bRc\) then \(aRc.\)<br>
    A term's definition may require additional properties that are not listed in this table.
  </div>
</div>

<div id="view-graph" class="view-content">
  <div style="display: flex; gap: 20px;">
    <div id="mynetwork" style="width: 70%; height: 800px; border: 1px solid #30363d; background: #010409;"></div>
    <div id="graph-panel" style="width: 30%; border: 1px solid #30363d; padding: 16px; border-radius: 6px; background: #010409; overflow-y: auto; height: 800px;">
      <h3>Node Details</h3>
      <p>Select a node to view its properties and Lean definitions.</p>
    </div>
  </div>
</div>


<script>
  const toggle = document.getElementById('toggleCodeView');
  toggle.addEventListener('change', (e) => {
    if (e.target.checked) document.body.classList.add('inline-mode');
    else document.body.classList.remove('inline-mode');
  });
  if (toggle.checked) document.body.classList.add('inline-mode');

  // Toggle popup on ▾ click; close on outside click
  document.addEventListener('click', (e) => {
    const trigger = e.target.closest('.tooltip-trigger');
    if (trigger) {
      const pid = trigger.dataset.popup;
      const popup = document.getElementById(pid);
      if (!popup) return;
      const isActive = popup.classList.contains('active');
      // close all
      document.querySelectorAll('.lean-code-container.active').forEach(p => p.classList.remove('active'));
      if (!isActive) popup.classList.add('active');
      e.stopPropagation();
      return;
    }
    // close on outside click
    document.querySelectorAll('.lean-code-container.active').forEach(p => p.classList.remove('active'));
  });
</script>

  <script type="text/javascript" src="https://unpkg.com/vis-network/standalone/umd/vis-network.min.js"></script>
  <script>
    // Tab switching
    document.getElementById('tab-table').addEventListener('click', (e) => {
        document.getElementById('tab-table').classList.add('active');
        document.getElementById('tab-graph').classList.remove('active');
        document.getElementById('view-table').classList.add('active');
        document.getElementById('view-graph').classList.remove('active');
    });
    document.getElementById('tab-graph').addEventListener('click', (e) => {
        document.getElementById('tab-graph').classList.add('active');
        document.getElementById('tab-table').classList.remove('active');
        document.getElementById('view-graph').classList.add('active');
        document.getElementById('view-table').classList.remove('active');
        if (!window.graphInitialized) initGraph();
    });

    const nodeDataMap = ${JSON.stringify(nodeDataMap)};

    function initGraph() {
        window.graphInitialized = true;
        const container = document.getElementById('mynetwork');
        const data = {
            nodes: new vis.DataSet(${JSON.stringify(nodes)}),
            edges: new vis.DataSet(${JSON.stringify(edges)})
        };
        const options = {
            layout: {
                hierarchical: {
                    direction: 'UD',
                    sortMethod: 'directed',
                    levelSeparation: 150,
                    nodeSpacing: 100,
                    treeSpacing: 200
                }
            },
            physics: false, // physics disabled for hierarchical
            edges: { smooth: false, color: '#30363d' },
            interaction: { navigationButtons: true, keyboard: true }
        };
        const network = new vis.Network(container, data, options);

        network.on("click", function (params) {
            if (params.nodes.length > 0) {
                const nodeId = params.nodes[0];
                const info = nodeDataMap[nodeId];
                const panel = document.getElementById('graph-panel');

                let html = "<h3>" + info.label + "</h3>";
                html += "<p><strong>Properties:</strong> " + (info.properties.length > 0 ? info.properties.join(", ") : "None") + "</p>";
                if (info.leanDefsHtml) {
                    html += "<div>" + info.leanDefsHtml + "</div>";
                } else if (info.label === 'Unknown') {
                    html += '<p style="color: #ff7b72;">This combination of properties has no mapped Lean definition.</p>';
                } else if (info.label === 'Impossible') {
                    html += '<p style="color: #d29922;">This combination of properties is logically self-excluding.</p>';
                }
                panel.innerHTML = html;
            }
        });
    }
  </script>

</body>
</html>`;
}

// ──────────────────────────────────────────────────────────────────────────────
// Main
// ──────────────────────────────────────────────────────────────────────────────

try {
    const html = buildHTML();
    const outPath = "transitive_binary_relations.html";
    writeFileSync(outPath, html, "utf8");
    console.log(`✅  Written to ${outPath}`);
} catch (err) {
    console.error("❌  Error:", err instanceof Error ? err.message : err);
    process.exit(1);
}
