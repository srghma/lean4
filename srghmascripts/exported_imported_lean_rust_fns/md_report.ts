import fs from "node:fs";
import { glob } from "node:fs/promises";
import path from "node:path";

export type ExternReportItem = {
    lineNum: number;
    symbolName: string;
    leanName: string;
    status: "ok" | "empty" | "missing" | "reference";
    rustPath: string | null;
    rustLineNum: number | null;
    rustSnippet: string | null;
};

export type ExportReportItem = {
    lineNum: number;
    symbolName: string;
    leanName: string;
    status: "correct" | "wrong_import" | "defined_in_rust" | "extern_c" | "dynamic_lookup" | "missing";
    rustPath: string | null;
    rustLineNum: number | null;
    rustSnippet: string | null;
    currentImport: string | null;
    correctUsePath: string;
    cppUsages: CppUsage[];
};

export type CppUsage = {
    absolutePath: string;
    relativePath: string;
    lineNum: number;
};

export type MarkdownReportBlock<T> = {
    relativePath: string;
    items: T[];
    lines: string[];
};

export const discoverRustWorkspacePackages = (rustDir: string) => {
    const entries = fs.readdirSync(rustDir, { withFileTypes: true });
    return entries
        .filter((entry) => entry.isDirectory())
        .map((entry) => entry.name)
        .filter((name) => name === "leanh" || /^leanh_l\d+$/.test(name) || name === "runtime")
        .sort((a, b) => {
            const rank = (name: string) => {
                const match = name.match(/^leanh_l(\d+)$/);
                if (match) return Number(match[1]);
                if (name === "runtime") return 1000;
                if (name === "leanh") return 2000;
                return 3000;
            };
            return rank(a) - rank(b) || a.localeCompare(b);
        });
};

const escapeMdInline = (text: string) =>
    text
        .replaceAll("\\", "\\\\")
        .replaceAll("`", "\\`")
        .replaceAll("|", "\\|");

const mdCode = (text: string) => `\`${escapeMdInline(text)}\``;

const mdLink = (label: string, absPath: string) => `[${label}](${absPath})`;

const workspaceLink = (reportDir: string, absPath: string, lineNum?: number) => {
    const rel = path.relative(reportDir, absPath).replaceAll(path.sep, "/");
    return lineNum ? `${rel}#${lineNum}` : rel;
};

const mdAbsolutePath = (rootDir: string, relativePath: string) =>
    path.isAbsolute(relativePath) ? relativePath : path.join(rootDir, relativePath);

const stripCppCommentsKeepLines = (content: string) => {
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
            if (char === "/" && nextChar === "*") {
                insideBlockComment++;
                result += "  ";
                i += 2;
            } else if (char === "*" && nextChar === "/") {
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
            if (char === "/" && nextChar === "/") {
                insideLineComment = true;
                result += "  ";
                i += 2;
            } else if (char === "/" && nextChar === "*") {
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
};

const escapeRegExp = (str: string) => str.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

export const collectCppUsages = async (rootDir: string, symbols: Iterable<string>) => {
    const symbolList = [...new Set(symbols)].filter(Boolean);
    const usageMap = new Map<string, CppUsage[]>();
    if (symbolList.length === 0) return usageMap;

    const pattern = new RegExp(`\\b(${symbolList.map(escapeRegExp).join("|")})\\b`, "g");
    const cppFilePaths: string[] = [];
    for await (const file of glob("**/*.{h,cpp,c,hpp}", { cwd: rootDir })) {
        cppFilePaths.push(path.join(rootDir, file));
    }

    await Promise.all(cppFilePaths.map(async (absoluteFile) => {
        const content = stripCppCommentsKeepLines(await fs.promises.readFile(absoluteFile, "utf8"));
        const lines = content.split("\n");
        for (let lineIdx = 0; lineIdx < lines.length; lineIdx++) {
            const rawLine = lines[lineIdx] ?? "";
            const trimmed = rawLine.trim();
            if (trimmed.startsWith("#include") || trimmed.startsWith("import ") || trimmed.startsWith("using ")) continue;

            pattern.lastIndex = 0;
            const matches = rawLine.matchAll(pattern);
            for (const match of matches) {
                const symbol = match[1];
                if (!symbol) continue;
                const list = usageMap.get(symbol) ?? [];
                const rel = path.relative(rootDir, absoluteFile);
                if (!list.some((item) => item.relativePath === rel && item.lineNum === lineIdx + 1)) {
                    list.push({ absolutePath: absoluteFile, relativePath: rel, lineNum: lineIdx + 1 });
                    usageMap.set(symbol, list);
                }
            }
        }
    }));

    for (const list of usageMap.values()) {
        list.sort((a, b) => a.relativePath.localeCompare(b.relativePath) || a.lineNum - b.lineNum);
    }

    return usageMap;
};

const renderCommonHeader = (rootDir: string, leanDir: string, rustDir: string, workspacePackages: string[], title: string) => {
    const lines: string[] = [];
    lines.push(`# ${title}`);
    lines.push("");
    lines.push(`- Root: ${mdCode(rootDir)}`);
    lines.push(`- Lean scan root: ${mdCode(leanDir)}`);
    lines.push(`- Rust scan root: ${mdCode(rustDir)}`);
    if (workspacePackages.length > 0) {
        lines.push(`- Rust workspace packages: ${workspacePackages.map(mdCode).join(", ")}`);
    }
    lines.push("");
    return lines;
};

const reportDir = (rootDir: string) => path.join(rootDir, "srghmascripts");

const renderExternSection = (params: {
    rootDir: string;
    leanDir: string;
    rustDir: string;
    workspacePackages: string[];
    externBlocks: MarkdownReportBlock<ExternReportItem>[];
}) => {
    const { rootDir, leanDir, rustDir, workspacePackages, externBlocks } = params;
    const linkRoot = reportDir(rootDir);
    const lines = renderCommonHeader(rootDir, leanDir, rustDir, workspacePackages, `List of all functions that lean imports from rust`);
    lines.push(`## Lean imports from Rust ([extern]): (Lean <- Rust)`);
    lines.push("");
    lines.push(`| File | Line | Item | Status | Rust | Details |`);
    lines.push(`| --- | ---: | --- | --- | --- | --- |`);
    for (const block of externBlocks) {
        const leanFile = mdLink(mdCode(block.relativePath), workspaceLink(linkRoot, mdAbsolutePath(rootDir, block.relativePath)));
        for (const item of block.items) {
            const rustLocation = item.rustPath && item.rustLineNum !== null ? `${item.rustPath}:${item.rustLineNum}` : null;
            const rustLink = item.rustPath ? mdLink(mdCode(rustLocation ?? item.rustPath), workspaceLink(linkRoot, mdAbsolutePath(rootDir, item.rustPath), item.rustLineNum ?? undefined)) : mdCode("❌");
            const status =
                item.status === "ok" ? "✅" :
                item.status === "empty" ? "⚠️" :
                item.status === "missing" ? "❌" :
                "🔍";
            const details =
                item.status === "ok"
                    ? `Rust defined this function and function body is not empty (correct)`
                    : item.status === "empty"
                        ? `Rust defined this function but function body is empty (empty)`
                        : item.status === "reference"
                            ? `Referenced in Rust`
                            : `Rust does not define this function (missing)`;
            const extra = item.rustSnippet ? ` ${mdCode(item.rustSnippet)}` : "";
            lines.push(`| ${leanFile} | ${item.lineNum} | ${mdCode(`[extern "${item.symbolName}"] ${item.leanName}`)} | ${status} | ${rustLink} | ${details}${extra} |`);
        }
    }
    return lines.join("\n");
};

const renderExportSection = (params: {
    rootDir: string;
    leanDir: string;
    rustDir: string;
    workspacePackages: string[];
    exportBlocks: MarkdownReportBlock<ExportReportItem>[];
}) => {
    const { rootDir, leanDir, rustDir, workspacePackages, exportBlocks } = params;
    const linkRoot = reportDir(rootDir);
    const lines = renderCommonHeader(rootDir, leanDir, rustDir, workspacePackages, `list of all functions that rust imports from lean`);
    lines.push(`## Rust should import from Lean ([export]): (Lean -> Rust)`);
    lines.push("");
    lines.push(`| File | Line | Item | Status | Rust | C++ Usage | Details |`);
    lines.push(`| --- | ---: | --- | --- | --- | --- | --- |`);
    for (const block of exportBlocks) {
        const leanFile = mdLink(mdCode(block.relativePath), workspaceLink(linkRoot, mdAbsolutePath(rootDir, block.relativePath)));
        for (const item of block.items) {
            const rustLocation = item.rustPath && item.rustLineNum !== null ? `${item.rustPath}:${item.rustLineNum}` : null;
            const rustLink = item.rustPath ? mdLink(mdCode(rustLocation ?? item.rustPath), workspaceLink(linkRoot, mdAbsolutePath(rootDir, item.rustPath), item.rustLineNum ?? undefined)) : mdCode("❌");
            const cppUsage = item.cppUsages.length > 0
                ? item.cppUsages
                    .map((usage) => mdLink(mdCode(`${usage.relativePath}:${usage.lineNum}`), workspaceLink(linkRoot, usage.absolutePath, usage.lineNum)))
                    .join(", ")
                : mdCode("none");
            const status =
                item.status === "correct" ? "✅" :
                item.status === "wrong_import" ? "⚠️" :
                item.status === "defined_in_rust" ? "🛠️" :
                item.status === "extern_c" ? "🔌" :
                item.status === "dynamic_lookup" ? "🔍" :
                "❌";
            const details =
                item.status === "correct"
                    ? `Function is found in rust code and import is correct (correct)`
                    : item.status === "wrong_import"
                        ? `Function is found in rust code, but import is wrong (wrong): ${mdCode(`use ${item.correctUsePath};`)}`
                        : item.status === "defined_in_rust"
                            ? `Function is found in rust code, but is defined in rust (defined): ${mdCode(`use ${item.correctUsePath};`)}`
                            : item.status === "extern_c"
                                ? `Function is found inside of extern "C" block / FFI (externc)`
                                : item.status === "dynamic_lookup"
                                    ? `Function is referenced via dynamic string lookup (dynamic)`
                                    : `Function is not found in rust code (missing): ${mdCode(`use ${item.correctUsePath};`)}`;
            const snippet = item.rustSnippet ? ` ${mdCode(item.rustSnippet)}` : "";
            const currentImport = item.currentImport ? ` current import ${mdCode(item.currentImport)}` : "";
            lines.push(`| ${leanFile} | ${item.lineNum} | ${mdCode(item.leanName)} / ${mdCode(item.symbolName)} | ${status} | ${rustLink} | ${cppUsage} | ${details}${currentImport}${snippet} |`);
        }
    }
    return lines.join("\n");
};

const renderSummarySection = (params: {
    stats: {
        extern: { total: number; ok: number; empty: number; missing: number };
        export: { total: number; ok: number; wrong: number; definedRust: number; externC: number; dynamicLookup: number; missing: number };
    };
}) => {
    const { stats } = params;
    const lines: string[] = [];
    lines.push(`# WORKSPACE ANALYSIS SUMMARY`);
    lines.push(`========================================================================`);
    lines.push(`Lean imports from Rust ([extern]): (Lean <- Rust)`);
    lines.push("");
    lines.push(`| Label | Count |`);
    lines.push(`| --- | ---: |`);
    lines.push(`| Total occurrences: | ${stats.extern.total} |`);
    lines.push(`| Rust defined this function and function body is not empty (correct) (✅): | ${stats.extern.ok} |`);
    lines.push(`| Rust defined this function but function body is empty (empty) (⚠️): | ${stats.extern.empty} |`);
    lines.push(`| Rust does not define this function (missing) (❌): | ${stats.extern.missing} |`);
    lines.push("");
    lines.push(`Rust should import from Lean ([export]): (Lean -> Rust)`);
    lines.push("");
    lines.push(`| Label | Count |`);
    lines.push(`| --- | ---: |`);
    lines.push(`| Total occurrences: | ${stats.export.total} |`);
    lines.push(`| Function is found in rust code and import is correct (correct) (✅): | ${stats.export.ok} |`);
    lines.push(`| Function is found in rust code, but import is wrong (wrong) (⚠️): | ${stats.export.wrong} |`);
    lines.push(`| Function is found in rust code, but is defined in rust (defined) (🛠️): | ${stats.export.definedRust} |`);
    lines.push(`| Function is found inside of extern "C" block / FFI (externc) (🔌): | ${stats.export.externC} |`);
    lines.push(`| Function is referenced via dynamic string lookup (dynamic) (🔍): | ${stats.export.dynamicLookup} |`);
    lines.push(`| Function is not found in rust code (missing) (❌): | ${stats.export.missing} |`);
    lines.push(`========================================================================`);
    return lines.join("\n");
};

export const renderExternMarkdown = (params: {
    rootDir: string;
    leanDir: string;
    rustDir: string;
    workspacePackages: string[];
    externBlocks: MarkdownReportBlock<ExternReportItem>[];
}) => renderExternSection(params);

export const renderExportMarkdown = (params: {
    rootDir: string;
    leanDir: string;
    rustDir: string;
    workspacePackages: string[];
    exportBlocks: MarkdownReportBlock<ExportReportItem>[];
}) => renderExportSection(params);

export const renderSummaryMarkdown = (params: {
    stats: {
        extern: { total: number; ok: number; empty: number; missing: number };
        export: { total: number; ok: number; wrong: number; definedRust: number; externC: number; dynamicLookup: number; missing: number };
    };
}) => renderSummarySection(params);
