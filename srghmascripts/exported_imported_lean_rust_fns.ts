#!/usr/bin/env bun

import { glob } from "node:fs/promises";
import fs from "node:fs";
import path from "node:path";
import {
    scanLeanFile,
    findSymbolsInRust,
    getCorrectRustUsePath,
    classifyRustLine,
    type LeanOccurrence,
    type RustSearchResult
} from "./exported_imported_lean_rust_fns/lib";
import { makePathExcluder } from "./exported_imported_lean_rust_fns/glob";
import {
    discoverRustWorkspacePackages,
    collectCppUsages,
    type CppUsage,
    renderExternMarkdown,
    renderExportMarkdown,
    renderSummaryMarkdown,
    type ExternReportItem,
    type ExportReportItem,
    type MarkdownReportBlock,
} from "./exported_imported_lean_rust_fns/md_report";
import { buildJsonReport } from "./exported_imported_lean_rust_fns/json_report";
import {
    appendRuntimeAnnotations,
    collectRuntimeAnnotation,
    formatRuntimeAnnotation,
} from "./exported_imported_lean_rust_fns/runtime_annotations";
import { validateAndProcessOptions, printHelp } from "./exported_imported_lean_rust_fns/parse_args";

// Detect if output is being redirected or piped (like to copyq)
// or if the user has requested no colors via env variables
const useColors = !!process.stdout.isTTY && !process.env.NO_COLOR;

const colors = useColors
    ? {
        reset: "\x1b[0m",
        bold: "\x1b[1m",
        dim: "\x1b[2m",
        cyan: "\x1b[36m",
        green: "\x1b[32m",
        yellow: "\x1b[33m",
        red: "\x1b[31m",
        magenta: "\x1b[35m",
        blue: "\x1b[34m",
    }
    : {
        reset: "",
        bold: "",
        dim: "",
        cyan: "",
        green: "",
        yellow: "",
        red: "",
        magenta: "",
        blue: "",
    };

const c = {
    header: (text: string) => `${colors.magenta}${colors.bold}${text}${colors.reset}`,
    file: (text: string) => `${colors.cyan}${colors.bold}${text}${colors.reset}`,
    symbol: (text: string) => `${colors.yellow}${text}${colors.reset}`,
    name: (text: string) => `${colors.green}${colors.bold}${text}${colors.reset}`,
    line: (num: number) => `${colors.dim}Line ${num}:${colors.reset}`,
    path: (text: string) => `${colors.blue}${text}${colors.reset}`,
    warning: (text: string) => `${colors.red}${colors.bold}${text}${colors.reset}`,
    ok: (text: string) => `${colors.green}${text}${colors.reset}`,
    dim: (text: string) => `${colors.dim}${text}${colors.reset}`,
};

const IGNORED_PATH_GLOBS = [
    "src/rust/**/src/gen/**",
    "src/rust/**/src/lean_imports_rs/**",
    "src/rust/gen_*/**",
    "src/**/.lake/**",
    "src/**/build/**",
    "src/**/dist/**",
    "src/**/out/**",
];

/**
 * Alignment helper that formats label and value columns uniformly.
 * Accounts for 2-column terminal display width of emojis to ensure precise margins.
 */
const alignLine = (label: string, value: number, valueColorFn?: (val: string) => string): string => {
    const targetWidth = 78;
    const segmenter = new Intl.Segmenter("en", { granularity: "grapheme" });
    const charCount = Array.from(segmenter.segment(label)).length;

    // Explicitly detect 2-cell emojis used in the summary output
    const emojiRegex = /[✅⚠️❌🛠️🔌🔍]/gu;
    const emojiCount = (label.match(emojiRegex) || []).length;

    const displayWidth = charCount + emojiCount;
    const padding = " ".repeat(Math.max(1, targetWidth - displayWidth));

    const formattedValue = valueColorFn ? valueColorFn(value.toString()) : value.toString();
    return `${label}${padding}${formattedValue}`;
};

type LeanFileInfo = {
    relativePath: string;
    absolutePath: string;
    moduleName: string;
    occurrences: LeanOccurrence[];
    imports: string[];
};

const stripLeanCommentsKeepLines = (content: string) => {
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
};

const parseLeanImports = (content: string): string[] => {
    const cleaned = stripLeanCommentsKeepLines(content);
    const imports = new Set<string>();
    for (const line of cleaned.split("\n")) {
        const trimmed = line.trim();
        const match = trimmed.match(/^(?:public\s+)?import\s+(.+)$/);
        if (!match) continue;
        const rest = match[1]!.trim();
        for (const item of rest.split(/\s+/)) {
            if (item) imports.add(item);
        }
    }
    return [...imports];
};

const moduleNameFromLeanPath = (absolutePath: string, rootDir: string) => {
    const rel = path.relative(rootDir, absolutePath).replaceAll(path.sep, "/");
    return rel.replace(/\.lean$/, "").split("/").join(".");
};

const topoSortLeanFiles = (files: LeanFileInfo[]) => {
    const byModule = new Map(files.map((file) => [file.moduleName, file] as const));
    const inDegree = new Map<string, number>();
    const reverse = new Map<string, string[]>();
    const reverseCount = new Map<string, number>();

    for (const file of files) {
        inDegree.set(file.moduleName, 0);
        reverse.set(file.moduleName, []);
        reverseCount.set(file.moduleName, 0);
    }

    for (const file of files) {
        for (const imp of file.imports) {
            if (!byModule.has(imp) || imp === file.moduleName) continue;
            reverse.get(imp)!.push(file.moduleName);
            reverseCount.set(imp, (reverseCount.get(imp) ?? 0) + 1);
            inDegree.set(file.moduleName, (inDegree.get(file.moduleName) ?? 0) + 1);
        }
    }

    const compareModules = (a: string, b: string) => {
        const byDependents = (reverseCount.get(b) ?? 0) - (reverseCount.get(a) ?? 0);
        if (byDependents !== 0) return byDependents;
        return a.localeCompare(b);
    };

    const queue = [...files]
        .filter((file) => (inDegree.get(file.moduleName) ?? 0) === 0)
        .map((file) => file.moduleName)
        .sort(compareModules);
    const ordered: string[] = [];

    while (queue.length > 0) {
        queue.sort(compareModules);
        const cur = queue.shift()!;
        ordered.push(cur);
        for (const next of reverse.get(cur) ?? []) {
            const deg = (inDegree.get(next) ?? 0) - 1;
            inDegree.set(next, deg);
            if (deg === 0) queue.push(next);
        }
    }

    const seen = new Set(ordered);
    const remaining = files
        .map((file) => file.moduleName)
        .filter((name) => !seen.has(name))
        .sort(compareModules);

    return [...ordered, ...remaining]
        .map((name) => byModule.get(name)!)
        .filter(Boolean);
};

(async () => {
    const rootDir = "/home/srghma/projects/lean4";
    const leanDir = path.join(rootDir, "src");
    const rustDir = path.join(rootDir, "src/rust");

    // Validate and parse configuration
    let config;
    try {
        config = validateAndProcessOptions(Bun.argv.slice(2));
    } catch (e: any) {
        console.error(c.warning(e.message));
        process.exit(1);
    }

    const {
        help,
        showSummary,
        showDetails,
        externConfig,
        exportConfig,
        genLeanImportsRsStubs,
        appendCommentToLeanImportsFromRust,
        appendCommentToRustShouldImportFromLean,
        writeMarkdown,
    } = config;

    // Handle Help Request
    if (help) {
        printHelp();
        process.exit(0);
    }

    if (showDetails) {
        console.log(c.dim(`Scanning Lean codebase under: ${leanDir}...`));
    }

    const targetSymbols = new Set<string>();
    const allLeanFilesData: LeanFileInfo[] = [];
    const leanFilesData: LeanFileInfo[] = [];

    // Collect all Lean files
    const leanFilePaths: string[] = [];
    const leanPathExcluder = makePathExcluder(leanDir, rootDir, IGNORED_PATH_GLOBS);
    for await (const file of glob("**/*.lean", { cwd: leanDir, exclude: leanPathExcluder })) {
        leanFilePaths.push(path.join(leanDir, file));
    }

    // Parallelize Lean files parsing
    await Promise.all(
        leanFilePaths.map(async (absoluteFile) => {
            try {
                const content = await fs.promises.readFile(absoluteFile, "utf8");
                const occurrences = Array.from(scanLeanFile(content));
                const fileInfo = {
                    relativePath: path.relative(rootDir, absoluteFile),
                    absolutePath: absoluteFile,
                    moduleName: moduleNameFromLeanPath(absoluteFile, leanDir),
                    occurrences,
                    imports: parseLeanImports(content),
                };
                allLeanFilesData.push(fileInfo);
                if (occurrences.length > 0) {
                    occurrences.forEach(occ => targetSymbols.add(occ.symbolName));
                    leanFilesData.push(fileInfo);
                }
            } catch (e) {
                console.error(`Warning: Failed to parse Lean file ${absoluteFile}:`, e);
            }
        })
    );

    const modulesWithOccurrences = new Set(leanFilesData.map(file => file.moduleName));
    const orderedLeanFilesData = topoSortLeanFiles(allLeanFilesData)
        .filter(file => modulesWithOccurrences.has(file.moduleName));

    const exportSymbols = new Set<string>();
    for (const fileData of orderedLeanFilesData) {
        for (const occ of fileData.occurrences) {
            if (occ.type === "export") {
                exportSymbols.add(occ.symbolName);
            }
        }
    }

    const originMasterDir = path.join(rootDir, "origin-master-src");
    const cppUsageBySymbol = fs.existsSync(originMasterDir)
        ? await collectCppUsages(originMasterDir, exportSymbols)
        : new Map<string, CppUsage[]>();

    // Collect all Rust files
    const rustFilePaths: string[] = [];
    const rustPathExcluder = makePathExcluder(rustDir, rootDir, IGNORED_PATH_GLOBS);
    for await (const file of glob("**/*.rs", { cwd: rustDir, exclude: rustPathExcluder })) {
        rustFilePaths.push(path.join(rustDir, file));
    }

    // Parallelize Rust files reading and indexing
    const rustIndex = new Map<string, RustSearchResult[]>();
    const runtimeAnnotations = new Map<string, Map<number, Set<string>>>();
    await Promise.all(
        rustFilePaths.map(async (absoluteFile) => {
            try {
                const content = await fs.promises.readFile(absoluteFile, "utf8");
                for (const item of findSymbolsInRust(absoluteFile, content, targetSymbols)) {
                    if (!rustIndex.has(item.symbol)) {
                        rustIndex.set(item.symbol, []);
                    }
                    rustIndex.get(item.symbol)!.push(item.result);
                }
            } catch (e) {
                console.error(`Warning: Failed to parse Rust file ${absoluteFile}:`, e);
            }
        })
    );

    if (showDetails) {
        console.log(c.dim(`Processed ${leanFilesData.length} Lean files with symbols (${allLeanFilesData.length} total Lean files) and indexed ${rustFilePaths.length} Rust files.`));
    }

    const getRustPackageRank = (filePath: string): number => {
        const rel = path.relative(rustDir, filePath).replaceAll(path.sep, "/");
        const firstSegment = rel.split("/")[0] ?? "";
        const match = firstSegment.match(/^leanh_l(\d+)$/);
        if (match) return Number(match[1]);
        if (firstSegment === "runtime") return 1000;
        if (firstSegment === "leanh") return 2000;
        return 3000;
    };

    const compareRustSearchResults = (a: RustSearchResult, b: RustSearchResult) => {
        const packageRankDiff = getRustPackageRank(a.filePath) - getRustPackageRank(b.filePath);
        if (packageRankDiff !== 0) return packageRankDiff;

        const aIsConcreteDefinition = a.isDefinition && a.hasBody;
        const bIsConcreteDefinition = b.isDefinition && b.hasBody;
        if (aIsConcreteDefinition !== bIsConcreteDefinition) return aIsConcreteDefinition ? -1 : 1;

        const aIsDefinition = a.isDefinition;
        const bIsDefinition = b.isDefinition;
        if (aIsDefinition !== bIsDefinition) return aIsDefinition ? -1 : 1;

        const lineDiff = a.lineNum - b.lineNum;
        if (lineDiff !== 0) return lineDiff;

        return a.filePath.localeCompare(b.filePath) || a.snippet.localeCompare(b.snippet);
    };

    const getBestRustMatch = (symbol: string): RustSearchResult | null => {
        const matches = rustIndex.get(symbol);
        if (!matches || matches.length === 0) return null;
        return [...matches].sort(compareRustSearchResults)[0];
    };

    const stats = {
        extern: { total: 0, ok: 0, empty: 0, missing: 0 },
        export: { total: 0, ok: 0, wrong: 0, definedRust: 0, externC: 0, dynamicLookup: 0, missing: 0 },
    };

    // Section 1: Lean imports from Rust [extern] (Lean <- Rust)
    const externOutputBlocks: MarkdownReportBlock<ExternReportItem>[] = [];

    for (const fileData of orderedLeanFilesData) {
        const externs = fileData.occurrences.filter(o => o.type === "extern");
        if (externs.length === 0) continue;

        const printedLines: string[] = [];
        const markdownItems: ExternReportItem[] = [];

        for (const occ of externs) {
            stats.extern.total++;
            const match = getBestRustMatch(occ.symbolName);

            const isOk = !!(match && match.isDefinition && match.hasBody);
            const isEmpty = !!(match && match.isDefinition && !match.hasBody);
            const isMissing = !match;
            const isReference = !!(match && !match.isDefinition);

            if (isOk) stats.extern.ok++;
            else if (isEmpty) stats.extern.empty++;
            else stats.extern.missing++;

            // Evaluate Leaf Filters
            if (isOk && !externConfig.rustOk) continue;
            if (isEmpty && !externConfig.rustEmpty) continue;
            if (isMissing && !externConfig.rustMissing) continue;
            if (isReference && !externConfig.rustOk) continue;

            const linePrefix = `  ${c.line(occ.lineNum)} [extern "${c.symbol(occ.symbolName)}"] ${c.name(occ.leanName)}`;

            if (match) {
                const relRust = path.relative(rootDir, match.filePath);
                if (appendCommentToLeanImportsFromRust) {
                    collectRuntimeAnnotation(
                        runtimeAnnotations,
                        match.filePath,
                        match.lineNum,
                        formatRuntimeAnnotation({
                            kind: "extern",
                            status: isOk ? "extern_ok" : isEmpty ? "extern_empty" : "extern_missing",
                            leanPath: fileData.relativePath,
                            leanLine: occ.lineNum,
                        })
                    );
                }
                if (isOk) {
                    printedLines.push(`${linePrefix} <- ${c.path(relRust)}:${match.lineNum} (${match.snippet}) ✅`);
                } else if (isEmpty) {
                    printedLines.push(`${linePrefix} <- ${c.path(relRust)}:${match.lineNum} (${match.snippet}) ⚠️ (Rust defined this function but function body is empty)`);
                } else {
                    printedLines.push(`${linePrefix} <- ${c.path(relRust)}:${match.lineNum} (${match.snippet}) 🔍 (Referenced in Rust)`);
                }
                markdownItems.push({
                    lineNum: occ.lineNum,
                    symbolName: occ.symbolName,
                    leanName: occ.leanName,
                    status: isOk ? "ok" : isEmpty ? "empty" : "reference",
                    rustPath: relRust,
                    rustLineNum: match.lineNum,
                    rustSnippet: match.snippet,
                });
            } else {
                printedLines.push(`${linePrefix} <- ❌ (Rust does not define this function)`);
                markdownItems.push({
                    lineNum: occ.lineNum,
                    symbolName: occ.symbolName,
                    leanName: occ.leanName,
                    status: "missing",
                    rustPath: null,
                    rustLineNum: null,
                    rustSnippet: null,
                });
            }
        }

        if (printedLines.length > 0) {
            externOutputBlocks.push({ relativePath: fileData.relativePath, items: markdownItems, lines: printedLines });
        }
    }

    // Section 2: Rust imports from Lean [export] (Lean -> Rust)
    const exportOutputBlocks: MarkdownReportBlock<ExportReportItem>[] = [];

    for (const fileData of orderedLeanFilesData) {
        const exports = fileData.occurrences.filter(o => o.type === "export");
        if (exports.length === 0) continue;

        const printedLines: string[] = [];
        const markdownItems: ExportReportItem[] = [];

        for (const occ of exports) {
            stats.export.total++;
            const match = getBestRustMatch(occ.symbolName);
            const correctUsePath = getCorrectRustUsePath(fileData.relativePath, occ.symbolName);
            const cppUsages = cppUsageBySymbol.get(occ.symbolName) ?? [];

            if (!match) {
                stats.export.missing++;
                if (exportConfig.missing) {
                    const cppUsageText = cppUsages.length > 0 ? cppUsages.map((usage) => `${usage.relativePath}:${usage.lineNum}`).join(", ") : "none";
                    printedLines.push(`  ${c.line(occ.lineNum)} @[export ${c.symbol(occ.symbolName)}] ${c.name(occ.leanName)} -> ❌ (Not found in Rust, should be \`use ${correctUsePath};\`) | C++ usage: ${cppUsageText}`);
                }
                markdownItems.push({
                    lineNum: occ.lineNum,
                    symbolName: occ.symbolName,
                    leanName: occ.leanName,
                    status: "missing",
                    rustPath: null,
                    rustLineNum: null,
                    rustSnippet: null,
                    currentImport: null,
                    correctUsePath,
                    cppUsages,
                });
                continue;
            }

            const classification = classifyRustLine(match.snippet, occ.symbolName, correctUsePath, match.hasBody, match.isDefinition, match.isStringLiteral);
            const relRust = path.relative(rootDir, match.filePath);
            const linePrefix = `  ${c.line(occ.lineNum)} @[export ${c.symbol(occ.symbolName)}] ${c.name(occ.leanName)} -> ${c.path(relRust)}:${match.lineNum}`;

            if (appendCommentToRustShouldImportFromLean) {
                const annotationStatus =
                    classification.status === "correct" ? "export_correct" :
                    classification.status === "wrong_import" ? "export_wrong" :
                    classification.status === "defined_in_rust" ? "export_defined" :
                    classification.status === "extern_c" ? "export_externc" :
                    "export_dynamic";
                collectRuntimeAnnotation(
                    runtimeAnnotations,
                    match.filePath,
                    match.lineNum,
                    formatRuntimeAnnotation({
                        kind: "export",
                        status: annotationStatus,
                        leanPath: fileData.relativePath,
                        leanLine: occ.lineNum,
                    })
                );
            }

            // Increment stats metrics
            if (classification.status === "correct") stats.export.ok++;
            else if (classification.status === "wrong_import") stats.export.wrong++;
            else if (classification.status === "defined_in_rust") stats.export.definedRust++;
            else if (classification.status === "extern_c") stats.export.externC++;
            else if (classification.status === "dynamic_lookup") stats.export.dynamicLookup++;

            // Evaluate Leaf Filters
            if (classification.status === "correct" && !exportConfig.importCorrect) continue;
            if (classification.status === "wrong_import" && !exportConfig.importWrong) continue;
            if (classification.status === "defined_in_rust" && !exportConfig.definedInRust) continue;
            if (classification.status === "extern_c" && !exportConfig.externC) continue;
            if (classification.status === "dynamic_lookup" && !exportConfig.dynamicLookup) continue;

            if (classification.status === "correct") {
                const cppUsageText = cppUsages.length > 0 ? cppUsages.map((usage) => `${usage.relativePath}:${usage.lineNum}`).join(", ") : "none";
                printedLines.push(`${linePrefix} (${classification.snippet}) ✅ | C++ usage: ${cppUsageText}`);
            } else if (classification.status === "wrong_import") {
                const cppUsageText = cppUsages.length > 0 ? cppUsages.map((usage) => `${usage.relativePath}:${usage.lineNum}`).join(", ") : "none";
                printedLines.push(`${linePrefix} -> ⚠️ (Wrong import: \`${classification.snippet}\`, should be \`use ${correctUsePath};\`) | C++ usage: ${cppUsageText}`);
            } else if (classification.status === "defined_in_rust") {
                const cppUsageText = cppUsages.length > 0 ? cppUsages.map((usage) => `${usage.relativePath}:${usage.lineNum}`).join(", ") : "none";
                printedLines.push(`${linePrefix} -> 🛠️ (Defined in Rust: \`${classification.snippet}\`, should be \`use ${correctUsePath};\`) | C++ usage: ${cppUsageText}`);
            } else if (classification.status === "extern_c") {
                const cppUsageText = cppUsages.length > 0 ? cppUsages.map((usage) => `${usage.relativePath}:${usage.lineNum}`).join(", ") : "none";
                printedLines.push(`${linePrefix} -> 🔌 (FFI Declaration: \`${classification.snippet}\`) ✅ | C++ usage: ${cppUsageText}`);
            } else if (classification.status === "dynamic_lookup") {
                const cppUsageText = cppUsages.length > 0 ? cppUsages.map((usage) => `${usage.relativePath}:${usage.lineNum}`).join(", ") : "none";
                printedLines.push(`${linePrefix} -> 🔍 (Dynamic string lookup: \`${classification.snippet}\`) ✅ | C++ usage: ${cppUsageText}`);
            }

            markdownItems.push({
                lineNum: occ.lineNum,
                symbolName: occ.symbolName,
                leanName: occ.leanName,
                status: classification.status,
                rustPath: relRust,
                rustLineNum: match.lineNum,
                rustSnippet: match.snippet,
                currentImport: classification.currentImport ?? null,
                correctUsePath,
                cppUsages,
            });
        }

        if (printedLines.length > 0) {
            exportOutputBlocks.push({ relativePath: fileData.relativePath, items: markdownItems, lines: printedLines });
        }
    }

    if (appendCommentToLeanImportsFromRust || appendCommentToRustShouldImportFromLean) {
        await appendRuntimeAnnotations(runtimeAnnotations);
        if (showDetails) {
            const touchedFiles = [...runtimeAnnotations.keys()].length;
            const touchedLines = [...runtimeAnnotations.values()].reduce((acc, lines) => acc + [...lines.values()].reduce((inner, comments) => inner + comments.size, 0), 0);
            console.log(c.dim(`Annotated ${touchedLines} runtime matches across ${touchedFiles} files.`));
        }
    }

    // Print execution details if not suppressed by configs
    if (showDetails) {
        console.log(`\n${c.header("# List of all functions that lean imports from rust")}\n`);
        for (const block of externOutputBlocks) {
            console.log(c.file(block.relativePath));
            block.lines.forEach(l => console.log(l));
            console.log();
        }

        console.log(`${c.header("# list of all functions that rust imports from lean")}\n`);
        for (const block of exportOutputBlocks) {
            console.log(c.file(block.relativePath));
            block.lines.forEach(l => console.log(l));
            console.log();
        }
    }

    // Final Output Summary Block
    if (showSummary) {
        console.log(colors.bold + "========================================================================" + colors.reset);
        console.log(c.header("WORKSPACE ANALYSIS SUMMARY"));
        console.log(colors.bold + "========================================================================" + colors.reset);

        console.log(`${colors.bold}Lean imports from Rust ([extern]): (Lean <- Rust)${colors.reset}`);
        console.log(alignLine(`  Total occurrences:`, stats.extern.total));
        console.log(alignLine(`  Rust defined this function and function body is not empty (correct) (✅):`, stats.extern.ok, c.ok));
        console.log(alignLine(`  Rust defined this function but function body is empty (empty) (⚠️):`, stats.extern.empty, c.warning));
        console.log(alignLine(`  Rust does not define this function (missing) (❌):`, stats.extern.missing, c.warning));

        console.log();

        console.log(`${colors.bold}Rust should import from Lean ([export]): (Lean -> Rust)${colors.reset}`);
        console.log(alignLine(`  Total occurrences:`, stats.export.total));
        console.log(alignLine(`  Function is found in rust code and import is correct (correct) (✅):`, stats.export.ok, c.ok));
        console.log(alignLine(`  Function is found in rust code, but import is wrong (wrong) (⚠️):`, stats.export.wrong, c.warning));
        console.log(alignLine(`  Function is found in rust code, but is defined in rust (defined) (🛠️):`, stats.export.definedRust, c.warning));
        console.log(alignLine(`  Function is found inside of extern "C" block / FFI (externc) (🔌):`, stats.export.externC, c.ok));
        console.log(alignLine(`  Function is referenced via dynamic string lookup (dynamic) (🔍):`, stats.export.dynamicLookup, c.ok));
        console.log(alignLine(`  Function is not found in rust code (missing) (❌):`, stats.export.missing, c.warning));
        console.log(colors.bold + "========================================================================" + colors.reset);
    }

    // --- SELF-CONSISTENCY INTEGRITY VALIDATION ---
    const validationErrors: string[] = [];

    // Verification 1: Sum of metrics must equal reported totals
    const sumExternMetric = stats.extern.ok + stats.extern.empty + stats.extern.missing;
    if (stats.extern.total !== sumExternMetric) {
        validationErrors.push(`Extern total (${stats.extern.total}) does not match the sum of its category metrics (${sumExternMetric}).`);
    }

    const sumExportMetric = stats.export.ok + stats.export.wrong + stats.export.definedRust + stats.export.externC + stats.export.dynamicLookup + stats.export.missing;
    if (stats.export.total !== sumExportMetric) {
        validationErrors.push(`Export total (${stats.export.total}) does not match the sum of its category metrics (${sumExportMetric}).`);
    }

    // Verification 2: Reported totals must match raw occurrences parsed from files
    const totalParsedExterns = leanFilesData.reduce((acc, f) => acc + f.occurrences.filter(o => o.type === "extern").length, 0);
    if (stats.extern.total !== totalParsedExterns) {
        validationErrors.push(`Extern total (${stats.extern.total}) does not match parsed occurrences in Lean codebase (${totalParsedExterns}).`);
    }

    const totalParsedExports = leanFilesData.reduce((acc, f) => acc + f.occurrences.filter(o => o.type === "export").length, 0);
    if (stats.export.total !== totalParsedExports) {
        validationErrors.push(`Export total (${stats.export.total}) does not match parsed occurrences in Lean codebase (${totalParsedExports}).`);
    }

    // Verification 3: If filters are wide-open, populated output block lines must match totals
    const isExternUnfiltered = externConfig.rustOk && externConfig.rustEmpty && externConfig.rustMissing;
    if (isExternUnfiltered) {
        const totalExternLines = externOutputBlocks.reduce((acc, b) => acc + b.items.length, 0);
        if (stats.extern.total !== totalExternLines) {
            validationErrors.push(`Extern total (${stats.extern.total}) does not match lines in detail output blocks (${totalExternLines}) under unfiltered mode.`);
        }
    }

    const isExportUnfiltered = exportConfig.importCorrect && exportConfig.importWrong && exportConfig.definedInRust && exportConfig.externC && exportConfig.dynamicLookup && exportConfig.missing;
    if (isExportUnfiltered) {
        const totalExportLines = exportOutputBlocks.reduce((acc, b) => acc + b.items.length, 0);
        if (stats.export.total !== totalExportLines) {
            validationErrors.push(`Export total (${stats.export.total}) does not match lines in detail output blocks (${totalExportLines}) under unfiltered mode.`);
        }
    }

    if (validationErrors.length > 0) {
        console.error(c.warning("\n❌ Validation Mismatch Error: Summary stats and detailed item structures do not align!"));
        for (const err of validationErrors) {
            console.error(c.warning(`  - ${err}`));
        }
        process.exit(1);
    }

    if (writeMarkdown) {
        const workspacePackages = discoverRustWorkspacePackages(rustDir);
        const externMarkdown = renderExternMarkdown({
            rootDir,
            leanDir,
            rustDir,
            workspacePackages,
            externBlocks: externOutputBlocks,
        });
        const exportMarkdown = renderExportMarkdown({
            rootDir,
            leanDir,
            rustDir,
            workspacePackages,
            exportBlocks: exportOutputBlocks,
        });
        const summaryMarkdown = renderSummaryMarkdown({ stats });

        const externMarkdownPath = path.join(rootDir, "srghmascripts/exported_imported_lean_rust_fns--lean_imports_from_rust.md");
        const exportMarkdownPath = path.join(rootDir, "srghmascripts/exported_imported_lean_rust_fns--rust_should_import_from_lean.md");
        const summaryMarkdownPath = path.join(rootDir, "srghmascripts/exported_imported_lean_rust_fns--summary.md");
        const externJsonPath = path.join(rootDir, "srghmascripts/exported_imported_lean_rust_fns--lean_imports_from_rust.json");
        const exportJsonPath = path.join(rootDir, "srghmascripts/exported_imported_lean_rust_fns--rust_should_import_from_lean.json");
        const externJson = buildJsonReport("lean_imports_from_rust", stats, externOutputBlocks);
        const exportJson = buildJsonReport("rust_should_import_from_lean", stats, exportOutputBlocks);

        await Promise.all([
            fs.promises.writeFile(externMarkdownPath, `${externMarkdown}\n`, "utf8"),
            fs.promises.writeFile(exportMarkdownPath, `${exportMarkdown}\n`, "utf8"),
            fs.promises.writeFile(summaryMarkdownPath, `${summaryMarkdown}\n`, "utf8"),
            fs.promises.writeFile(externJsonPath, `${JSON.stringify(externJson, null, 2)}\n`, "utf8"),
            fs.promises.writeFile(exportJsonPath, `${JSON.stringify(exportJson, null, 2)}\n`, "utf8"),
        ]);
        if (showDetails) {
            console.log(c.dim(`Wrote markdown reports to ${externMarkdownPath}, ${exportMarkdownPath}, and ${summaryMarkdownPath}`));
            console.log(c.dim(`Wrote JSON reports to ${externJsonPath} and ${exportJsonPath}`));
        }
    }

    // --- STUB GENERATION FOR LEAN IMPORTS ---
    if (genLeanImportsRsStubs) {
        console.log(c.header(`\nGenerating Lean-to-Rust stub files under: ${path.join(rootDir, "src/rust/lean_runtime/src/lean_imports_rs")}`));
        let generatedFileCount = 0;

        for (const fileData of leanFilesData) {
            const externs = fileData.occurrences.filter(o => o.type === "extern");
            if (externs.length === 0) continue;

            // Compute relative path from src/
            let leanRelToSrc = fileData.relativePath;
            if (leanRelToSrc.startsWith("src/")) {
                leanRelToSrc = leanRelToSrc.substring(4);
            }

            const rustStubRelPath = leanRelToSrc.replace(/\.lean$/, ".rs");
            const stubDestPath = path.join(rootDir, "src/rust/lean_runtime/src/lean_imports_rs", rustStubRelPath);

            // Deduplicate symbols to avoid repeated definitions
            const uniqueSymbols = Array.from(new Set(externs.map(o => o.symbolName)));

            // Construct file contents
            let content = `// Generated stub file for Lean FFI imports\n// Source: ${fileData.relativePath}\n\n`;
            for (const sym of uniqueSymbols) {
                content += `pub fn ${sym}() {\n    todo!("Stub for ${sym}");\n}\n\n`;
            }

            // Write file
            try {
                const destDir = path.dirname(stubDestPath);
                if (!fs.existsSync(destDir)) {
                    fs.mkdirSync(destDir, { recursive: true });
                }
                fs.writeFileSync(stubDestPath, content, "utf8");
                generatedFileCount++;
            } catch (e) {
                console.error(c.warning(`Error generating stub file ${stubDestPath}: ${e}`));
            }
        }

        console.log(c.ok(`Successfully generated FFI stubs across ${generatedFileCount} files.`));
    }
})();
