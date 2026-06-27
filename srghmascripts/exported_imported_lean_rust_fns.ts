#!/usr/bin/env bun

import { Glob } from "bun";
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
import { validateAndProcessOptions, printHelp } from "./exported_imported_lean_rust_fns/parse_args";

const colors = {
    reset: "\x1b[0m",
    bold: "\x1b[1m",
    dim: "\x1b[2m",
    cyan: "\x1b[36m",
    green: "\x1b[32m",
    yellow: "\x1b[33m",
    red: "\x1b[31m",
    magenta: "\x1b[35m",
    blue: "\x1b[34m",
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

    const { help, showSummary, showDetails, externConfig, exportConfig } = config;

    // Handle Help Request
    if (help) {
        printHelp();
        process.exit(0);
    }

    if (showDetails) {
        console.log(c.dim(`Scanning Lean codebase under: ${leanDir}...`));
    }

    const leanGlob = new Glob("**/*.lean");
    const rustGlob = new Glob("**/*.rs");

    const targetSymbols = new Set<string>();
    interface LeanFileInfo {
        relativePath: string;
        occurrences: LeanOccurrence[];
    }
    const leanFilesData: LeanFileInfo[] = [];

    // Parse Lean files
    for (const file of leanGlob.scanSync({ cwd: leanDir, absolute: true })) {
        try {
            const content = fs.readFileSync(file, "utf8");
            const occurrences = Array.from(scanLeanFile(content));
            if (occurrences.length > 0) {
                occurrences.forEach(occ => targetSymbols.add(occ.symbolName));
                leanFilesData.push({
                    relativePath: path.relative(rootDir, file),
                    occurrences,
                });
            }
        } catch (e) {
            console.error(`Warning: Failed to parse Lean file ${file}:`, e);
        }
    }

    // Parse Rust files and build matched lookup index
    const rustIndex = new Map<string, RustSearchResult[]>();
    for (const file of rustGlob.scanSync({ cwd: rustDir, absolute: true })) {
        try {
            const content = fs.readFileSync(file, "utf8");
            for (const item of findSymbolsInRust(file, content, targetSymbols)) {
                if (!rustIndex.has(item.symbol)) {
                    rustIndex.set(item.symbol, []);
                }
                rustIndex.get(item.symbol)!.push(item.result);
            }
        } catch (e) {
            console.error(`Warning: Failed to parse Rust file ${file}:`, e);
        }
    }

    const getBestRustMatch = (symbol: string): RustSearchResult | null => {
        const matches = rustIndex.get(symbol);
        if (!matches || matches.length === 0) return null;
        return [...matches].sort((a, b) => {
            if (a.isDefinition && a.hasBody && !(b.isDefinition && b.hasBody)) return -1;
            if (!(a.isDefinition && a.hasBody) && b.isDefinition && b.hasBody) return 1;
            if (a.isDefinition && !b.isDefinition) return -1;
            if (!a.isDefinition && b.isDefinition) return 1;
            return 0;
        })[0];
    };

    const stats = {
        extern: { total: 0, ok: 0, empty: 0, missing: 0 },
        export: { total: 0, ok: 0, wrong: 0, definedRust: 0, externC: 0, missing: 0 },
    };

    // Section 1: Lean imports from Rust [extern] (Lean <- Rust)
    const externOutputBlocks: { relativePath: string; lines: string[] }[] = [];

    for (const fileData of leanFilesData) {
        const externs = fileData.occurrences.filter(o => o.type === "extern");
        if (externs.length === 0) continue;

        const printedLines: string[] = [];

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
                if (isOk) {
                    printedLines.push(`${linePrefix} <- ${c.path(relRust)}:${match.lineNum} (${match.snippet}) ✅`);
                } else if (isEmpty) {
                    printedLines.push(`${linePrefix} <- ${c.path(relRust)}:${match.lineNum} (${match.snippet}) ⚠️ (Rust defined this function but function body is empty)`);
                } else {
                    printedLines.push(`${linePrefix} <- ${c.path(relRust)}:${match.lineNum} (${match.snippet}) 🔍 (Referenced in Rust)`);
                }
            } else {
                printedLines.push(`${linePrefix} <- ❌ (Rust does not define this function)`);
            }
        }

        if (printedLines.length > 0) {
            externOutputBlocks.push({ relativePath: fileData.relativePath, lines: printedLines });
        }
    }

    // Section 2: Rust imports from Lean [export] (Lean -> Rust)
    const exportOutputBlocks: { relativePath: string; lines: string[] }[] = [];

    for (const fileData of leanFilesData) {
        const exports = fileData.occurrences.filter(o => o.type === "export");
        if (exports.length === 0) continue;

        const printedLines: string[] = [];

        for (const occ of exports) {
            stats.export.total++;
            const match = getBestRustMatch(occ.symbolName);
            const correctUsePath = getCorrectRustUsePath(fileData.relativePath, occ.symbolName);

            if (!match) {
                stats.export.missing++;
                if (exportConfig.missing) {
                    printedLines.push(`  ${c.line(occ.lineNum)} @[export ${c.symbol(occ.symbolName)}] ${c.name(occ.leanName)} -> ❌ (Not found in Rust, should be \`use ${correctUsePath};\`)`);
                }
                continue;
            }

            const classification = classifyRustLine(match.snippet, occ.symbolName, correctUsePath, match.hasBody, match.isDefinition);
            const relRust = path.relative(rootDir, match.filePath);
            const linePrefix = `  ${c.line(occ.lineNum)} @[export ${c.symbol(occ.symbolName)}] ${c.name(occ.leanName)} -> ${c.path(relRust)}:${match.lineNum}`;

            // Increment stats metrics
            if (classification.status === "correct") stats.export.ok++;
            else if (classification.status === "wrong_import") stats.export.wrong++;
            else if (classification.status === "defined_in_rust") stats.export.definedRust++;
            else if (classification.status === "extern_c") stats.export.externC++;

            // Evaluate Leaf Filters
            if (classification.status === "correct" && !exportConfig.importCorrect) continue;
            if (classification.status === "wrong_import" && !exportConfig.importWrong) continue;
            if (classification.status === "defined_in_rust" && !exportConfig.definedInRust) continue;
            if (classification.status === "extern_c" && !exportConfig.externC) continue;
        }

        if (printedLines.length > 0) {
            exportOutputBlocks.push({ relativePath: fileData.relativePath, lines: printedLines });
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
        console.log(`  Total occurrences:                                                 ${stats.extern.total}`);
        console.log(`  Rust defined this function and function body is not empty (✅):     ${c.ok(stats.extern.ok.toString())}`);
        console.log(`  Rust defined this function but function body is empty (⚠️):       ${stats.extern.empty > 0 ? c.warning(stats.extern.empty.toString()) : stats.extern.empty}`);
        console.log(`  Rust does not define this function (❌):                            ${stats.extern.missing > 0 ? c.warning(stats.extern.missing.toString()) : stats.extern.missing}`);

        console.log();

        console.log(`${colors.bold}Rust should import from Lean ([export]): (Lean -> Rust)${colors.reset}`);
        console.log(`  Total occurrences:                                                 ${stats.export.total}`);
        console.log(`  Function is found in rust code and import is correct (✅):          ${c.ok(stats.export.ok.toString())}`);
        console.log(`  Function is found in rust code, but import is wrong (⚠️):            ${stats.export.wrong > 0 ? c.warning(stats.export.wrong.toString()) : stats.export.wrong}`);
        console.log(`  Function is found in rust code, but is defined in rust (🛠️):         ${stats.export.definedRust > 0 ? c.warning(stats.export.definedRust.toString()) : stats.export.definedRust}`);
        console.log(`  Function is found inside of extern "C" block (🔌):                  ${stats.export.externC > 0 ? c.warning(stats.export.externC.toString()) : stats.export.externC}`);
        console.log(`  Function is not found in rust code (❌):                            ${stats.export.missing > 0 ? c.warning(stats.export.missing.toString()) : stats.export.missing}`);
        console.log(colors.bold + "========================================================================" + colors.reset);
    }
})();
