import { parseArgs } from "node:util";

const options = {
    // Help toggle
    "help": { type: "boolean", short: "h" },

    // Summary visibility toggles
    "hide-summary": { type: "boolean" },
    "only-summary": { type: "boolean" },

    // Group visibility filters
    "only-extern": { type: "boolean" },
    "only-export": { type: "boolean" },

    // Only Toggles
    "only-extern-ok": { type: "boolean" },
    "only-extern-empty": { type: "boolean" },
    "only-extern-missing": { type: "boolean" },

    "only-export-correct": { type: "boolean" },
    "only-export-wrong": { type: "boolean" },
    "only-export-defined": { type: "boolean" },
    "only-export-externc": { type: "boolean" },
    "only-export-dynamic": { type: "boolean" },
    "only-export-missing": { type: "boolean" },

    // Stub Generation Option
    "gen-lean-imports-rs-stubs": { type: "boolean" },

    // Annotation Option
    "append-comment-to-lean-imports-from-rust": { type: "boolean" },
    "append-comment-to-rust-should-import-from-lean": { type: "boolean" },

    // Markdown report toggle
    "no-write-md": { type: "boolean" },
} as const;

/**
 * Prints CLI usage instructions
 */
export function printHelp() {
    console.log(`
Usage: ./srghmascripts/exported_imported_lean_rust_fns.ts [options]

Options:
  -h, --help                               Show this help message
  --gen-lean-imports-rs-stubs            Generate Rust stub files in lean_imports_rs for extern Lean imports
  --append-comment-to-lean-imports-from-rust
                                        Append audit comments for the "lean imports from rust" group
  --append-comment-to-rust-should-import-from-lean
                                        Append audit comments for the "rust should import from lean" group
  --no-write-md                          Do not write srghmascripts/exported_imported_lean_rust_fns--exluding-success.md

  Summary Visibility:
    --hide-summary                         Do not print the summary block
    --only-summary                         Only print the summary block (hides all details)

  Group Filters:
    --only-extern                          Only show Lean imports from Rust (extern) details
    --only-export                          Only show Rust imports from Lean (export) details

  Detailed Filters (disables other categories when used):
    Lean imports from Rust ([extern]):
      --only-extern-ok                     Only show "Rust defined this function and function body is not empty (✅)"
      --only-extern-empty                  Only show "Rust defined this function but function body is empty (⚠️)"
      --only-extern-missing                Only show "Rust does not define this function (❌)"

    Rust should import from Lean ([export]):
      --only-export-correct                Only show "Function is found in rust code and import is correct (✅)"
      --only-export-wrong                  Only show "Function is found in rust code, but import is wrong (⚠️)"
      --only-export-defined                Only show "Function is found in rust code, but is defined in rust (🛠️)"
      --only-export-externc                Only show "Function is found inside of extern "C" block / FFI (🔌)"
      --only-export-dynamic                Only show "Function is referenced via dynamic string lookup (🔍)"
      --only-export-missing                Only show "Function is not found in rust code (❌)"
`);
}

/**
 * Parses arguments and checks for structural configuration conflicts.
 * Throws an Error if contradictions are detected.
 */
export function validateAndProcessOptions(args: string[]) {
    const { values } = parseArgs({
        args,
        options,
        strict: true,
    });

    if (values.help) {
        return {
            help: true,
            showSummary: false,
            showDetails: false,
            externConfig: { rustOk: false, rustEmpty: false, rustMissing: false },
            exportConfig: { importCorrect: false, importWrong: false, definedInRust: false, externC: false, dynamicLookup: false, missing: false },
        genLeanImportsRsStubs: false,
        appendCommentToLeanImportsFromRust: false,
        appendCommentToRustShouldImportFromLean: false,
        writeMarkdown: false,
        };
    }

    const wasPassed = (keys: (keyof typeof options)[]) =>
        keys.some(k => values[k] !== undefined);

    // --- Check 1: Contradictory Summary Parameters ---
    if (values["only-summary"] && values["hide-summary"]) {
        throw new Error("Conflict: Cannot specify both --only-summary and --hide-summary.");
    }

    // --- Check 2: Detail Filtering Redundancy ---
    const detailKeys: (keyof typeof options)[] = [
        "only-extern", "only-export",
        "only-extern-ok", "only-extern-empty", "only-extern-missing",
        "only-export-correct", "only-export-wrong", "only-export-defined", "only-export-externc", "only-export-dynamic", "only-export-missing"
    ];

    if (values["only-summary"] && wasPassed(detailKeys)) {
        throw new Error("Conflict: Cannot specify detail filters when --only-summary is active.");
    }

    // --- Check 3: Mutually Exclusive Group Presets ---
    if (values["only-extern"] && values["only-export"]) {
        throw new Error("Conflict: Cannot specify both --only-extern and --only-export.");
    }

    // --- Determine Active Sections ---
    const hasExternLeaf = wasPassed(["only-extern-ok", "only-extern-empty", "only-extern-missing"]);
    const hasExportLeaf = wasPassed(["only-export-correct", "only-export-wrong", "only-export-defined", "only-export-externc", "only-export-dynamic", "only-export-missing"]);

    const hasAnyExtern = !!values["only-extern"] || hasExternLeaf;
    const hasAnyExport = !!values["only-export"] || hasExportLeaf;

    // Show a section's details if we explicitly asked for its details, OR if we didn't filter to only show the other section.
    const showExternDetails = hasAnyExtern || !hasAnyExport;
    const showExportDetails = hasAnyExport || !hasAnyExtern;

    // --- Options Merging and Resolution ---
    const showSummary = !values["hide-summary"];
    const showDetails = !values["only-summary"];

    const externConfig = {
        rustOk: showExternDetails && (hasExternLeaf ? !!values["only-extern-ok"] : true),
        rustEmpty: showExternDetails && (hasExternLeaf ? !!values["only-extern-empty"] : true),
        rustMissing: showExternDetails && (hasExternLeaf ? !!values["only-extern-missing"] : true),
    };

    const exportConfig = {
        importCorrect: showExportDetails && (hasExportLeaf ? !!values["only-export-correct"] : true),
        importWrong: showExportDetails && (hasExportLeaf ? !!values["only-export-wrong"] : true),
        definedInRust: showExportDetails && (hasExportLeaf ? !!values["only-export-defined"] : true),
        externC: showExportDetails && (hasExportLeaf ? !!values["only-export-externc"] : true),
        dynamicLookup: showExportDetails && (hasExportLeaf ? !!values["only-export-dynamic"] : true),
        missing: showExportDetails && (hasExportLeaf ? !!values["only-export-missing"] : true),
    };

    return {
        help: false,
        showSummary,
        showDetails,
        externConfig,
        exportConfig,
        genLeanImportsRsStubs: !!values["gen-lean-imports-rs-stubs"],
        appendCommentToLeanImportsFromRust: !!values["append-comment-to-lean-imports-from-rust"],
        appendCommentToRustShouldImportFromLean: !!values["append-comment-to-rust-should-import-from-lean"],
        writeMarkdown: !values["no-write-md"],
    };
}
