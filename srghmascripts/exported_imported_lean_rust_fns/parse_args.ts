import { parseArgs } from "node:util";

const options = {
    // Help toggle
    "help": { type: "boolean", short: "h" },

    // Summary visibility toggles
    "show-summary": { type: "boolean" },
    "hide-summary": { type: "boolean" },
    "show-only-summary": { type: "boolean" },

    // Group visibility presets
    "extern-all": { type: "boolean" },
    "extern-none": { type: "boolean" },
    "export-all": { type: "boolean" },
    "export-none": { type: "boolean" },

    // Individual [extern] Leaf toggles
    "show-extern-ok": { type: "boolean" },
    "hide-extern-ok": { type: "boolean" },
    "show-extern-empty": { type: "boolean" },
    "hide-extern-empty": { type: "boolean" },
    "show-extern-missing": { type: "boolean" },
    "hide-extern-missing": { type: "boolean" },

    // Individual [export] Leaf toggles
    "show-export-correct": { type: "boolean" },
    "hide-export-correct": { type: "boolean" },
    "show-export-wrong": { type: "boolean" },
    "hide-export-wrong": { type: "boolean" },
    "show-export-defined": { type: "boolean" },
    "hide-export-defined": { type: "boolean" },
    "show-export-externc": { type: "boolean" },
    "hide-export-externc": { type: "boolean" },
    "show-export-missing": { type: "boolean" },
    "hide-export-missing": { type: "boolean" },
} as const;

/**
 * Prints CLI usage instructions
 */
export function printHelp() {
    console.log(`
Usage: ./srghmascripts/exported_imported_lean_rust_fns.ts [options]

Options:
  -h, --help                               Show this help message

  Summary Visibility:
    --show-summary                         Always print the summary block (default: true)
    --hide-summary                         Do not print the summary block
    --show-only-summary                    Only print the summary block (hides detail listings)

  Group Visibility Presets:
    --extern-all                           Show all Lean imports from Rust (extern)
    --extern-none                          Hide all Lean imports from Rust (extern) by default
    --export-all                           Show all Rust imports from Lean (export)
    --export-none                          Hide all Rust imports from Lean (export) by default

  Detailed Leaf Toggles:
    Lean imports from Rust ([extern]):
      --show-extern-ok / --hide-extern-ok
      --show-extern-empty / --hide-extern-empty
      --show-extern-missing / --hide-extern-missing

    Rust should import from Lean ([export]):
      --show-export-correct / --hide-export-correct
      --show-export-wrong / --hide-export-wrong
      --show-export-defined / --hide-export-defined
      --show-export-externc / --hide-export-externc
      --show-export-missing / --hide-export-missing
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
            exportConfig: { importCorrect: false, importWrong: false, definedInRust: false, externC: false, missing: false },
        };
    }

    const wasPassed = (keys: (keyof typeof options)[]) =>
        keys.some(k => values[k] !== undefined);

    // --- Check 1: Contradictory Summary Parameters ---
    if (values["show-summary"] && values["hide-summary"]) {
        throw new Error("Conflict: Cannot specify both --show-summary and --hide-summary.");
    }
    if (values["show-only-summary"] && values["hide-summary"]) {
        throw new Error("Conflict: Cannot specify both --show-only-summary and --hide-summary.");
    }

    // --- Check 2: Detail Filtering Redundancy ---
    const detailKeys: (keyof typeof options)[] = [
        "extern-all", "extern-none", "export-all", "export-none",
        "show-extern-ok", "hide-extern-ok",
        "show-extern-empty", "hide-extern-empty",
        "show-extern-missing", "hide-extern-missing",
        "show-export-correct", "hide-export-correct",
        "show-export-wrong", "hide-export-wrong",
        "show-export-defined", "hide-export-defined",
        "show-export-externc", "hide-export-externc",
        "show-export-missing", "hide-export-missing"
    ];

    if (values["show-only-summary"] && wasPassed(detailKeys)) {
        throw new Error("Conflict: Cannot specify individual visibility flags when --show-only-summary is active.");
    }

    // --- Check 3: Mutually Exclusive Group Presets ---
    if (values["extern-all"] && values["extern-none"]) {
        throw new Error("Conflict: Cannot specify both --extern-all and --extern-none.");
    }
    if (values["export-all"] && values["export-none"]) {
        throw new Error("Conflict: Cannot specify both --export-all and --export-none.");
    }

    // --- Check 4: Opposite Leaf Toggle Pairs ---
    const opposingPairs: [keyof typeof options, keyof typeof options][] = [
        ["show-extern-ok", "hide-extern-ok"],
        ["show-extern-empty", "hide-extern-empty"],
        ["show-extern-missing", "hide-extern-missing"],
        ["show-export-correct", "hide-export-correct"],
        ["show-export-wrong", "hide-export-wrong"],
        ["show-export-defined", "hide-export-defined"],
        ["show-export-externc", "hide-export-externc"],
        ["show-export-missing", "hide-export-missing"],
    ];

    for (const [showKey, hideKey] of opposingPairs) {
        if (values[showKey] && values[hideKey]) {
            throw new Error(`Conflict: Cannot specify both --${showKey} and --${hideKey}.`);
        }
    }

    // --- Options Merging and Resolution ---
    let showSummary = true;
    if (values["hide-summary"]) showSummary = false;
    if (values["show-only-summary"]) showSummary = true;

    // Initialize defaults
    const externConfig = {
        rustOk: true,
        rustEmpty: true,
        rustMissing: true,
    };

    if (values["extern-none"]) {
        externConfig.rustOk = false;
        externConfig.rustEmpty = false;
        externConfig.rustMissing = false;
    }

    // Evaluate explicit overrides for Lean-from-Rust (externs)
    if (values["show-extern-ok"] !== undefined) externConfig.rustOk = values["show-extern-ok"];
    if (values["hide-extern-ok"] !== undefined) externConfig.rustOk = !values["hide-extern-ok"];
    if (values["show-extern-empty"] !== undefined) externConfig.rustEmpty = values["show-extern-empty"];
    if (values["hide-extern-empty"] !== undefined) externConfig.rustEmpty = !values["hide-extern-empty"];
    if (values["show-extern-missing"] !== undefined) externConfig.rustMissing = values["show-extern-missing"];
    if (values["hide-extern-missing"] !== undefined) externConfig.rustMissing = !values["hide-extern-missing"];

    const exportConfig = {
        importCorrect: true,
        importWrong: true,
        definedInRust: true,
        externC: true,
        missing: true,
    };

    if (values["export-none"]) {
        exportConfig.importCorrect = false;
        exportConfig.importWrong = false;
        exportConfig.definedInRust = false;
        exportConfig.externC = false;
        exportConfig.missing = false;
    }

    // Evaluate explicit overrides for Rust-from-Lean (exports)
    if (values["show-export-correct"] !== undefined) exportConfig.importCorrect = values["show-export-correct"];
    if (values["hide-export-correct"] !== undefined) exportConfig.importCorrect = !values["hide-export-correct"];

    if (values["show-export-wrong"] !== undefined) exportConfig.importWrong = values["show-export-wrong"];
    if (values["hide-export-wrong"] !== undefined) exportConfig.importWrong = !values["hide-export-wrong"];

    if (values["show-export-defined"] !== undefined) exportConfig.definedInRust = values["show-export-defined"];
    if (values["hide-export-defined"] !== undefined) exportConfig.definedInRust = !values["hide-export-defined"];

    if (values["show-export-externc"] !== undefined) exportConfig.externC = values["show-export-externc"];
    if (values["hide-export-externc"] !== undefined) exportConfig.externC = !values["hide-export-externc"];

    if (values["show-export-missing"] !== undefined) exportConfig.missing = values["show-export-missing"];
    if (values["hide-export-missing"] !== undefined) exportConfig.missing = !values["hide-export-missing"];

    return {
        help: false,
        showSummary,
        showDetails: !values["show-only-summary"],
        externConfig,
        exportConfig,
    };
}
