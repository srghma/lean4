#!/usr/bin/env bun

import fs from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import { parseArgs } from "node:util";
import {
  resolveTargetFiles,
  processFiles,
  parseLeanhDefinitions,
  classifyLeanFn,
  getFnsToDisable
} from "./extract_lean_fns/lib";

const useColors = !!process.stdout.isTTY && !process.env.NO_COLOR;
const colors = useColors ? {
  reset: "\x1b[0m",
  bold: "\x1b[1m",
  cyan: "\x1b[36m",
  green: "\x1b[32m",
  yellow: "\x1b[33m",
  red: "\x1b[31m",
  dim: "\x1b[2m",
} : {
  reset: "",
  bold: "",
  cyan: "",
  green: "",
  yellow: "",
  red: "",
  dim: "",
};

const c = {
  header: (text: string) => `${colors.cyan}${colors.bold}${text}${colors.reset}`,
  file: (text: string) => `${colors.bold}${text}${colors.reset}`,
  error: (text: string) => `${colors.red}${colors.bold}${text}${colors.reset}`,
  dim: (text: string) => `${colors.dim}${text}${colors.reset}`,
};

(async () => {
  const { values, positionals } = parseArgs({
    options: {
      exclude: {
        type: "string",
        multiple: true,
        short: "e",
      },
      "leanh-path": {
        type: "string",
        default: "/home/srghma/projects/lean4/src/rust/lean_runtime/src/leanh.rs"
      },
      help: {
        type: "boolean",
        short: "h",
      },
    },
    allowPositionals: true,
  });

  if (values.help || positionals.length === 0) {
    console.log(`${colors.bold}Usage:${colors.reset} ./srghmascripts/extract_lean_fns.ts <file.rs | directory | glob_pattern> [options]`);
    console.log(`\nOptions:`);
    console.log(`  -h, --help           Show this help message`);
    console.log(`  -e, --exclude        Exclude specific glob patterns (can be specified multiple times)`);
    console.log(`  --leanh-path         Path to leanh.rs (defaults to standard repo location)`);
    process.exit(0);
  }

  const leanhPath = values["leanh-path"] as string;
  if (!existsSync(leanhPath)) {
    console.error(c.error(`Error: Could not locate leanh.rs at ${leanhPath}`));
    process.exit(1);
  }

  // Parse definitions from standard/overridden leanh.rs file
  const leanhContent = await fs.readFile(leanhPath, "utf8");
  const leanhMap = parseLeanhDefinitions(leanhContent);

  const excludePatterns = values.exclude ?? [];
  const filesToProcess = await resolveTargetFiles(positionals, excludePatterns);

  if (filesToProcess.length === 0) {
    console.error(c.error("Error: No valid Rust (.rs) files found matching the provided arguments."));
    process.exit(1);
  }

  console.log(c.dim(`Scanning ${filesToProcess.length} file(s)...`));
  console.log(c.dim(`Using leanh.rs definitions from: ${leanhPath}\n`));

  const reports = await processFiles(filesToProcess);

  if (reports.length > 0) {
    console.log(c.header("# Breakdown of used lean_ functions by file:\n"));

    for (const report of reports) {
      const relativePath = path.relative(process.cwd(), report.filePath);
      console.log(`  ${c.file(relativePath)} (${c.dim(`${report.found.length} fns`)})`);

      for (const fn of report.found) {
        const classification = report.localDefinitions.includes(fn)
          ? { status: "implemented" as const }
          : classifyLeanFn(fn, leanhMap);
        if (classification.status === "not_implemented") {
          console.log(`    - ❌ ${colors.red}${fn}${colors.reset}`);
        } else if (classification.status === "disabled") {
          console.log(`    - ⚠️  ${colors.yellow}${fn}${colors.reset}`);
        } else {
          console.log(`    - ${colors.green}${fn}${colors.reset}`);
        }
      }
      console.log();
    }
  }

  // Unique aggregate summary
  const allUniqueFns = Array.from(new Set(reports.flatMap(r => r.found))).sort();
  const allLocalDefinitions = new Set(reports.flatMap(r => r.localDefinitions));
  const usedFnsSet = new Set(allUniqueFns);
  const fnsToDisable = getFnsToDisable(leanhMap, usedFnsSet);

  console.log("========================================================================");
  console.log(`${colors.bold}SUMMARY of all lean_ functions found across scanned files (${allUniqueFns.length}):${colors.reset}`);
  console.log("========================================================================");

  if (allUniqueFns.length > 0) {
    for (const fn of allUniqueFns) {
      const classification = allLocalDefinitions.has(fn)
        ? { status: "implemented" as const }
        : classifyLeanFn(fn, leanhMap);
      if (classification.status === "not_implemented") {
        console.log(`  - ❌ ${colors.red}${fn}${colors.reset}`);
      } else if (classification.status === "disabled") {
        console.log(`  - ⚠️  ${colors.yellow}${fn}${colors.reset}`);
      } else {
        console.log(`  - ${colors.green}${fn}${colors.reset}`);
      }
    }
  } else {
    console.log("  No occurrences starting with 'lean_' found inside function blocks.");
  }

  console.log("========================================================================");
  console.log(`${colors.bold}FUNCTIONS IN leanh.rs THAT SHOULD BE DISABLED (Active but Unused) (${fnsToDisable.length}):${colors.reset}`);
  console.log("========================================================================");

  if (fnsToDisable.length > 0) {
    for (const fn of fnsToDisable) {
      console.log(`  - ⚠️  ${colors.dim}${fn}${colors.reset}`);
    }
  } else {
    console.log("  No active functions are unused. All defined functions are currently active and used.");
  }
  console.log("========================================================================");
})();
