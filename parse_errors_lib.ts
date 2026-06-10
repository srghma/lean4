// ==== FILE: parse_errors_lib.ts ====
import { readdir, mkdir } from "fs/promises";
import { join, normalize } from "path";

// ============================================================================
// Generic Utilities
// ============================================================================

/** Merges multiple Maps of arrays into a single Map of arrays. */
const mergeMultiMaps = <K, V>(maps: Map<K, V[]>[]): Map<K, V[]> => {
  const merged = new Map<K, V[]>();
  for (const map of maps) {
    for (const [key, values] of map) {
      merged.set(key, [...(merged.get(key) ?? []), ...values]);
    }
  }
  return merged;
};

/** Groups items by a string key, counting their frequencies. */
const countFrequencies = <T>(items: T[], keyFn: (item: T) => string): Map<string, number> => {
  const counts = new Map<string, number>();
  for (const item of items) {
    const key = keyFn(item);
    counts.set(key, (counts.get(key) ?? 0) + 1);
  }
  return counts;
};

/** Formats a frequency map into an array of strings, appending a suffix for counts > 1. */
const formatFrequencies = (counts: Map<string, number>, suffixFn = (c: number) => ` (${c}x)`): string[] => {
  return Array.from(counts.entries()).map(([key, count]) =>
    count > 1 ? `${key}${suffixFn(count)}` : key
  );
};

/** Converts a string to a safe, filesystem-friendly filename. */
const toSafeFilename = (str: string, maxLength = 150): string =>
  str
    .replace(/[^a-zA-Z0-9]/g, "_")
    .replace(/_+/g, "_")
    .replace(/^_+|_+$/g, "")
    .substring(0, maxLength)
    .toLowerCase();

// ============================================================================
// Rust Error Parsing Domain
// ============================================================================

export interface Issue {
  file: string;
  line: string;
  codeSnippet: string;
  raw: string;
}

// Strip redundant rustc boilerplate to save tokens
export const cleanTrace = (raw: string): string =>
  raw
    .split("\n")
    .filter(line => {
      const trimmed = line.trim();
      if (trimmed.startsWith("= warning: this was previously accepted")) return false;
      if (trimmed.startsWith("= note: for more information")) return false;
      return true;
    })
    .join("\n")
    .trim();

const parseLocation = (block: string): { fileLocation: string; lineNumber: string } => {
  const locMatch = block.match(/-->\s+([^\n]+)/);
  if (!locMatch) return { fileLocation: "Unknown", lineNumber: "?" };

  const parts = locMatch[1].trim().split(":");
  return parts.length >= 2
    ? { fileLocation: normalize(parts[0]), lineNumber: parts[1] }
    : { fileLocation: normalize(locMatch[1].trim()), lineNumber: "?" };
};

const parseBlock = (block: string): { issueType: string; issue: Issue } | null => {
  block = block.trim();
  if (!block.startsWith("warning: ") && !block.startsWith("error: ")) return null;

  const issueType = block.split("\n")[0].trim();
  const { fileLocation, lineNumber } = parseLocation(block);

  const codeMatch = block.match(/^\s*\d+\s*\|\s*(.*)$/m);
  const codeSnippet = codeMatch ? codeMatch[1].trim() : "";

  return { issueType, issue: { file: fileLocation, line: lineNumber, codeSnippet, raw: block } };
};

const parseFile = (text: string): Map<string, Issue[]> =>
  text
    .replace(/^> /gm, "") // Remove Cargo's blockquote prefix
    .split(/\n(?=warning: |error: )/)
    .reduce((acc, block) => {
      const result = parseBlock(block);
      if (!result) return acc;
      const { issueType, issue } = result;
      acc.set(issueType, [...(acc.get(issueType) ?? []), issue]);
      return acc;
    }, new Map<string, Issue[]>());

const getIssueLocationString = (issue: Issue): string =>
  `${issue.file}:${issue.line}: ${issue.codeSnippet}`;

const deduplicateLocations = (issues: Issue[]): string => {
  const frequencies = countFrequencies(issues, getIssueLocationString);
  return formatFrequencies(frequencies).join("\n");
};

// ============================================================================
// Formatting & File I/O
// ============================================================================

const formatCategory = (issueType: string, issues: Issue[]): string => {
  return [
    `ISSUE TYPE: ${issueType}`,
    `TOTAL OCCURRENCES: ${issues.length}`,
    "",
    `### Trace:\n${cleanTrace(issues[0].raw)}`,
    "",
    `### Locations:\n${deduplicateLocations(issues)}`,
    "",
  ].join("\n");
};

const formatCombined = (groupedIssues: Map<string, Issue[]>): string => {
  const sections = Array.from(groupedIssues.entries()).map(([issueType, issues], i) => {
    return [
      `## [${i + 1}] ${issueType} (${issues.length} occurrences)`,
      "",
      `### Trace:\n${cleanTrace(issues[0].raw)}`,
      "",
      `### Locations:\n${deduplicateLocations(issues)}`,
      "",
    ].join("\n");
  });

  return [`# COMPILER REPORT (${groupedIssues.size} categories)`, "", ...sections].join("\n").trimEnd() + "\n";
};

export const processReports = async (inputDir: string, outputDir: string): Promise<void> => {
  await mkdir(outputDir, { recursive: true });

  let files: string[];
  try {
    files = await readdir(inputDir);
  } catch (err) {
    console.error(`Error reading ${inputDir}`);
    return;
  }

  const fileContents = await Promise.all(
    files.filter(f => f.endsWith(".txt")).map(f => Bun.file(join(inputDir, f)).text())
  );

  const groupedIssues = mergeMultiMaps(fileContents.map(parseFile));

  await Promise.all(
    Array.from(groupedIssues.entries()).map(([issueType, issues], i) =>
      Bun.write(
        join(outputDir, `${i + 1}_${toSafeFilename(issueType)}.txt`),
        formatCategory(issueType, issues)
      )
    )
  );

  if (groupedIssues.size > 0) {
    const combinedPath = join(outputDir, "all_issues_combined.txt");
    await Bun.write(combinedPath, formatCombined(groupedIssues));
    console.log(`\n🎉 Created/Updated ultra-compact file: ${combinedPath}`);
  } else {
    console.log("No issues found to parse.");
  }
};

// ============================================================================
// Cargo Output Extraction & Reporting
// ============================================================================

export const extractReportsFromText = (text: string): { dir: string; id: string }[] => {
  const results: { dir: string; id: string }[] = [];
  const seenIds = new Set<string>();
  let currentDir = "";

  const lines = text.split("\n");
  for (const line of lines) {
    // Note: Captures lines like: Compiling lean_lean_1 v0.1.0 (/home/srghma/.../lean_lean_1)
    const dirMatch = line.match(/^\s*Compiling\s+\S+\s+v[^\s]+\s+\(([^)]+)\)/);
    if (dirMatch) {
      currentDir = dirMatch[1];
    }

    // Note: Captures lines like: note: this report can be shown with `cargo report future-incompatibilities --id 1`
    const idMatch = line.match(/cargo report future-incompatibilities --id (\d+)/);
    if (idMatch && currentDir) {
      const id = idMatch[1];
      if (!seenIds.has(id)) {
        seenIds.add(id);
        results.push({ dir: currentDir, id });
      }
    }
  }
  return results;
};

export const generateRawReport = async (dir: string, id: string, outPath: string): Promise<void> => {
  const proc = Bun.spawn(["cargo", "report", "future-incompatibilities", "--id", id], {
    cwd: dir,
    stdout: "pipe",
    stderr: "ignore",
  });
  const text = await new Response(proc.stdout).text();
  await proc.exited;
  await Bun.write(outPath, text);
};
