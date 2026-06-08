import { readdir, mkdir } from "fs/promises";
import { join, normalize } from "path";

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

const mergeGrouped = (maps: Map<string, Issue[]>[]): Map<string, Issue[]> =>
  maps.reduce((acc, map) => {
    for (const [issueType, issues] of map) {
      acc.set(issueType, [...(acc.get(issueType) ?? []), ...issues]);
    }
    return acc;
  }, new Map<string, Issue[]>());

const formatCategory = (issueType: string, issues: Issue[]): string => {
  const locationLines = issues.map(i => `${i.file}:${i.line}: ${i.codeSnippet}`).join("\n");
  return [
    `ISSUE TYPE: ${issueType}`,
    `TOTAL OCCURRENCES: ${issues.length}`,
    "",
    `### Trace:\n${cleanTrace(issues[0].raw)}`,
    "",
    `### Locations:\n${locationLines}`,
    "",
  ].join("\n");
};

const formatCombined = (groupedIssues: Map<string, Issue[]>): string => {
  const sections = Array.from(groupedIssues.entries()).map(([issueType, issues], i) => {
    const locationLines = issues.map(issue => `${issue.file}:${issue.line}: ${issue.codeSnippet}`).join("\n");
    return [
      `## [${i + 1}] ${issueType} (${issues.length} occurrences)`,
      "",
      `### Trace:\n${cleanTrace(issues[0].raw)}`,
      "",
      `### Locations:\n${locationLines}`,
      "",
    ].join("\n");
  });

  return [`# COMPILER REPORT (${groupedIssues.size} categories)`, "", ...sections].join("\n").trimEnd() + "\n";
};

const safeName = (issueType: string): string =>
  issueType
    .replace(/[^a-zA-Z0-9]/g, "_")
    .replace(/_+/g, "_")
    .replace(/^_+|_+$/g, "")
    .substring(0, 50)
    .toLowerCase();

export const processReports = async (inputDir: string, outputDir: string): Promise<void> => {
  await mkdir(outputDir, { recursive: true });

  let files: string[];
  try {
    files = await readdir(inputDir);
  } catch (err) {
    console.error(`Error reading ${inputDir}`);
    return;
  }

  const groupedIssues = mergeGrouped(
    await Promise.all(
      files
        .filter(f => f.endsWith(".txt"))
        .map(async file => parseFile(await Bun.file(join(inputDir, file)).text()))
    )
  );

  await Promise.all(
    Array.from(groupedIssues.entries()).map(([issueType, issues], i) =>
      Bun.write(
        join(outputDir, `${i + 1}_${safeName(issueType)}.txt`),
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
// New functions for parsing logs and running the cargo report dynamically
// ============================================================================

export const extractReportsFromText = (text: string): { dir: string; id: string }[] => {
  const results: { dir: string; id: string }[] = [];
  const seenIds = new Set<string>();
  let currentDir = "";

  const lines = text.split("\n");
  for (const line of lines) {
    // Look for lines like: Compiling lean_lean_1 v0.1.0 (/home/srghma/.../lean_lean_1)
    const dirMatch = line.match(/^\s*Compiling\s+\S+\s+v[^\s]+\s+\(([^)]+)\)/);
    if (dirMatch) {
      currentDir = dirMatch[1];
    }

    // Look for lines like: note: this report can be shown with `cargo report future-incompatibilities --id 1`
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
