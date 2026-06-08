import { readdir, mkdir } from "fs/promises";
import { join, normalize } from "path";

export interface Issue {
  file: string;
  line: string;
  codeSnippet: string;
  raw: string;
}

// Strip redundant rustc boilerplate to save tokens
export function cleanTrace(raw: string): string {
  return raw
    .split("\n")
    .filter(line => {
      const trimmed = line.trim();
      if (trimmed.startsWith("= warning: this was previously accepted")) return false;
      if (trimmed.startsWith("= note: for more information")) return false;
      return true;
    })
    .join("\n")
    .trim();
}

export async function processReports(inputDir: string, outputDir: string): Promise<void> {
  await mkdir(outputDir, { recursive: true });

  let files: string[];
  try {
    files = await readdir(inputDir);
  } catch (err) {
    console.error(`Error reading ${inputDir}`);
    return;
  }

  const groupedIssues = new Map<string, Issue[]>();

  for (const file of files) {
    if (!file.endsWith(".txt")) continue;

    const filePath = join(inputDir, file);
    let text = await Bun.file(filePath).text();
    text = text.replace(/^> /gm, ""); // Remove Cargo's blockquote prefix

    const blocks = text.split(/\n(?=warning: |error: )/);

    for (let block of blocks) {
      block = block.trim();
      if (!block.startsWith("warning: ") && !block.startsWith("error: ")) continue;

      const issueType = block.split("\n")[0].trim();

      const locMatch = block.match(/-->\s+([^\n]+)/);
      let fileLocation = "Unknown";
      let lineNumber = "?";

      if (locMatch) {
        const parts = locMatch[1].trim().split(":");
        if (parts.length >= 2) {
          fileLocation = normalize(parts[0]);
          lineNumber = parts[1];
        } else {
          fileLocation = normalize(locMatch[1].trim());
        }
      }

      let codeSnippet = "";
      const codeMatch = block.match(/^\s*\d+\s*\|\s*(.*)$/m);
      if (codeMatch) {
        codeSnippet = codeMatch[1].trim();
      }

      if (!groupedIssues.has(issueType)) {
        groupedIssues.set(issueType, []);
      }

      groupedIssues.get(issueType)!.push({
        file: fileLocation,
        line: lineNumber,
        codeSnippet,
        raw: block,
      });
    }
  }

  let combinedText = `# COMPILER REPORT (${groupedIssues.size} categories)\n\n`;

  let groupIndex = 1;
  for (const [issueType, issues] of groupedIssues.entries()) {
    const safeName = issueType
      .replace(/[^a-zA-Z0-9]/g, "_")
      .replace(/_+/g, "_")
      .replace(/^_+|_+$/g, "")
      .substring(0, 50)
      .toLowerCase();
    const outPath = join(outputDir, `${groupIndex}_${safeName}.txt`);

    let outText = `ISSUE TYPE: ${issueType}\n`;
    outText += `TOTAL OCCURRENCES: ${issues.length}\n\n`;
    outText += `### Trace:\n${cleanTrace(issues[0].raw)}\n\n`;
    outText += `### Locations:\n`;
    for (const issue of issues) {
      outText += `${issue.file}:${issue.line}: ${issue.codeSnippet}\n`;
    }
    outText += "\n";

    // Write individual category file
    await Bun.write(outPath, outText);

    // Append to unified document
    combinedText += `## [${groupIndex}] ${issueType} (${issues.length} occurrences)\n\n`;
    combinedText += `### Trace:\n${cleanTrace(issues[0].raw)}\n\n`;
    combinedText += `### Locations:\n`;
    for (const issue of issues) {
      combinedText += `${issue.file}:${issue.line}: ${issue.codeSnippet}\n`;
    }
    combinedText += "\n";

    groupIndex++;
  }

  if (groupedIssues.size > 0) {
    const combinedPath = join(outputDir, "all_issues_combined.txt");
    await Bun.write(combinedPath, combinedText.trim() + "\n");
    console.log(`\n🎉 Created ultra-compact file: ${combinedPath}`);
  } else {
    console.log("No issues found to parse.");
  }
}
