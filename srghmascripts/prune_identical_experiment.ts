#!/usr/bin/env bun

import { createHash } from "crypto";
import { readdir, lstat, unlink } from "fs/promises";
import { createReadStream } from "fs";
import path from "path";
import process from "process";

const repoRoot = path.resolve(import.meta.dir, "..");
const experimentRoot = path.join(repoRoot, "src/rust/leanh_l1_experiment");
const originalRoot = path.join(repoRoot, "src/rust/leanh_l1");

type Mode = "dry-run" | "apply";

function usage(): never {
  console.log([
    "Usage:",
    "  bun script/prune_identical_experiment.ts [--apply]",
    "",
    "Defaults to dry-run. Use --apply to delete matching experiment files.",
  ].join("\n"));
  process.exit(1);
}

function parseMode(argv: string[]): Mode {
  if (argv.includes("--help") || argv.includes("-h")) {
    usage();
  }
  if (argv.includes("--apply")) {
    return "apply";
  }
  return "dry-run";
}

async function isFile(filePath: string): Promise<boolean> {
  try {
    return (await lstat(filePath)).isFile();
  } catch {
    return false;
  }
}

async function isDirectory(dirPath: string): Promise<boolean> {
  try {
    return (await lstat(dirPath)).isDirectory();
  } catch {
    return false;
  }
}

async function* walkFiles(root: string, relativeDir = ""): AsyncGenerator<string> {
  const dir = path.join(root, relativeDir);
  const entries = await readdir(dir, { withFileTypes: true });
  entries.sort((a, b) => a.name.localeCompare(b.name));

  for (const entry of entries) {
    const nextRelative = path.join(relativeDir, entry.name);
    if (entry.isDirectory()) {
      yield* walkFiles(root, nextRelative);
      continue;
    }
    if (entry.isFile()) {
      yield nextRelative;
    }
  }
}

async function sha256(filePath: string): Promise<string> {
  const hash = createHash("sha256");
  await new Promise<void>((resolve, reject) => {
    const stream = createReadStream(filePath);
    stream.on("data", (chunk) => hash.update(chunk));
    stream.on("end", () => resolve());
    stream.on("error", reject);
  });
  return hash.digest("hex");
}

async function main() {
  const mode = parseMode(process.argv.slice(2));

  if (!(await isDirectory(originalRoot))) {
    throw new Error(`Original tree not found: ${originalRoot}`);
  }
  if (!(await isDirectory(experimentRoot))) {
    throw new Error(`Experiment tree not found: ${experimentRoot}`);
  }

  const matches: string[] = [];
  let scanned = 0;

  for await (const relativePath of walkFiles(experimentRoot)) {
    scanned += 1;
    const experimentPath = path.join(experimentRoot, relativePath);
    const originalPath = path.join(originalRoot, relativePath);

    if (!(await isFile(originalPath))) {
      continue;
    }

    const [experimentStat, originalStat] = await Promise.all([
      lstat(experimentPath),
      lstat(originalPath),
    ]);

    if (!experimentStat.isFile() || !originalStat.isFile()) {
      continue;
    }

    if (experimentStat.size !== originalStat.size) {
      continue;
    }

    const [experimentHash, originalHash] = await Promise.all([
      sha256(experimentPath),
      sha256(originalPath),
    ]);

    if (experimentHash === originalHash) {
      matches.push(relativePath);
    }
  }

  console.log(`Scanned ${scanned} files in ${path.relative(repoRoot, experimentRoot)}.`);
  console.log(`Found ${matches.length} identical files.`);

  if (matches.length === 0) {
    return;
  }

  for (const relativePath of matches) {
    console.log(`  ${relativePath}`);
  }

  if (mode === "dry-run") {
    console.log("");
    console.log("No files deleted. Re-run with --apply to remove the matched experiment files.");
    return;
  }

  for (const relativePath of matches) {
    await unlink(path.join(experimentRoot, relativePath));
  }

  console.log("");
  console.log(`Deleted ${matches.length} files from ${path.relative(repoRoot, experimentRoot)}.`);
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exit(1);
});
