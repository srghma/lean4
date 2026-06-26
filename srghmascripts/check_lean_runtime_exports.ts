#!/usr/bin/env bun
import { $ } from "bun";

const repoRoot = (await $`git rev-parse --show-toplevel`.text()).trim();
process.chdir(repoRoot);

const diff = await $`git diff --cached --unified=0 -- src/rust/lean_runtime/src`.text();

let currentFile = "";
const violations: string[] = [];

for (const line of diff.split("\n")) {
  if (line.startsWith("diff --git ")) {
    currentFile = "";
    continue;
  }
  if (line.startsWith("+++ b/")) {
    currentFile = line.slice(6).trim();
    continue;
  }

  if (
    currentFile &&
    currentFile !== "src/rust/lean_runtime/src/foreign_ffi.rs" &&
    line.startsWith("+") &&
    !line.startsWith("+++")
  ) {
    const addedLine = line.slice(1);
    if (/no_mangle|export_name/.test(addedLine)) {
      violations.push(`${currentFile}:${addedLine}`);
    }
  }
}

if (violations.length > 0) {
  console.error("export attributes are only allowed in src/rust/lean_runtime/src/foreign_ffi.rs\n");
  for (const violation of violations) {
    console.error(violation);
  }
  process.exit(1);
}
