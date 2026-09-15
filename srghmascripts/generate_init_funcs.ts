#!/usr/bin/env bun
import path from "node:path";
import { spawnSync } from "node:child_process";

const SCRIPT_DIR = import.meta.dir;
const LEAN_SCRIPT = path.join(SCRIPT_DIR, "generate_init_funcs.lean");

const args = ["--run", LEAN_SCRIPT, ...process.argv.slice(2)];
const result = spawnSync("lean", args, {
  stdio: "inherit",
});

process.exit(result.status ?? 0);
