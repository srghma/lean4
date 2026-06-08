#!/usr/bin/env bun
import { processReports } from "./parse_errors_lib";

const INPUT_DIR = "/tmp/reports";
const OUTPUT_DIR = "/tmp/reports-short";

async function main() {
  await processReports(INPUT_DIR, OUTPUT_DIR);
}

main().catch(console.error);
