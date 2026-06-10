#!/usr/bin/env bun
import { extractReportsFromText, generateRawReport, processReports } from "./parse_errors_lib";
import { mkdir } from "fs/promises";
import { join } from "path";
import { $ } from "bun";

const INPUT_DIR = "/tmp/reports";
const OUTPUT_DIR = "/tmp/reports-short";

await (async () => {
  // Read entire stdin block
  let text = "";
  for await (const chunk of Bun.stdin.stream()) {
    text += new TextDecoder().decode(chunk);
  }

  const reports = extractReportsFromText(text);
  if (reports.length === 0) {
    console.log("No future-incompatibilities reports found in the provided text.");
    return;
  }

  // Clear previous runs
  await $`rm -rf ${INPUT_DIR} ${OUTPUT_DIR}`.nothrow();
  await mkdir(INPUT_DIR, { recursive: true });

  for (const { dir, id } of reports) {
    console.log(`Extracting report ID ${id} from dir ${dir}...`);
    await generateRawReport(dir, id, join(INPUT_DIR, `${id}.txt`));
  }

  console.log("Processing reports...");
  await processReports(INPUT_DIR, OUTPUT_DIR);
})().catch(console.error);
