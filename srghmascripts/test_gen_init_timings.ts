#!/usr/bin/env bun

import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";

type Mode = "build-default" | "build-mold" | "check";
type PassName = "cold" | "hot";

type CellSpec = {
  useSccache: boolean;
  useThreads8: boolean;
  mode: Mode;
};

type PassResult =
  | {
      status: "passed";
      elapsedMs: number;
      peakRssKiB: number;
      logPath: string;
      reportPath?: string;
      command: string;
    }
  | {
      status: "failed" | "skipped";
      elapsedMs?: number;
      reason: string;
      logPath?: string;
      command: string;
    };

type CellResult = {
  cell: CellSpec;
  cold: PassResult;
  hot: PassResult;
};

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const manifestPath = path.join(rootDir, "src/rust/Cargo.toml");
const packageName = "gen_init";
const defaultJobs = Math.max(1, os.availableParallelism?.() ?? os.cpus().length ?? 1);
const hotJobs = 8;
const defaultOutPath = path.join(rootDir, "srghmascripts", "test_gen_init_timings-output.html");

const usage = () => {
  console.error(
    [
      "usage:",
      "  bun srghmascripts/test_gen_init_timings.ts [--out=PATH]",
      "",
      "runs a 2x2x3 matrix for gen_init:",
      "  - with / without RUSTC_WRAPPER=sccache",
      "  - with / without threads=8 parallelism",
      "  - build with default linker / build with mold linker / check",
      "",
      "each cell runs twice:",
      "  - cold run: from a cleaned target dir",
      "  - hot run: second run with the same cell cache state",
      "",
      "output:",
      "  - standalone HTML table written to --out=PATH",
    ].join("\n"),
  );
  process.exit(2);
};

const shQuote = (value: string) => `'${value.replaceAll("'", `'\"'\"'`)}'`;
const escapeHtml = (value: string) =>
  value
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");

const fileUrl = (absolutePath: string) => `file://${absolutePath}`;

const argOut = process.argv.find((arg) => arg.startsWith("--out="));
if (process.argv.includes("--help") || process.argv.includes("-h")) usage();

const outPath = argOut ? path.resolve(argOut.slice("--out=".length)) : defaultOutPath;

async function exists(filePath: string) {
  return fs.stat(filePath).then(() => true).catch(() => false);
}

async function which(cmd: string) {
  const proc = Bun.spawn(["bash", "-lc", `command -v ${shQuote(cmd)}`], {
    stdout: "pipe",
    stderr: "pipe",
  });
  const exitCode = await proc.exited;
  if (exitCode !== 0) return undefined;
  return (await new Response(proc.stdout).text()).trim() || undefined;
}

async function resolveExternalBinary(cmd: string) {
  const proc = Bun.spawn(["bash", "-lc", `type -P ${shQuote(cmd)}`], {
    stdout: "pipe",
    stderr: "pipe",
  });
  const exitCode = await proc.exited;
  if (exitCode !== 0) return undefined;
  return (await new Response(proc.stdout).text()).trim() || undefined;
}

async function newestTimingReport(dir: string) {
  const reports: { file: string; mtimeMs: number }[] = [];

  const walk = async (current: string) => {
    for (const entry of await fs.readdir(current, { withFileTypes: true }).catch(() => [])) {
      const abs = path.join(current, entry.name);
      if (entry.isDirectory()) {
        await walk(abs);
      } else if (entry.isFile() && entry.name.endsWith(".html")) {
        const stat = await fs.stat(abs);
        reports.push({ file: abs, mtimeMs: stat.mtimeMs });
      }
    }
  };

  await walk(dir);
  reports.sort((a, b) => b.mtimeMs - a.mtimeMs);
  return reports[0]?.file;
}

async function tail(filePath: string, lines = 80) {
  const text = await fs.readFile(filePath, "utf8").catch(() => "");
  const chunks = text.split(/\r?\n/);
  return chunks.slice(Math.max(0, chunks.length - lines)).join("\n");
}

function parsePeakRssKiB(text: string) {
  const matches = [...text.matchAll(/Maximum resident set size \(kbytes\):\s+(\d+)/g)];
  const last = matches.at(-1)?.[1];
  return last ? Number(last) : undefined;
}

function buildCommand(cell: CellSpec) {
  const subcommand = cell.mode === "check" ? "check" : "build";
  const jobs = cell.useThreads8 ? hotJobs : defaultJobs;
  return `cargo ${subcommand} --manifest-path ${shQuote(manifestPath)} -p ${packageName} --timings --locked -j ${jobs}`;
}

function modeLabel(mode: Mode) {
  switch (mode) {
    case "build-default":
      return "build/default";
    case "build-mold":
      return "build/mold";
    case "check":
      return "check";
  }
}

function cellName(cell: CellSpec) {
  return [
    cell.useSccache ? "sccache" : "plain",
    cell.useThreads8 ? "threads8" : "threads-default",
    modeLabel(cell.mode).replaceAll("/", "-"),
  ].join("-");
}

async function runPass(
  cell: CellSpec,
  passName: PassName,
  dirs: { tempRoot: string; targetDir: string; sccacheDir: string },
  timeBinary: string,
  moldAvailable: boolean,
): Promise<PassResult> {
  const command = buildCommand(cell);
  const logPath = path.join(dirs.tempRoot, `${passName}.log`);
  const copiedReportPath = path.join(dirs.tempRoot, `${passName}-cargo-timing.html`);

  if (cell.mode === "build-mold" && !moldAvailable) {
    return {
      status: "skipped",
      reason: "mold linker is not available on PATH",
      command,
    };
  }

  if (passName === "cold") {
    await fs.rm(dirs.targetDir, { recursive: true, force: true });
    await fs.mkdir(dirs.targetDir, { recursive: true });
    if (cell.useSccache) {
      await fs.rm(dirs.sccacheDir, { recursive: true, force: true });
      await fs.mkdir(dirs.sccacheDir, { recursive: true });
    }
  } else if (cell.useSccache) {
    await fs.rm(dirs.targetDir, { recursive: true, force: true });
    await fs.mkdir(dirs.targetDir, { recursive: true });
  }

  const envLines: string[] = [
    `export CARGO_TARGET_DIR=${shQuote(dirs.targetDir)}`,
    "export CARGO_INCREMENTAL=0",
    "export CARGO_TERM_COLOR=never",
  ];
  if (cell.useSccache) {
    envLines.push(`export RUSTC_WRAPPER=${shQuote(process.env.RUSTC_WRAPPER || (await which("sccache")) || "sccache")}`);
    envLines.push(`export SCCACHE_DIR=${shQuote(dirs.sccacheDir)}`);
  } else {
    envLines.push("unset RUSTC_WRAPPER || true");
  }
  if (cell.mode === "build-mold") {
    envLines.push(`export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER=clang`);
    envLines.push(`export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS=${shQuote("-C link-arg=-fuse-ld=mold")}`);
  } else {
    envLines.push("unset CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER || true");
    envLines.push("unset CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS || true");
  }

  const innerScript = [
    "set -e",
    "set -o pipefail",
    `cd ${shQuote(rootDir)}`,
    ...envLines,
    `${command}`,
  ].join("\n");
  const timedShellScript = shQuote(innerScript);
  const wrappedScript = [
    "set -o pipefail",
    `cd ${shQuote(rootDir)}`,
    `${timeBinary} -v bash -lc ${timedShellScript} 2>&1 | tee ${shQuote(logPath)}`,
  ].join("\n");

  const start = performance.now();
  const proc = Bun.spawn(["bash", "-lc", wrappedScript], {
    stdout: "pipe",
    stderr: "pipe",
  });
  const exitCode = await proc.exited;
  const elapsedMs = Math.round(performance.now() - start);
  const logExists = await exists(logPath);

  if (exitCode !== 0) {
    return {
      status: "failed",
      elapsedMs,
      reason: logExists ? await tail(logPath) : `cargo exited with code ${exitCode}`,
      logPath,
      command,
    };
  }

  const report = await newestTimingReport(path.join(dirs.targetDir, "cargo-timings"));
  const peakRssKiB = parsePeakRssKiB(await fs.readFile(logPath, "utf8").catch(() => ""));
  if (report) {
    await fs.copyFile(report, copiedReportPath).catch(() => undefined);
  }
  return {
    status: "passed",
    elapsedMs,
    peakRssKiB: peakRssKiB ?? NaN,
    logPath,
    reportPath: report ? copiedReportPath : undefined,
    command,
  };
}

async function runCell(cell: CellSpec, moldAvailable: boolean): Promise<CellResult> {
  const tempRoot = await fs.mkdtemp(path.join(os.tmpdir(), `gen-init-timings-${cellName(cell)}-`));
  const dirs = {
    tempRoot,
    targetDir: path.join(tempRoot, "target"),
    sccacheDir: path.join(tempRoot, "sccache"),
  };
  const timeBinary = (await resolveExternalBinary("time")) ?? (await which("time")) ?? "time";
  return {
    cell,
    cold: await runPass(cell, "cold", dirs, timeBinary, moldAvailable),
    hot: await runPass(cell, "hot", dirs, timeBinary, moldAvailable),
  };
}

function formatDuration(ms?: number) {
  if (ms === undefined) return "n/a";
  const totalSeconds = Math.round(ms / 10) / 100;
  if (totalSeconds < 60) return `${totalSeconds.toFixed(2)}s`;
  const minutes = Math.floor(totalSeconds / 60);
  const seconds = (totalSeconds - minutes * 60).toFixed(2).padStart(5, "0");
  return `${minutes}m${seconds}s`;
}

function formatPeakRssKiB(kib?: number) {
  if (kib === undefined || Number.isNaN(kib)) return "n/a";
  const mib = kib / 1024;
  return `${kib.toLocaleString("en-US")} KiB (${mib.toFixed(1)} MiB)`;
}

function renderResult(result: PassResult) {
  if (result.status === "passed") {
    const time = formatDuration(result.elapsedMs);
    const rss = formatPeakRssKiB(result.peakRssKiB);
    const report = result.reportPath ? `<a href="${escapeHtml(fileUrl(result.reportPath))}">report</a>` : "n/a";
    const log = result.logPath ? `<a href="${escapeHtml(fileUrl(result.logPath))}">log</a>` : "n/a";
    return `<td class="ok">${escapeHtml(result.status)}</td><td class="ok">${escapeHtml(time)}</td><td>${escapeHtml(rss)}</td><td>${report}</td><td>${log}</td>`;
  }
  const note = result.reason;
  return `<td class="${result.status}">${escapeHtml(result.status)}</td><td colspan="4">${escapeHtml(note)}</td>`;
}

function htmlPage(results: CellResult[], moldAvailable: boolean) {
  const rows = results
    .map((result) => {
      const cell = result.cell;
      const wrapper = cell.useSccache ? "on" : "off";
      const threads = cell.useThreads8 ? "8" : "default";
      const mode = modeLabel(cell.mode);
      return `
        <tr>
          <td>${escapeHtml(wrapper)}</td>
          <td>${escapeHtml(threads)}</td>
          <td>${escapeHtml(mode)}</td>
          ${renderResult(result.cold)}
          ${renderResult(result.hot)}
        </tr>`;
    })
    .join("\n");

  const summary = {
    passed: results.filter((result) => result.cold.status === "passed" && result.hot.status === "passed").length,
    failed: results.filter((result) => result.cold.status === "failed" || result.hot.status === "failed").length,
    skipped: results.filter((result) => result.cold.status === "skipped" || result.hot.status === "skipped").length,
  };

  return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>gen_init cargo timings</title>
  <style>
    :root { color-scheme: light; }
    body { font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, sans-serif; margin: 24px; color: #111827; background: #f8fafc; }
    h1 { font-size: 1.5rem; margin: 0 0 12px; }
    .meta, .summary { margin: 0 0 16px; color: #374151; }
    table { border-collapse: collapse; width: 100%; background: white; box-shadow: 0 1px 2px rgba(0,0,0,.05); }
    th, td { border: 1px solid #d1d5db; padding: 8px 10px; text-align: left; vertical-align: top; }
    th { background: #e5e7eb; position: sticky; top: 0; }
    td.ok { color: #065f46; font-weight: 600; }
    td.failed { color: #991b1b; font-weight: 600; }
    td.skipped { color: #92400e; font-weight: 600; }
    code { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
    .notes { margin-top: 12px; color: #4b5563; }
  </style>
</head>
<body>
  <h1>gen_init cargo timings</h1>
  <p class="meta">manifest: <code>${escapeHtml(path.relative(rootDir, manifestPath))}</code> · package: <code>${escapeHtml(packageName)}</code> · default jobs: <code>${defaultJobs}</code> · hot jobs: <code>${hotJobs}</code></p>
  <p class="summary">passed: ${summary.passed} · failed: ${summary.failed} · skipped: ${summary.skipped}${moldAvailable ? "" : " · mold not found on PATH, mold rows skipped"}</p>
  <table>
    <thead>
      <tr>
        <th>sccache</th>
        <th>threads=8</th>
        <th>mode</th>
        <th>cold status</th>
        <th>cold time</th>
        <th>cold peak rss</th>
        <th>cold report</th>
        <th>cold log</th>
        <th>hot status</th>
        <th>hot time</th>
        <th>hot peak rss</th>
        <th>hot report</th>
        <th>hot log</th>
      </tr>
    </thead>
    <tbody>
      ${rows}
    </tbody>
  </table>
</body>
</html>`;
}

async function main() {
  const moldAvailable = (await which("mold")) !== undefined;
  const cells: CellSpec[] = [];
  for (const useSccache of [false, true]) {
    for (const useThreads8 of [false, true]) {
      for (const mode of ["build-default", "build-mold", "check"] as const) {
        cells.push({ useSccache, useThreads8, mode });
      }
    }
  }

  const results: CellResult[] = [];
  for (const cell of cells) {
    console.error(`running ${cellName(cell)}...`);
    results.push(await runCell(cell, moldAvailable));
  }

  const html = htmlPage(results, moldAvailable);
  await fs.writeFile(outPath, html);
  console.log(`wrote ${path.relative(rootDir, outPath)}`);
}

main().catch((err) => {
  console.error(String(err?.stack ?? err));
  process.exit(1);
});
