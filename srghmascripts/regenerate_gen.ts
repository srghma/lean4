#!/usr/bin/env bun

import crypto from "node:crypto";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";

type GeneratedFile = {
  leanFile: string;
  rustFile: string;
  moduleRoot: string;
};

type Progress = {
  total: number;
  done: number;
  label: string;
};

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const srcDir = path.join(rootDir, "src");
const lakeSrcDir = path.join(srcDir, "lake");
const rustDir = path.join(rootDir, "src/rust");
const cacheDir = path.join(rootDir, "build/release/stage1/emitrust-cache");
const signatureFile = path.join(cacheDir, ".regen-signature");
const stage1Lean = path.join(rootDir, "build/release/stage1/bin/lean");
const stage1Lib = path.join(rootDir, "build/release/stage1/lib/lean");
const workers = Number(Bun.env.NPROC ?? (os.availableParallelism?.() ?? os.cpus().length));

const generatedRoots = ["Init", "Std", "Lean", "Leanc", "LeanIR", "LeanChecker"];

const rootOutputDirs = new Map([
  ["Init", path.join(rustDir, "gen_init/src/gen")],
  ["Std", path.join(rustDir, "gen_std/src/gen")],
  ["Lean", path.join(rustDir, "gen_lean/src/gen")],
  ["Lake", path.join(rustDir, "lake/src/gen")],
  ["LakeMain", path.join(rustDir, "lake/src/gen")],
  ["Leanc", path.join(rustDir, "leanc/src/gen")],
  ["LeanIR", path.join(rustDir, "lean_ir/src/gen")],
  ["LeanChecker", path.join(rustDir, "lean_checker/src/gen")],
]);

async function* walkFiles(dir: string): AsyncGenerator<string> {
  for (const entry of await fs.readdir(dir, { withFileTypes: true }).catch(() => [])) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      yield* walkFiles(abs);
    } else if (entry.isFile()) {
      yield abs;
    }
  }
}

const collect = async <T>(items: AsyncIterable<T>) => {
  const out: T[] = [];
  for await (const item of items) out.push(item);
  return out;
};

const hashString = (h: crypto.Hash, value: string) => {
  h.update(value);
  h.update("\0");
};

const isGeneratedLeanFile = (file: string) => {
  const rel = path.relative(srcDir, file).replaceAll(path.sep, "/");
  return generatedRoots.some((root) => rel === `${root}.lean` || rel.startsWith(`${root}/`));
};

const isLakeLeanFile = (file: string) => {
  const rel = path.relative(lakeSrcDir, file).replaceAll(path.sep, "/");
  return rel === "Lake.lean" || rel === "LakeMain.lean" || rel.startsWith("Lake/");
};

const outputDirForGeneratedRoot = (moduleRoot: string) => {
  const outputDir = rootOutputDirs.get(moduleRoot);
  if (!outputDir) throw new Error(`no Rust output directory configured for generated root ${moduleRoot}`);
  return outputDir;
};

const rustOutputForLeanFile = (leanFile: string, moduleRoot: string) => {
  const rel = path.relative(moduleRoot, leanFile).replace(/\.lean$/, ".rs");
  const generatedRoot = rel.replaceAll(path.sep, "/").split("/")[0]!.replace(/\.rs$/, "");
  return path.join(outputDirForGeneratedRoot(generatedRoot), rel);
};

const generatedFileForLean = (leanFile: string, moduleRoot: string): GeneratedFile => ({
  leanFile,
  rustFile: rustOutputForLeanFile(leanFile, moduleRoot),
  moduleRoot,
});

const formatProgress = ({ done, total, label }: Progress) => `${label}: ${done}/${total}`;

const computeSignature = async (files: GeneratedFile[]) => {
  const h = crypto.createHash("sha256");
  const leanStats = await fs.stat(stage1Lean);
  hashString(h, `stage1-lean:${leanStats.size}:${leanStats.mtimeMs}`);

  for (const { leanFile } of files) {
    const st = await fs.stat(leanFile);
    hashString(h, path.relative(rootDir, leanFile));
    hashString(h, `${st.size}:${st.mtimeMs}`);
  }

  hashString(h, "regenerate-gen-v7-split-rust-crates-with-local-ffi-module");
  return h.digest("hex");
};

const run = async (args: string[], label: string) => {
  const proc = Bun.spawn(args, {
    cwd: rootDir,
    env: {
      ...Bun.env,
      LEAN_PATH: stage1Lib,
    },
    stdout: "pipe",
    stderr: "pipe",
  });
  const [code, stdout, stderr] = await Promise.all([
    proc.exited,
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
  ]);
  if (code !== 0) {
    throw new Error(
      [
        `${label} failed with exit code ${code}: ${args.join(" ")}`,
        stdout.trim(),
        stderr.trim(),
      ].filter(Boolean).join("\n"),
    );
  }
};

const normalizeRust = (src: string) =>
  src
    .replaceAll("crate::gen::", "crate::r#gen::")
    .replace(/use crate::lean_imports_rs(?:::[A-Za-z0-9_]+)+::\{/g, "use crate::ffi::{")
    .replace(/use crate::lean_imports_rs(?:::[A-Za-z0-9_]+)+::([A-Za-z0-9_]+);/g, "use crate::ffi::$1;")
    .replace(/crate::lean_imports_rs(?:::[A-Za-z0-9_]+)+::([A-Za-z0-9_]+)/g, "crate::ffi::$1")
    .replace(/[ \t]+$/gm, "");

const normalizeRustFile = async (file: string) => {
  const src = await fs.readFile(file, "utf8");
  const normalized = normalizeRust(src);
  if (normalized !== src) {
    await fs.writeFile(file, normalized);
  }
};

const needsLeanRun = async ({ leanFile, rustFile }: GeneratedFile, stage1LeanMtimeMs: number) => {
  const [leanStat, rustStat] = await Promise.all([
    fs.stat(leanFile),
    fs.stat(rustFile).catch(() => null),
  ]);
  return !rustStat || rustStat.mtimeMs < leanStat.mtimeMs || rustStat.mtimeMs < stage1LeanMtimeMs;
};

const generateOne = async (file: GeneratedFile, stage1LeanMtimeMs: number) => {
  await fs.mkdir(path.dirname(file.rustFile), { recursive: true });

  if (await needsLeanRun(file, stage1LeanMtimeMs)) {
    await run(
      [stage1Lean, "-R", file.moduleRoot, "-c", file.rustFile, file.leanFile],
      "stage1 lean",
    );
  }

  await normalizeRustFile(file.rustFile);
  await run(["rustfmt", "--edition", "2024", file.rustFile], "rustfmt");
};

const runWithProgress = async <T>(
  items: readonly T[],
  concurrency: number,
  label: string,
  fn: (item: T, index: number) => Promise<void>,
) => {
  const total = items.length;
  if (total === 0) {
    console.log(`${label}: nothing to do`);
    return;
  }
  let done = 0;
  let next = 0;
  console.log(`${label}: starting ${total} items with ${concurrency} workers`);
  await Promise.all(
    Array.from({ length: Math.min(concurrency, total) }, async () => {
      while (next < total) {
        const index = next++;
        await fn(items[index]!, index);
        done += 1;
        if (done === total || done % 25 === 0) {
          console.log(formatProgress({ done, total, label }));
        }
      }
    }),
  );
};

await (async () => {
  const stage1LeanStat = await fs.stat(stage1Lean).catch(() => {
    throw new Error(`stage1 compiler does not exist: ${stage1Lean}. Run 'just update-stage1' first.`);
  });
  await fs.mkdir(cacheDir, { recursive: true });
  const oldCacheRustFiles = (await collect(walkFiles(cacheDir))).filter((file) => file.endsWith(".rs"));
  if (oldCacheRustFiles.length > 0) {
    console.log(`removing ${oldCacheRustFiles.length} obsolete generated Rust cache files`);
  }
  await runWithProgress(oldCacheRustFiles, workers, "cache rust prune", (file) =>
    fs.rm(file, { force: true }),
  );

  const leanFiles = (await collect(walkFiles(srcDir)))
    .filter((file) => file.endsWith(".lean"))
    .filter(isGeneratedLeanFile)
    .sort();
  const lakeFiles = (await collect(walkFiles(lakeSrcDir)))
    .filter((file) => file.endsWith(".lean"))
    .filter(isLakeLeanFile)
    .sort();
  const generatedFiles = [
    ...leanFiles.map((file) => generatedFileForLean(file, srcDir)),
    ...lakeFiles.map((file) => generatedFileForLean(file, lakeSrcDir)),
  ].sort((a, b) => a.rustFile.localeCompare(b.rustFile));
  const currentOutputs = new Set(generatedFiles.map(({ rustFile }) => rustFile));

  const signature = await computeSignature(generatedFiles);
  const cachedSignature = await fs.readFile(signatureFile, "utf8").catch(() => "");
  const outputNeedsRebuild = await (async () => {
    for (const file of generatedFiles) {
      if (await needsLeanRun(file, stage1LeanStat.mtimeMs)) return true;
    }
    return false;
  })();
  const needsRebuild = cachedSignature.trim() !== signature || outputNeedsRebuild;

  if (needsRebuild) {
    console.log(`generating ${generatedFiles.length} Rust files with ${workers} workers`);
    await runWithProgress(generatedFiles, workers, "stage1 generation", (file) =>
      generateOne(file, stage1LeanStat.mtimeMs),
    );

    await fs.writeFile(signatureFile, `${signature}\n`);
  }

  const outputDirs = [...new Set(rootOutputDirs.values())];
  const staleOutputs = (await Promise.all(outputDirs.map((dir) => collect(walkFiles(dir)))))
    .flat()
    .filter((file) => file.endsWith(".rs"))
    .filter((file) => !currentOutputs.has(file));
  if (staleOutputs.length > 0) {
    console.log(`removing ${staleOutputs.length} stale output files`);
  }
  await runWithProgress(
    staleOutputs,
    workers,
    "output prune",
    (file) => fs.rm(file, { force: true }),
  );

  console.log(
    `regenerated Rust files directly under split crates; signature cache ${path.relative(rootDir, cacheDir)}`,
  );
})().catch((err) => {
  console.error(String(err?.stack ?? err));
  process.exit(1);
});
