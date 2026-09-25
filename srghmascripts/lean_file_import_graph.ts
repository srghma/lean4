#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";
import { parseArgs } from "node:util";

type ModuleInfo = {
  module: string;
  relPath: string;
  absPath: string;
  active: boolean;
  deps: Set<string>;
};

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const genDir = path.join(rootDir, "src/rust/lean_runtime/src/gen");
const defaultMermaidOut = path.join(import.meta.dir, "lean_file_import_graph.mermaid");
const defaultReportOut = path.join(import.meta.dir, "lean_file_import_graph.md");

const normalize = (file: string) => file.replaceAll(path.sep, "/");

async function* walk(dir: string): AsyncGenerator<string> {
  for (const entry of await fs.readdir(dir, { withFileTypes: true }).catch(() => [])) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      yield* walk(abs);
    } else if (entry.isFile() && (entry.name.endsWith(".rs") || entry.name.endsWith(".rs_"))) {
      yield abs;
    }
  }
}

const moduleFromFile = (absPath: string) => {
  const rel = normalize(path.relative(genDir, absPath));
  const withoutExt = rel.endsWith(".rs_")
    ? rel.slice(0, -".rs_".length)
    : rel.slice(0, -".rs".length);
  return withoutExt.split("/").join(".");
};

const nodeId = (mod: string) => `m_${mod.replace(/[^A-Za-z0-9_]/g, "_")}`;

const escapeLabel = (s: string) =>
  s.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;").replaceAll('"', "&quot;");

const extractGeneratedImportCandidates = (src: string) => {
  const candidates = new Set<string>();
  const re = /crate::r#gen::([A-Za-z0-9_]+(?:::[A-Za-z0-9_]+)*)/g;
  for (const match of src.matchAll(re)) {
    candidates.add(match[1]!.split("::").join("."));
  }
  return [...candidates];
};

const resolveDep = (candidate: string, moduleSet: Set<string>) => {
  const parts = candidate.split(".");
  while (parts.length > 0) {
    const mod = parts.join(".");
    if (moduleSet.has(mod)) return mod;
    parts.pop();
  }
  return null;
};

const readModules = async () => {
  const files: string[] = [];
  for await (const file of walk(genDir)) files.push(file);
  files.sort();

  const modules = new Map<string, ModuleInfo>();
  for (const absPath of files) {
    const module = moduleFromFile(absPath);
    const relPath = normalize(path.relative(rootDir, absPath));
    modules.set(module, {
      module,
      relPath,
      absPath,
      active: absPath.endsWith(".rs"),
      deps: new Set(),
    });
  }

  const moduleSet = new Set(modules.keys());
  for (const info of modules.values()) {
    const src = await fs.readFile(info.absPath, "utf8");
    for (const candidate of extractGeneratedImportCandidates(src)) {
      const dep = resolveDep(candidate, moduleSet);
      if (dep && dep !== info.module) info.deps.add(dep);
    }
  }

  return modules;
};

const computeLayers = (modules: Map<string, ModuleInfo>, maxLayers: number) => {
  const available = new Set(
    [...modules.values()].filter((info) => info.active).map((info) => info.module),
  );
  const layerByModule = new Map<string, number>();
  for (const mod of available) layerByModule.set(mod, 0);

  for (let layer = 1; layer <= maxLayers; layer++) {
    const ready = [...modules.values()]
      .filter((info) => !available.has(info.module))
      .filter((info) => [...info.deps].every((dep) => available.has(dep)))
      .map((info) => info.module)
      .sort();

    if (ready.length === 0) break;
    for (const mod of ready) {
      available.add(mod);
      layerByModule.set(mod, layer);
    }
  }

  return layerByModule;
};

const missingDeps = (info: ModuleInfo, available: Set<string>) =>
  [...info.deps].filter((dep) => !available.has(dep)).sort();

const renderMermaid = (
  modules: Map<string, ModuleInfo>,
  layerByModule: Map<string, number>,
  includeFull: boolean,
) => {
  const included = includeFull
    ? new Set(modules.keys())
    : new Set([...layerByModule.keys()]);

  const lines = [
    "graph TD",
    "  classDef active fill:#d7f7d7,stroke:#277d27,color:#111;",
    "  classDef ready fill:#fff2b8,stroke:#9f7a00,color:#111;",
    "  classDef later fill:#eef2f7,stroke:#64748b,color:#111;",
    "",
  ];

  for (const mod of [...included].sort()) {
    const info = modules.get(mod)!;
    const layer = layerByModule.get(mod);
    const status = info.active ? ".rs" : `.rs_${layer ? `, wave ${layer}` : ""}`;
    lines.push(`  ${nodeId(mod)}["${escapeLabel(mod)}<br/>${status}"];`);
  }

  lines.push("");
  for (const mod of [...included].sort()) {
    const info = modules.get(mod)!;
    for (const dep of [...info.deps].sort()) {
      if (included.has(dep)) {
        // Edges point in build/unblock direction: dependency -> importer.
        lines.push(`  ${nodeId(dep)} --> ${nodeId(mod)};`);
      }
    }
  }

  lines.push("");
  for (const mod of [...included].sort()) {
    const info = modules.get(mod)!;
    const layer = layerByModule.get(mod);
    const cls = info.active ? "active" : layer === 1 ? "ready" : "later";
    lines.push(`  class ${nodeId(mod)} ${cls};`);
  }

  return `${lines.join("\n")}\n`;
};

const renderReport = (modules: Map<string, ModuleInfo>, layerByModule: Map<string, number>) => {
  const active = [...modules.values()].filter((info) => info.active).sort((a, b) => a.module.localeCompare(b.module));
  const activeSet = new Set(active.map((info) => info.module));
  const inactive = [...modules.values()].filter((info) => !info.active);
  const readyNow = inactive
    .filter((info) => [...info.deps].every((dep) => activeSet.has(dep)))
    .sort((a, b) => a.module.localeCompare(b.module));

  const blocked = inactive
    .filter((info) => !readyNow.includes(info))
    .map((info) => ({ info, missing: missingDeps(info, activeSet) }))
    .sort((a, b) => a.missing.length - b.missing.length || a.info.module.localeCompare(b.info.module));

  const lines = [
    "# Lean Generated Rust Import Graph",
    "",
    `Generated by \`./srghmascripts/lean_file_import_graph.ts\`.`,
    "",
    "Edges in the Mermaid graph point from dependency to importer.",
    "",
    "## Summary",
    "",
    `- Active .rs modules: ${active.length}`,
    `- Inactive .rs_ modules: ${inactive.length}`,
    `- Ready to un-rs_ now: ${readyNow.length}`,
    "",
    "## Active Modules",
    "",
    ...active.map((info) => `- \`${info.module}\` (${info.relPath})`),
    "",
    "## Ready To Un-rs_ Now",
    "",
  ];

  if (readyNow.length === 0) {
    lines.push("- none");
  } else {
    for (const info of readyNow) {
      const deps = [...info.deps].sort();
      lines.push(`- \`${info.module}\` (${info.relPath})${deps.length ? `; deps: ${deps.map((d) => `\`${d}\``).join(", ")}` : "; deps: none"}`);
    }
  }

  const maxLayer = Math.max(0, ...layerByModule.values());
  lines.push("", "## Unblock Waves", "");
  for (let layer = 1; layer <= maxLayer; layer++) {
    const mods = [...layerByModule.entries()]
      .filter(([, value]) => value === layer)
      .map(([mod]) => mod)
      .sort();
    lines.push(`### Wave ${layer}`, "");
    if (mods.length === 0) {
      lines.push("- none", "");
      continue;
    }
    for (const mod of mods) {
      const info = modules.get(mod)!;
      lines.push(`- \`${mod}\` (${info.relPath})`);
    }
    lines.push("");
  }

  lines.push("## Closest Blocked Modules", "");
  for (const { info, missing } of blocked.slice(0, 100)) {
    lines.push(`- \`${info.module}\` (${info.relPath}); missing ${missing.length}: ${missing.map((dep) => `\`${dep}\``).join(", ")}`);
  }

  return `${lines.join("\n")}\n`;
};

const main = async () => {
  const { values } = parseArgs({
    options: {
      layers: { type: "string", default: "2" },
      full: { type: "boolean", default: false },
      "mermaid-out": { type: "string", default: defaultMermaidOut },
      "report-out": { type: "string", default: defaultReportOut },
      help: { type: "boolean", short: "h" },
    },
  });

  if (values.help) {
    console.log("Usage: ./srghmascripts/lean_file_import_graph.ts [--layers 2] [--full]");
    console.log("  --layers N       Include N unblock waves after active .rs modules in the default Mermaid graph.");
    console.log("  --full           Include every generated module in the Mermaid graph.");
    console.log("  --mermaid-out P  Output Mermaid path.");
    console.log("  --report-out P   Output Markdown report path.");
    return;
  }

  const layers = Number(values.layers);
  if (!Number.isInteger(layers) || layers < 0) {
    throw new Error(`--layers must be a non-negative integer, got ${values.layers}`);
  }

  const modules = await readModules();
  const layerByModule = computeLayers(modules, layers);
  const mermaid = renderMermaid(modules, layerByModule, !!values.full);
  const report = renderReport(modules, layerByModule);

  const mermaidOut = path.resolve(String(values["mermaid-out"]));
  const reportOut = path.resolve(String(values["report-out"]));
  await fs.writeFile(mermaidOut, mermaid);
  await fs.writeFile(reportOut, report);

  const activeCount = [...modules.values()].filter((info) => info.active).length;
  const readyCount = [...modules.values()].filter(
    (info) => !info.active && [...info.deps].every((dep) => layerByModule.get(dep) === 0),
  ).length;
  console.log(`Wrote ${normalize(path.relative(rootDir, mermaidOut))}`);
  console.log(`Wrote ${normalize(path.relative(rootDir, reportOut))}`);
  console.log(`Active .rs modules: ${activeCount}`);
  console.log(`Ready to un-rs_ now: ${readyCount}`);
};

await main();
