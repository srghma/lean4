import type {
  ExternReportItem,
  ExportReportItem,
  MarkdownReportBlock,
} from "./md_report";

export type ReportStats = {
  extern: { total: number; ok: number; empty: number; missing: number };
  export: {
    total: number;
    ok: number;
    wrong: number;
    definedRust: number;
    externC: number;
    dynamicLookup: number;
    missing: number;
  };
};

export type JsonReport<T> = {
  generatedAt: string;
  kind: "lean_imports_from_rust" | "rust_should_import_from_lean";
  stats: ReportStats;
  blocks: Array<{
    relativePath: string;
    items: T[];
  }>;
  bySymbol: Record<
    string,
    Array<{
      relativePath: string;
      item: T;
    }>
  >;
};

export function buildJsonReport<T extends { symbolName: string }>(
  kind: JsonReport<T>["kind"],
  stats: ReportStats,
  blocks: MarkdownReportBlock<T>[],
): JsonReport<T> {
  const bySymbol: JsonReport<T>["bySymbol"] = {};
  for (const block of blocks) {
    for (const item of block.items) {
      const entries = bySymbol[item.symbolName] ?? [];
      entries.push({ relativePath: block.relativePath, item });
      bySymbol[item.symbolName] = entries;
    }
  }
  return {
    generatedAt: new Date().toISOString(),
    kind,
    stats,
    blocks: blocks.map((block) => ({
      relativePath: block.relativePath,
      items: block.items,
    })),
    bySymbol,
  };
}

export type LeanImportsFromRustJson = JsonReport<ExternReportItem>;
export type RustShouldImportFromLeanJson = JsonReport<ExportReportItem>;
