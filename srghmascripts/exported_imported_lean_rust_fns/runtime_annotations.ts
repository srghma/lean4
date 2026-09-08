import fs from "node:fs/promises";
import path from "node:path";

const RUNTIME_ANNOTATION_PREFIX = "[lean-audit]";

export type RuntimeAnnotationStatus =
    | "extern_ok"
    | "extern_empty"
    | "extern_missing"
    | "export_correct"
    | "export_wrong"
    | "export_defined"
    | "export_externc"
    | "export_dynamic"
    | "export_missing";

export const isRuntimeRustPath = (filePath: string, rootDir: string) => {
    const relative = path.relative(rootDir, filePath).replaceAll(path.sep, "/");
    return relative.startsWith("src/rust/runtime/") && relative.endsWith(".rs");
};

export const collectRuntimeAnnotation = (
    annotations: Map<string, Map<number, Set<string>>>,
    filePath: string,
    lineNum: number,
    comment: string
) => {
    const byLine = annotations.get(filePath) ?? new Map<number, Set<string>>();
    const items = byLine.get(lineNum) ?? new Set<string>();
    items.add(comment);
    byLine.set(lineNum, items);
    annotations.set(filePath, byLine);
};

export const formatRuntimeAnnotation = (params: {
    kind: "extern" | "export";
    status: RuntimeAnnotationStatus;
    leanPath: string;
    leanLine: number;
}) => {
    const summaryLabel =
        params.kind === "extern"
            ? "Lean imports from Rust ([extern]):"
            : "Rust should import from Lean ([export]):";

    const summaryText =
        params.kind === "extern"
            ? params.status === "extern_ok"
                ? "Rust defined this function and function body is not empty (correct) (✅)"
                : params.status === "extern_empty"
                    ? "Rust defined this function but function body is empty (empty) (⚠️)"
                    : "Rust does not define this function (missing) (❌)"
            : params.status === "export_correct"
                ? "Function is found in rust code and import is correct (correct) (✅)"
                : params.status === "export_wrong"
                    ? "Function is found in rust code, but import is wrong (wrong) (⚠️)"
                    : params.status === "export_defined"
                        ? "Function is found in rust code, but is defined in rust (defined) (🛠️)"
                        : params.status === "export_externc"
                            ? 'Function is found inside of extern "C" block / FFI (externc) (🔌)'
                            : params.status === "export_dynamic"
                                ? "Function is referenced via dynamic string lookup (dynamic) (🔍)"
                                : "Function is not found in rust code (missing) (❌)";

    const parts = [
        `${summaryLabel} ${summaryText}`,
        `Lean: ${params.leanPath}:${params.leanLine}`,
    ];

    return parts.join(" | ");
};

export const appendRuntimeAnnotations = async (annotations: Map<string, Map<number, Set<string>>>) => {
    for (const [filePath, byLine] of annotations) {
        const text = await fs.readFile(filePath, "utf8");
        const lines = text.split("\n");
        let changed = false;

        for (const [lineNum, comments] of byLine) {
            const idx = lineNum - 1;
            const current = lines[idx];
            if (current === undefined) continue;

            const desired = [...comments].sort().join("; ");
            const auditRegex = /\s*\/\/\s*\[lean-audit\].*$/;
            if (current.includes(desired) && current.includes(RUNTIME_ANNOTATION_PREFIX)) continue;

            const currentWithoutAudit = current.replace(auditRegex, "");
            const hasOtherComment = currentWithoutAudit !== current;
            const baseLine = currentWithoutAudit.trimEnd();
            const separator = hasOtherComment || current.includes("//") ? " " : " ";
            lines[idx] = `${baseLine}${separator}// ${RUNTIME_ANNOTATION_PREFIX} ${desired}`;
            changed = true;
        }

        if (changed) {
            await fs.writeFile(filePath, lines.join("\n"));
        }
    }
};
