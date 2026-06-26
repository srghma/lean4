#!/usr/bin/env bun
import { $ } from "bun";
import { basename, join } from "node:path";

if (process.argv.length !== 3) {
  console.error(`usage: ${basename(process.argv[1])} output-path`);
  process.exit(2);
}

await (async () => {
  try {
    const repoRoot = (await $`git rev-parse --show-toplevel`.text()).trim();
    const outputPath = process.argv[2];

    const templatePath = join(repoRoot, "src/include/lean/lean_header.template");
    const typesDir = join(repoRoot, "src/rust/lean_ffi_types");
    const cbindgenToml = join(typesDir, "cbindgen.toml");

    const rawGeneratedHeader = await $`cbindgen ${typesDir} --config ${cbindgenToml}`.text();
    const typesBlock = processTypes(rawGeneratedHeader);

    const templateText = await Bun.file(templatePath).text();
    const finalizedHeader = injectAndSanitize(templateText, typesBlock);

    await Bun.write(outputPath, finalizedHeader);
  } catch (error) {
    console.error("Pipeline failure:", error);
    process.exit(1);
  }
})();

/**
 * Extracts and decorates the generated types without manual line-by-line iteration.
 */
function processTypes(headerText: string): string {
  const startMarker = "typedef struct LeanObject {";
  const endMarker = "#endif  /* LEAN_H */";

  const startIndex = headerText.indexOf(startMarker);
  const endIndex = headerText.indexOf(endMarker);

  if (startIndex < 0 || endIndex < 0 || endIndex <= startIndex) {
    throw new Error("Could not locate cbindgen block in generated header");
  }

  // 1. Rename PascalCase matches globally
  const renamed = headerText.slice(startIndex, endIndex)
    .replaceAll("[0]", "[]")
    .replaceAll("typedef struct LeanObject {", "typedef struct lean_object {")
    .replaceAll("} LeanObject;", "} lean_object;")
    .replaceAll("struct LeanObject", "lean_object");

  // 2. Isolate and decorate target structs using precise block replacements
  return renamed
    .replace(/typedef struct lean_thunk_object \{[\s\S]*?\} lean_thunk_object;/g, (match) =>
      match
        .replaceAll("lean_object *m_value;", "_Atomic(lean_object *) m_value;")
        .replaceAll("lean_object *m_closure;", "_Atomic(lean_object *) m_closure;")
    )
    .replace(/typedef struct lean_task_object \{[\s\S]*?\} lean_task_object;/g, (match) =>
      match.replaceAll("lean_object *m_value;", "_Atomic(lean_object *) m_value;")
    )
    .replace(/typedef struct lean_once_cell_t \{[\s\S]*?\} lean_once_cell_t;/g, (match) =>
      match
        .replaceAll("int32_t state;", "_Atomic(int) state;")
        .replaceAll("int32_t lock;", "_Atomic(int) lock;")
    );
}

/**
 * Injects the generated types and strips LEAN_MIMALLOC directives.
 */
function injectAndSanitize(template: string, typesBlock: string): string {
  // 1. Strip LEAN_MIMALLOC blocks cleanly
  const sanitized = template.replace(/#ifdef LEAN_MIMALLOC[\s\S]*?#endif\r?\n?/g, "");

  // 2. Inject generated types block (capturing and preserving trailing comments on the b_lean_obj_res line)
  const insertionRegex = /(typedef lean_object \* b_lean_obj_res;.*?)\r?\n[\s\S]*?typedef void \(\*lean_external_finalize_proc\)\(void \*\);/;

  return sanitized.replace(
    insertionRegex,
    `$1\n\n/* BEGIN GENERATED LEAN C ABI TYPES */\n${typesBlock.trimEnd()}\n\n/* END GENERATED LEAN C ABI TYPES */\n\ntypedef void (*lean_external_finalize_proc)(void *);`
  );
}
