import { describe, it, expect } from "bun:test";
import path from "node:path";
import fs from "node:fs/promises";
import { spawnSync } from "node:child_process";

const ROOT_DIR = path.resolve(path.join(import.meta.dir, ".."));
const SCRIPT_PATH = path.join(ROOT_DIR, "srghmascripts", "generate_init_funcs.ts");

describe("generate_init_funcs", () => {
  it("shows help message with -h or --help", () => {
    const res = spawnSync(SCRIPT_PATH, ["--help"], { encoding: "utf8" });
    expect(res.status).toBe(0);
    expect(res.stdout).toContain("Usage: lean --run srghmascripts/generate_init_funcs.lean");
    expect(res.stdout).toContain("InitFuncsPure.md and InitFuncsImpure.md");
  });

  it("generates InitFuncsPure.md and InitFuncsImpure.md with markdown tables", async () => {
    const tmpDir = await fs.mkdtemp(path.join(ROOT_DIR, "scratch_test_"));
    try {
      const res = spawnSync(SCRIPT_PATH, ["--out-dir", tmpDir, "Init"], {
        encoding: "utf8",
      });
      expect(res.status).toBe(0);

      const pureFile = path.join(tmpDir, "InitFuncsPure.md");
      const impureFile = path.join(tmpDir, "InitFuncsImpure.md");

      expect(await fs.exists(pureFile)).toBe(true);
      expect(await fs.exists(impureFile)).toBe(true);

      const pureContent = await fs.readFile(pureFile, "utf8");
      const impureContent = await fs.readFile(impureFile, "utf8");

      // Verify unique types list header at the top
      expect(pureContent.startsWith("/-\n")).toBe(true);
      expect(pureContent).toContain("Array Float");
      expect(pureContent).toContain("FloatArray");
      expect(pureContent).toContain("Unit");
      expect(pureContent).toContain("PUnit");

      expect(impureContent.startsWith("/-\n")).toBe(true);
      expect(impureContent).toContain("IO Unit");
      expect(impureContent).toContain("BaseIO Unit");

      // Verify table headers and file sections
      expect(pureContent).toContain("# Init/Prelude.lean");
      expect(pureContent).toMatch(/\|\s*name of extern\s*\|\s*def\s*\|\s*full name of func\s*\|\s*type of func\s*\|/);
      expect(pureContent).toMatch(/\|\s*---+\s*\|\s*---+\s*\|\s*---+\s*\|\s*---+\s*\|/);

      expect(impureContent).toContain("# Init/System/IO.lean");
      expect(impureContent).toMatch(/\|\s*name of extern\s*\|\s*def\s*\|\s*full name of func\s*\|\s*type of func\s*\|/);

      // Verify pure functions in table
      expect(pureContent).toMatch(/\|\s*lean_is_scalar\s*\|\s*axiom\s*\|\s*isScalarObj\s*\|\s*\{α : Type u\} → α → Bool\s*\|/);
      expect(pureContent).toMatch(/\|\s*lean_uint8_of_nat_mk\s*\|\s*constructor\s*\|\s*UInt8\.ofBitVec\s*\|\s*BitVec 8 → UInt8\s*\|/);
      expect(pureContent).toMatch(
        /\|\s*lean_io_process_child_pid\s*\|\s*opaque\s*\|\s*IO\.Process\.Child\.pid\s*\|\s*\{cfg : @& IO\.Process\.StdioConfig\} → IO\.Process\.Child cfg → UInt32\s*\|/
      );
      // Verify function arguments in signatures are enclosed in parentheses (e.g. (Unit → α))
      expect(pureContent).toMatch(
        /\|\s*lean_dbg_sleep\s*\|\s*def\s*\|\s*dbgSleep\s*\|\s*\{α : Type u\} → UInt32 → \(Unit → α\) → α\s*\|/
      );

      // Verify grouped externIdent with aligned columns and deduplicated cells (empty if same as prev row)
      expect(pureContent).toMatch(
        /\|\s*lean_mk_empty_array_with_capacity\s*\|\s*def\s*\|\s*Array\.emptyWithCapacity\s*\|\s*\{α : Type u\} → \(@& Nat\) → Array α\s*\|\n\|\s*\|\s*\|\s*Array\.mkEmpty\s*\|\s*\|/
      );

      expect(pureContent).toMatch(
        /\|\s*lean_uint8_of_nat\s*\|\s*def\s*\|\s*UInt8\.ofNat\s*\|\s*\(@& Nat\) → UInt8\s*\|\n\|\s*\|\s*\|\s*UInt8\.ofNatLT\s*\|\s*\(n : @& Nat\) → instLTNat\.lt n UInt8\.size → UInt8\s*\|/
      );

      // Verify column alignment in every table (every row in a table block has equal length and identical pipe indices)
      for (const content of [pureContent, impureContent]) {
        const sections = content.split(/^# /m).slice(1);
        for (const section of sections) {
          const lines = section.split("\n").filter((l) => l.startsWith("|"));
          if (lines.length > 0) {
            const firstLen = lines[0].length;
            const pipeIndices = [...lines[0]].flatMap((c, i) => (c === "|" ? [i] : []));
            for (const line of lines) {
              expect(line.length).toBe(firstLen);
              const currentPipes = [...line].flatMap((c, i) => (c === "|" ? [i] : []));
              expect(currentPipes).toEqual(pipeIndices);
            }
          }
        }
      }

      // Verify borrowing annotations (@&) are preserved
      expect(pureContent).toMatch(/\|\s*lean_byte_array_size\s*\|\s*def\s*\|\s*ByteArray\.size\s*\|\s*\(@& ByteArray\) → Nat\s*\|/);
      expect(pureContent).toMatch(
        /\|\s*lean_array_get_borrowed\s*\|\s*opaque\s*\|\s*Array\.get!InternalBorrowed\s*\|\s*\{α : Type u\} → \[@& Inhabited α\] → \(@& Array α\) → \(@& Nat\) → α\s*\|/
      );

      // Verify impure functions in table
      expect(impureContent).toMatch(
        /\|\s*lean_io_cancel\s*\|\s*opaque\s*\|\s*IO\.cancel\s*\|\s*\{α : Type u_1\} → \(@& Task α\) → BaseIO Unit\s*\|/
      );
      expect(impureContent).toMatch(
        /\|\s*lean_st_mk_ref\s*\|\s*opaque\s*\|\s*ST\.Prim\.mkRef\s*\|\s*\{σ : Type\} → \{α : Type\} → α → ST σ \(ST\.Ref σ α\)\s*\|/
      );

      // Pure file shouldn't contain IO actions like lean_io_cancel
      expect(pureContent).not.toMatch(/\|\s*lean_io_cancel\s*\|/);
      // Impure file shouldn't contain pure functions like lean_is_scalar
      expect(impureContent).not.toMatch(/\|\s*lean_is_scalar\s*\|/);
    } finally {
      await fs.rm(tmpDir, { recursive: true, force: true });
    }
  });
});
