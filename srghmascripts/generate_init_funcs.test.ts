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
        /\|\s*lean_uint8_of_nat\s*\|\s*def\s*\|\s*UInt8\.ofNat\s*\|\s*\(@& Nat\) → UInt8\s*\|\n\|\s*\|\s*def 🌌\s*\|\s*UInt8\.ofNatLT\s*\|\s*\(n : @& Nat\) → \(h : n < UInt8\.size\) → UInt8\s*\|/
      );

      // Verify column alignment in every table (every row in a table block has equal length and identical pipe indices)
      for (const content of [pureContent, impureContent]) {
        const sections = content.split(/^# /m).slice(1);
        for (const section of sections) {
          const lines = section.split("\n").filter((l) => l.startsWith("|"));
          if (lines.length > 0) {
            const firstLen = [...lines[0]].length;
            const pipeIndices = [...lines[0]].flatMap((c, i) => (c === "|" ? [i] : []));
            for (const line of lines) {
              expect([...line].length).toBe(firstLen);
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
      expect(impureContent).toMatch(
        /\|\s*lean_io_wait_any\s*\|\s*opaque 🌌\s*\|\s*IO\.waitAny\s*\|/
      );

      // Verify universe emoji 🌌 marks functions requiring proof arguments
      expect(pureContent).toMatch(
        /\|\s*lean_string_from_utf8_unchecked\s*\|\s*constructor 🌌\s*\|\s*String\.ofByteArray\s*\|/
      );
      expect(pureContent).toMatch(
        /\|\s*lean_array_fget_borrowed\s*\|\s*opaque 🌌\s*\|\s*Array\.getInternalBorrowed\s*\|/
      );

      // Pure file shouldn't contain IO actions like lean_io_cancel
      expect(pureContent).not.toMatch(/\|\s*lean_io_cancel\s*\|/);
      // Impure file shouldn't contain pure functions like lean_is_scalar
      expect(impureContent).not.toMatch(/\|\s*lean_is_scalar\s*\|/);

      // Verify generated .lean files
      const pureLeanFile = "/home/srghma/projects/leanscript/LeanScript/LeanInitPureExterns.lean";
      const impureLeanFile = "/home/srghma/projects/leanscript/LeanScript/LeanInitImpureExterns.lean";
      expect(await fs.exists(pureLeanFile)).toBe(true);
      expect(await fs.exists(impureLeanFile)).toBe(true);

      const pureLeanContent = await fs.readFile(pureLeanFile, "utf8");
      const impureLeanContent = await fs.readFile(impureLeanFile, "utf8");

      expect(pureLeanContent).toContain("inductive LeanInitPureExtern : MyTy → Type where");
      expect(impureLeanContent).toContain("inductive LeanInitImpureExtern : MyTy → Type where");

      // Verify constructor formats and sanitized hygiene names
      expect(pureLeanContent).toContain("| lean_uint32_of_nat_mk : BitVec 32 → LeanInitPureExtern uint32 -- UInt32.ofBitVec");
      expect(pureLeanContent).toContain("| lean_float_array_uget : (a : FloatArray) → (i : USize) → (h : i.toNat < a.size) → LeanInitPureExtern float -- FloatArray.uget");
      expect(pureLeanContent).not.toContain("._@._internal");
      expect(pureLeanContent).toContain("| lean_array_fset : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → denote αt → (h : i < xs.size := by get_elem_tactic) → LeanInitPureExtern (array αt) -- Array.set");
      expect(pureLeanContent).toContain("| lean_array_get_borrowed : (αt : MyTy) → (inhabited_default : denote αt) → Array (denote αt) → Nat → LeanInitPureExtern αt -- Array.get!InternalBorrowed");
      expect(pureLeanContent).toContain("| lean_panic_fn_borrowed : (αt : MyTy) → String → LeanInitPureExtern αt -- panicCore");
      expect(pureLeanContent).toContain("| lean_system_platform_nbits : LeanInitPureExtern (lazy nat) -- System.Platform.getNumBits");
      expect(pureLeanContent).toContain("| lean_substring_drop : Substring.Raw → Nat → LeanInitPureExtern substringRaw -- Substring.Raw.Internal.drop");
      expect(pureLeanContent).toContain("| lean_substring_prev : Substring.Raw → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- Substring.Raw.Internal.prev");
      expect(pureLeanContent).toContain("| lean_version_get_is_release : LeanInitPureExtern (lazy LeanPrimTy.bool) -- Lean.version.getIsRelease");
      expect(pureLeanContent).toContain("| lean_string_utf8_next_fast__String_Pos_next : {s : String} → (pos : s.Pos) → (h : pos ≠ s.endPos) → LeanInitPureExtern (LeanPrimTy.stringPos s) -- String.Pos.next");
      expect(pureLeanContent).toContain("| lean_float_frexp : Float → LeanInitPureExtern (prod float int) -- Float.frExp");
      expect(pureLeanContent).toContain("| lean_float_to_bits__Float_toModel : Float → LeanInitPureExtern floatModel -- Float.toModel");
      expect(pureLeanContent).toContain("| lean_io_promise_result_opt : (αt : MyTy) → IO.Promise (denote αt) → LeanInitPureExtern (task (option αt)) -- IO.Promise.result?");
      expect(pureLeanContent).toContain("| lean_state_sharecommon : (αt : MyTy) → {σ : ShareCommon.StateFactory} → ShareCommon.State σ → denote αt → LeanInitPureExtern (prod αt (shareCommonState σ)) -- ShareCommon.State.shareCommon");

      // Verify cross-file duplicate externs are disambiguated with decl names
      expect(pureLeanContent).toContain("| lean_uint64_to_nat__UInt64_toBitVec : UInt64 → LeanInitPureExtern (bitvec 64) -- UInt64.toBitVec");
      expect(pureLeanContent).toContain("| lean_uint64_to_nat__UInt64_toNat : UInt64 → LeanInitPureExtern nat -- UInt64.toNat");
    } finally {
      await fs.rm(tmpDir, { recursive: true, force: true });
    }
  });
});
