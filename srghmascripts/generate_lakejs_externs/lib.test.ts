import { describe, it, expect } from "bun:test";
import {
  extractFuncName,
  parseFileExterns,
  extractImports,
  buildScanTree,
  treeToTopoSortedArray,
  generateLakeJsContent,
} from "./lib";

describe("generate_lakejs_externs/lib", () => {
  it("extracts function names correctly", () => {
    expect(extractFuncName("unsafe axiom isScalarObj {α : Type u} (x : α) : Bool")).toBe("isScalarObj");
    expect(extractFuncName("axiom sorryAx (α : Sort u) (synthetic : Bool) : α")).toBe("sorryAx");
    expect(
      extractFuncName("protected def Nat.add : (@& Nat) → (@& Nat) → Nat\n  | a, Nat.zero => a")
    ).toBe("Nat.add");
    expect(extractFuncName("def strictOr (b₁ b₂ : Bool) := b₁ || b₂")).toBe("strictOr");
  });

  it("parses @[extern] and attribute [extern] declarations from Lean content", () => {
    const sample = `
@[extern "lean_is_scalar"]
unsafe axiom isScalarObj {α : Type u} (x : α) : Bool

/-- Doc comment -/
@[extern "lean_sorry", never_extract]
axiom sorryAx (α : Sort u) (synthetic : Bool) : α

@[extern "lean_nat_add", instance_reducible]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

structure UInt8 where
  ofBitVec ::

attribute [extern "lean_uint8_of_nat_mk"] UInt8.ofBitVec
`;

    const fns = parseFileExterns(sample);
    expect(Object.keys(fns)).toContain("isScalarObj");
    expect(Object.keys(fns)).toContain("sorryAx");
    expect(Object.keys(fns)).toContain("Nat.add");
    expect(Object.keys(fns)).toContain("UInt8.ofBitVec");

    expect(fns["isScalarObj"]?.externIdent).toBe("lean_is_scalar");
    expect(fns["isScalarObj"]?.body).toBe("unsafe axiom isScalarObj {α : Type u} (x : α) : Bool");

    expect(fns["sorryAx"]?.externIdent).toBe("lean_sorry");
    expect(fns["sorryAx"]?.body).toBe("axiom sorryAx (α : Sort u) (synthetic : Bool) : α");

    expect(fns["Nat.add"]?.externIdent).toBe("lean_nat_add");
    expect(fns["Nat.add"]?.body).toBe(
      "protected def Nat.add : (@& Nat) → (@& Nat) → Nat\n  | a, Nat.zero   => a\n  | a, Nat.succ b => Nat.succ (Nat.add a b)"
    );

    expect(fns["UInt8.ofBitVec"]?.externIdent).toBe("lean_uint8_of_nat_mk");
    expect(fns["UInt8.ofBitVec"]?.body).toBe('attribute [extern "lean_uint8_of_nat_mk"] UInt8.ofBitVec');
  });

  it("extracts imports correctly while ignoring comments", () => {
    const sample = `
prelude
public import Init.Prelude
-- import Init.Ignored
import all Init.Data.Nat.Basic
meta import Lean.Parser
`;
    const imports = extractImports(sample);
    expect(imports).toEqual(["Init.Prelude", "Init.Data.Nat.Basic", "Lean.Parser"]);
  });

  it("builds a scan tree and topologically sorts with Prelude.lean at the top", () => {
    const files = [
      {
        relPath: "Init/Data/Nat/Basic.lean",
        imports: ["Init.Prelude"],
        functions: {
          "Nat.add": {
            externIdent: "lean_nat_add",
            body: "protected def Nat.add : Nat -> Nat -> Nat",
          },
        },
      },
      {
        relPath: "Init/Prelude.lean",
        imports: [],
        functions: {
          isScalarObj: {
            externIdent: "lean_is_scalar",
            body: "unsafe axiom isScalarObj : Bool",
          },
        },
      },
      {
        relPath: "Init/Data/Nat/Extra.lean",
        imports: ["Init.Data.Nat.Basic"],
        functions: {},
      },
    ];

    const tree = buildScanTree(files);
    expect(tree.kind).toBe("dir");
    expect(tree.children.has("Init")).toBe(true);

    const sorted = treeToTopoSortedArray(tree);
    expect(sorted.length).toBe(3);

    // Prelude.lean must be at index 0
    expect(sorted[0]![0]).toBe("Init/Prelude.lean");
    // Nat/Basic must precede Nat/Extra
    expect(sorted[1]![0]).toBe("Init/Data/Nat/Basic.lean");
    expect(sorted[2]![0]).toBe("Init/Data/Nat/Extra.lean");
  });

  it("generates LakeJs content with Lean and C++ code blocks and existing impls", () => {
    const sorted: Array<[string, Record<string, { externIdent: string; body: string }>]> = [
      [
        "Init/Prelude.lean",
        {
          isScalarObj: {
            externIdent: "lean_is_scalar",
            body: "unsafe axiom isScalarObj {α : Type u} (x : α) : Bool",
          },
          "Nat.beq": {
            externIdent: "lean_nat_dec_eq",
            body: "def Nat.beq : (@& Nat) → (@& Nat) → Bool\n  | zero,   zero   => true",
          },
          "Nat.decEq": {
            externIdent: "lean_nat_dec_eq",
            body: "protected def Nat.decEq (n m : @& Nat) : Decidable (Eq n m) where\n  decide := beq n m",
          },
        },
      ],
    ];

    const cppDefs = new Map<string, string>([
      [
        "lean_is_scalar",
        "static inline uint8_t lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }",
      ],
      [
        "lean_nat_dec_eq",
        "static inline uint8_t lean_nat_dec_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) {\n    return lean_nat_eq(a1, a2);\n}",
      ],
    ]);

    const existingImpls = {
      byModule: new Map([
        [
          "Init/Prelude.lean",
          new Map([
            ["lean_is_scalar", '[JS_EXPR|throw new Error("lean_is_scalar is not and should not be implemented")]'],
            ["lean_nat_dec_eq", "[JS_EXPR|#0 == #1]"],
          ]),
        ],
      ]),
      global: new Map(),
    };

    const content = generateLakeJsContent(sorted, cppDefs, existingImpls);

    expect(content).toContain("import LakeJs.Js");
    expect(content).toContain("-- ============");
    expect(content).toContain("-- Init.Prelude");
    expect(content).toContain("-- ============");

    // Lean block for isScalarObj
    expect(content).toContain("-- ```lean\n-- unsafe axiom isScalarObj {α : Type u} (x : α) : Bool\n-- ```");
    // Cpp block for isScalarObj
    expect(content).toContain("-- ```cpp\n-- static inline uint8_t lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }\n-- ```");
    // Impl for isScalarObj
    expect(content).toContain('def lean_is_scalar := [JS_EXPR|throw new Error("lean_is_scalar is not and should not be implemented")]');

    // Grouping of Nat.beq and Nat.decEq under a single lean_nat_dec_eq
    expect(content).toContain("-- ```lean\n-- def Nat.beq : (@& Nat) → (@& Nat) → Bool\n--   | zero,   zero   => true\n-- ```");
    expect(content).toContain("-- ```lean\n-- protected def Nat.decEq (n m : @& Nat) : Decidable (Eq n m) where\n--   decide := beq n m\n-- ```");
    expect(content).toContain("def lean_nat_dec_eq := [JS_EXPR|#0 == #1]");
  });
});
