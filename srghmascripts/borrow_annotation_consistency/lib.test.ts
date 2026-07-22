import { describe, it, expect } from "bun:test";
import {
  parseCppFunctions,
  parseLeanExterns,
  classifyCppType,
  compareBorrow,
  findCppSignatureDrift,
  pickCanonicalCppFn,
  type CppFn,
} from "./lib";

describe("classifyCppType", () => {
  it("classifies the borrow typedefs", () => {
    expect(classifyCppType("b_lean_obj_arg o")).toBe("b");
    expect(classifyCppType("b_lean_obj_res")).toBe("b");
    expect(classifyCppType("u_lean_obj_arg v")).toBe("u");
    expect(classifyCppType("lean_obj_arg s1")).toBe("owned");
    expect(classifyCppType("lean_obj_res")).toBe("owned");
    expect(classifyCppType("unsigned i")).toBe("other");
    expect(classifyCppType("lean_object * x")).toBe("other");
    // short `namespace lean` aliases (object.h)
    expect(classifyCppType("b_obj_arg a")).toBe("b");
    expect(classifyCppType("obj_arg a")).toBe("owned");
    expect(classifyCppType("u_obj_arg a")).toBe("u");
    expect(classifyCppType("b_obj_res")).toBe("b");
  });
});

describe("parseCppFunctions", () => {
  it("parses a static inline definition (with body)", () => {
    const src = `static inline b_lean_obj_res lean_ctor_get(b_lean_obj_arg o, unsigned i) {\n  return foo;\n}`;
    const fns = parseCppFunctions(src, "lean.h");
    expect(fns).toHaveLength(1);
    const f = fns[0]!;
    expect(f.fnName).toBe("lean_ctor_get");
    expect(f.hasBody).toBe(true);
    expect(f.returnType).toBe("b_lean_obj_res");
    expect(f.returnBorrowed).toBe(true);
    expect(f.args.map((a) => a.kind)).toEqual(["b", "other"]);
    expect(f.args[1]!.raw).toBe("unsigned");
  });

  it("parses a LEAN_EXPORT re-export (no body)", () => {
    const src = `LEAN_EXPORT lean_obj_res lean_decode_io_error(int errnum, b_lean_obj_arg fname);`;
    const fns = parseCppFunctions(src, "lean.h");
    expect(fns).toHaveLength(1);
    const f = fns[0]!;
    expect(f.fnName).toBe("lean_decode_io_error");
    expect(f.hasBody).toBe(false);
    expect(f.returnType).toBe("lean_obj_res");
    expect(f.args.map((a) => a.kind)).toEqual(["other", "b"]);
  });

  it("does not mistake calls for declarations", () => {
    const src = `void other() { object * r = lean_alloc_string(x); return lean_string_append(a, b); }`;
    const fns = parseCppFunctions(src, "object.cpp");
    expect(fns.map((f) => f.fnName)).not.toContain("lean_alloc_string");
    expect(fns.map((f) => f.fnName)).not.toContain("lean_string_append");
  });

  it("parses an extern \"C\" definition with bare object* pointers", () => {
    const src = `extern "C" LEAN_EXPORT object * lean_string_append(object * s1, object * s2) {\n  body;\n}`;
    const fns = parseCppFunctions(src, "object.cpp");
    expect(fns).toHaveLength(1);
    const f = fns[0]!;
    expect(f.fnName).toBe("lean_string_append");
    expect(f.returnType).toBe("object*");
    expect(f.args.map((a) => a.kind)).toEqual(["other", "other"]);
  });

  it("ignores typedef function pointers", () => {
    const src = `typedef void (*lean_external_foreach_proc)(void *, b_lean_obj_arg);`;
    const fns = parseCppFunctions(src, "lean.h");
    expect(fns).toHaveLength(0);
  });

  it("ignores preprocessor directives around a signature", () => {
    const src = `#ifdef LEAN_USE_GMP\nlean_object* lean_alloc_mpz(mpz_t v) { body; }\n#endif`;
    const fns = parseCppFunctions(src, "object.cpp");
    expect(fns).toHaveLength(1);
    expect(fns[0]!.returnType).toBe("lean_object*");
  });

  it("does not treat a `for` comparison as a declaration", () => {
    const src = `void f() { for (unsigned i = 0; i < lean_ctor_num_objs(o); i++) {} }`;
    const fns = parseCppFunctions(src, "object.cpp");
    expect(fns.map((f) => f.fnName)).not.toContain("lean_ctor_num_objs");
  });
});

describe("parseLeanExterns — binder style", () => {
  it("parses def with (s : String) (t : @& String)", () => {
    const src = `@[extern "lean_string_append", expose]\ndef String.append (s : String) (t : @& String) : String where\n  toByteArray := s.toByteArray`;
    const ext = parseLeanExterns(src, "Defs.lean");
    expect(ext).toHaveLength(1);
    expect(ext[0]!.symbolName).toBe("lean_string_append");
    expect(ext[0]!.leanName).toBe("String.append");
    expect(ext[0]!.parseOk).toBe(true);
    expect(ext[0]!.params).toEqual(["N", "B"]);
  });

  it("drops implicit {α : Type} type params", () => {
    const src = `@[extern "lean_array_push"]\ndef Array.push {α : Type u} (xs : Array α) (v : α) : Array α := sorry`;
    const ext = parseLeanExterns(src, "Basic.lean");
    expect(ext[0]!.params).toEqual(["N", "N"]);
  });

  it("expands multi-name borrowed binder (i j : @& Nat)", () => {
    const src = `@[extern "lean_foo"]\ndef swap (xs : Array α) (i j : @& Nat) : Array α := sorry`;
    const ext = parseLeanExterns(src, "Basic.lean");
    expect(ext[0]!.params).toEqual(["N", "B", "B"]);
  });
});

describe("parseLeanExterns — arrow style", () => {
  it("parses opaque append : String → (@& String) → String", () => {
    const src = `@[extern "lean_string_append"]\nopaque append : String → (@& String) → String`;
    const ext = parseLeanExterns(src, "Bootstrap.lean");
    expect(ext[0]!.parseOk).toBe(true);
    expect(ext[0]!.params).toEqual(["N", "B"]);
  });

  it("records attribute-form externs as unparsed", () => {
    const src = `attribute [extern "lean_mk_thunk"] Thunk.mk`;
    const ext = parseLeanExterns(src, "Core.lean");
    expect(ext[0]!.symbolName).toBe("lean_mk_thunk");
    expect(ext[0]!.parseOk).toBe(false);
  });

  it("ignores @& inside comments", () => {
    const src = `-- def foo (x : @& Bar) : Baz\n@[extern "lean_real"]\ndef real (x : Bar) : Baz := sorry`;
    const ext = parseLeanExterns(src, "X.lean");
    expect(ext).toHaveLength(1);
    expect(ext[0]!.params).toEqual(["N"]);
  });
});

describe("compareBorrow", () => {
  const cpp: CppFn = {
    fnName: "lean_string_append",
    returnType: "lean_obj_res",
    returnBorrowed: false,
    args: [
      { raw: "lean_obj_arg", kind: "owned" },
      { raw: "b_lean_obj_arg", kind: "b" },
    ],
    hasBody: false,
    filePath: "lean.h",
    lineNum: 1,
  };

  it("reports no findings when borrow matches", () => {
    const lean = parseLeanExterns(
      `@[extern "lean_string_append"]\ndef String.append (s : String) (t : @& String) : String := sorry`,
      "x.lean",
    )[0]!;
    const cmp = compareBorrow("lean_string_append", cpp, lean);
    expect(cmp.arityMatch).toBe(true);
    expect(cmp.findings).toHaveLength(0);
  });

  it("flags a Lean @& that is not borrowed in CPP", () => {
    const lean = parseLeanExterns(
      `@[extern "lean_string_append"]\ndef String.append (s : @& String) (t : @& String) : String := sorry`,
      "x.lean",
    )[0]!;
    const cmp = compareBorrow("lean_string_append", cpp, lean);
    expect(cmp.findings).toHaveLength(1);
    expect(cmp.findings[0]!.direction).toBe("lean_borrowed_cpp_not");
    expect(cmp.findings[0]!.position).toBe(0);
  });

  it("flags a CPP b_lean_obj_arg that is not @& in Lean", () => {
    const lean = parseLeanExterns(
      `@[extern "lean_string_append"]\ndef String.append (s : String) (t : String) : String := sorry`,
      "x.lean",
    )[0]!;
    const cmp = compareBorrow("lean_string_append", cpp, lean);
    expect(cmp.findings).toHaveLength(1);
    expect(cmp.findings[0]!.direction).toBe("cpp_borrowed_lean_not");
    expect(cmp.findings[0]!.position).toBe(1);
  });
});

describe("findCppSignatureDrift + pickCanonicalCppFn", () => {
  it("treats object* and the borrow typedefs as the same ABI type", () => {
    const fns = parseCppFunctions(
      `extern "C" LEAN_EXPORT object * lean_string_append(object * s1, object * s2) { b; }\nLEAN_EXPORT lean_obj_res lean_string_append(lean_obj_arg s1, b_lean_obj_arg s2);`,
      "mixed",
    );
    // No type-level drift: object* ≡ lean_obj_arg ≡ b_lean_obj_arg at the ABI level.
    expect(findCppSignatureDrift(fns)).toHaveLength(0);
    // Canonical pick keeps the borrow-documented header entry.
    const canon = pickCanonicalCppFn(fns);
    expect(canon.args.map((a) => a.kind)).toEqual(["owned", "b"]);
  });

  it("treats obj/object/lean_object and int width aliases as identical ABI", () => {
    const fns: CppFn[] = [
      { fnName: "lean_x", returnType: "obj*", returnBorrowed: false, args: [{ raw: "obj*", kind: "owned" }, { raw: "unsigned", kind: "other" }], hasBody: true, filePath: "a.cpp", lineNum: 1 },
      { fnName: "lean_x", returnType: "lean_object*", returnBorrowed: false, args: [{ raw: "lean_object*", kind: "other" }, { raw: "uint32_t", kind: "other" }], hasBody: false, filePath: "a.h", lineNum: 2 },
    ];
    expect(findCppSignatureDrift(fns)).toHaveLength(0);
  });

  it("reports genuine type/arity drift", () => {
    const fns: CppFn[] = [
      { fnName: "lean_x", returnType: "lean_obj_res", returnBorrowed: false, args: [{ raw: "int", kind: "other" }], hasBody: false, filePath: "a.h", lineNum: 1 },
      { fnName: "lean_x", returnType: "lean_obj_res", returnBorrowed: false, args: [{ raw: "bool", kind: "other" }], hasBody: true, filePath: "a.cpp", lineNum: 2 },
    ];
    expect(findCppSignatureDrift(fns)).toHaveLength(1);
  });
});
