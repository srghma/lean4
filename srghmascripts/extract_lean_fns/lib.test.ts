import { describe, it, expect } from "vitest";
import {
  stripRustCommentsAndStrings,
  extractBlockContents,
  findLeanFns,
  findLeanFunctionDefinitions,
  parseLeanhDefinitions,
  classifyLeanFn,
  getFnsToDisable
} from "./lib";

describe("Lean Function Extractor and Classifier Library", () => {
  describe("Comments and Strings Stripping", () => {
    it("should strip single line comments, block comments, and string literals", () => {
      const code = `
        // This is a comment
        let x = "lean_inc"; // string literal
        let y = b"lean_dec\\0"; // byte string literal
        /* Block comment
           lean_box */
        lean_unbox(x);
      `;
      const stripped = stripRustCommentsAndStrings(code);
      expect(stripped).not.toContain("This is a comment");
      expect(stripped).not.toContain("lean_inc");
      expect(stripped).not.toContain("lean_dec");
      expect(stripped).not.toContain("lean_box");
      expect(stripped).toContain("lean_unbox");
    });
  });

  describe("Block Scope Extraction", () => {
    it("should strictly extract content inside curly braces, ignoring outer level declarations", () => {
      const code = `
        use lean_runtime::leanh::*;
        fn outer_level() {
          lean_inc();
          if true {
            lean_dec();
          }
        }
      `;
      const stripped = stripRustCommentsAndStrings(code);
      const blocks = extractBlockContents(stripped);
      expect(blocks).not.toContain("use lean_runtime::leanh::*;");
      expect(blocks).not.toContain("fn outer_level()");
      expect(blocks).toContain("lean_inc();");
      expect(blocks).toContain("lean_dec();");
    });
  });

  describe("Symbol Matching", () => {
    it("should extract all valid lean_ symbols", () => {
      const text = "lean_inc(a); lean_dec_ref_cold(b); some_other_fn();";
      const matches = findLeanFns(text);
      expect(matches).toContain("lean_inc");
      expect(matches).toContain("lean_dec_ref_cold");
      expect(matches).not.toContain("some_other_fn");
    });

    it("should extract local lean_ function definitions", () => {
      const definitions = findLeanFunctionDefinitions(`
        pub unsafe fn lean_erase_macro_scopes(x: *mut LeanObject) -> *mut LeanObject { x }
        unsafe fn lean_local_helper() {}
        fn not_lean() {}
      `);

      expect(definitions).toContain("lean_erase_macro_scopes");
      expect(definitions).toContain("lean_local_helper");
      expect(definitions).not.toContain("not_lean");
    });
  });

  describe("leanh.rs Parsing & Classification", () => {
    const mockLeanh = `
      #[inline]
      pub unsafe fn lean_is_scalar(obj: *mut LeanObject) -> bool { true }

      #[cfg(false)]
      #[inline]
      pub unsafe fn lean_ptr_other(obj: *mut LeanObject) -> u8 { 0 }
    `;

    it("should parse active and disabled function definitions correctly", () => {
      const definitions = parseLeanhDefinitions(mockLeanh);

      const isScalar = definitions.get("lean_is_scalar");
      expect(isScalar).toBeDefined();
      expect(isScalar?.disabled).toBe(false);

      const ptrOther = definitions.get("lean_ptr_other");
      expect(ptrOther).toBeDefined();
      expect(ptrOther?.disabled).toBe(true);
    });

    it("should classify matched functions based on parsed definitions map", () => {
      const definitions = parseLeanhDefinitions(mockLeanh);

      const activeStatus = classifyLeanFn("lean_is_scalar", definitions);
      expect(activeStatus.status).toBe("implemented");
      expect(activeStatus.emoji).toBe("");

      const disabledStatus = classifyLeanFn("lean_ptr_other", definitions);
      expect(disabledStatus.status).toBe("disabled");
      expect(disabledStatus.emoji).toBe("⚠️");

      const missingStatus = classifyLeanFn("lean_non_existent", definitions);
      expect(missingStatus.status).toBe("not_implemented");
      expect(missingStatus.emoji).toBe("❌");
    });

    it("should treat concrete lean_ names in macro invocations as definitions", () => {
      const definitions = parseLeanhDefinitions(`
        macro_rules! define_uint_family { () => {} }
        define_uint_family!(
          u8,
          lean_uint8_of_nat,
          lean_uint8_of_nat_mk,
          lean_uint8_to_nat,
          lean_uint8_dec_eq
        );
      `);

      expect(classifyLeanFn("lean_uint8_of_nat", definitions).status).toBe("implemented");
      expect(classifyLeanFn("lean_uint8_of_nat_mk", definitions).status).toBe("implemented");
      expect(classifyLeanFn("lean_uint8_to_nat", definitions).status).toBe("implemented");
      expect(classifyLeanFn("lean_uint8_dec_eq", definitions).status).toBe("implemented");
    });
  });

  describe("Deactivation Check", () => {
    it("should correctly identify active definitions inside leanh.rs that are unused", () => {
      const mockLeanh = `
        pub unsafe fn lean_is_scalar() {}
        pub unsafe fn lean_box() {}
        #[cfg(false)]
        pub unsafe fn lean_ptr_other() {}
      `;
      const definitions = parseLeanhDefinitions(mockLeanh);
      const usedFns = new Set(["lean_is_scalar"]);

      const toDisable = getFnsToDisable(definitions, usedFns);

      // lean_box is active but not used -> should be disabled
      expect(toDisable).toContain("lean_box");
      // lean_is_scalar is active and used -> should NOT be disabled
      expect(toDisable).not.toContain("lean_is_scalar");
      // lean_ptr_other is already disabled -> should NOT be in the "should be disabled" list
      expect(toDisable).not.toContain("lean_ptr_other");
    });
  });
});
