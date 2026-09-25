import { describe, it, expect } from "vitest";
import {
    scanLeanFile,
    findSymbolsInRust,
    classifyRustLine,
    getCorrectRustUsePath,
    stripRustComments,
    stripLeanComments,
    isIndexInRustString,
    type RustSearchResult
} from "./lib";

describe("FFI Checker Parser & Classification Engine", () => {

    describe("Comment Stripping Logic", () => {
        it("should correctly strip single and block comments from Lean code", () => {
            const code = "-- this is a line comment\n@[extern] def foo : Nat\n/- block comment -/";
            const stripped = stripLeanComments(code);
            expect(stripped).not.toContain("this is a line comment");
            expect(stripped).toContain("def foo");
        });

        it("should correctly strip single and block comments from Rust code", () => {
            const code = "// this is a line comment\nfn foo() {}\n/* block comment */";
            const stripped = stripRustComments(code);
            expect(stripped).not.toContain("this is a line comment");
            expect(stripped).toContain("fn foo");
        });
    });

    describe("String Detection in Rust Context", () => {
        it("should accurately determine if an index points inside a string literal", () => {
            const code = 'const A: &str = "symbol_name";\nconst B: u32 = 42;';
            const indexInside = code.indexOf("symbol_name");
            const indexOutside = code.indexOf("B");

            expect(isIndexInRustString(code, indexInside)).toBe(true);
            expect(isIndexInRustString(code, indexOutside)).toBe(false);
        });
    });

    describe("Correct Rust Use Path Generation", () => {
        it("should map Lean path structure to Rust module names", () => {
            const leanFile = "src/Init/Data/Array/Basic.lean";
            const path = getCorrectRustUsePath(leanFile, "lean_array_to_list_impl");
            expect(path).toBe("crate::Init::Data::Array::Basic::lean_array_to_list_impl");
        });
    });

    describe("Lean FFI Extraction Cases", () => {
        it("should parse [extern] declarations using standard attribute syntax", () => {
            const code = 'attribute [extern "lean_mk_thunk"] Thunk.mk';
            const occurrences = Array.from(scanLeanFile(code));
            expect(occurrences).toHaveLength(1);
            expect(occurrences[0]).toEqual({
                type: "extern",
                symbolName: "lean_mk_thunk",
                leanName: "Thunk.mk",
                lineNum: 1
            });
        });

        it("should parse [extern] declarations in mixed attribute lists", () => {
            const code = 'attribute [extern "lean_task_pure", inline] Task.pure';
            const occurrences = Array.from(scanLeanFile(code));
            expect(occurrences).toHaveLength(1);
            expect(occurrences[0]).toEqual({
                type: "extern",
                symbolName: "lean_task_pure",
                leanName: "Task.pure",
                lineNum: 1
            });
        });

        it("should parse decorator @[extern] declarations", () => {
            const code = '@[extern "lean_task_pure"] def Task.pure (a : α) : Task α';
            const occurrences = Array.from(scanLeanFile(code));
            expect(occurrences).toHaveLength(1);
            expect(occurrences[0]).toEqual({
                type: "extern",
                symbolName: "lean_task_pure",
                leanName: "Task.pure",
                lineNum: 1
            });
        });

        it("should parse attribute [export] declarations", () => {
            const code = 'attribute [export lean_enable_initializer_execution] enableInitializerExecution';
            const occurrences = Array.from(scanLeanFile(code));
            expect(occurrences).toHaveLength(1);
            expect(occurrences[0]).toEqual({
                type: "export",
                symbolName: "lean_enable_initializer_execution",
                leanName: "enableInitializerExecution",
                lineNum: 1
            });
        });

        it("should parse @[export] declarations", () => {
            const code = '@[export lean_array_to_list_impl] def Array.toList';
            const occurrences = Array.from(scanLeanFile(code));
            expect(occurrences).toHaveLength(1);
            expect(occurrences[0]).toEqual({
                type: "export",
                symbolName: "lean_array_to_list_impl",
                leanName: "Array.toList",
                lineNum: 1
            });
        });
    });

    describe("Rust Should Import from Lean ([export]) - Verification States", () => {
        const correctUsePath = "crate::Init::Data::Array::Basic::lean_array_to_list_impl";

        it("State 1 (✅): Function is found in rust code and import is correct (absolute path)", () => {
            const line = "use crate::Init::Data::Array::Basic::lean_array_to_list_impl;";
            const classification = classifyRustLine(line, "lean_array_to_list_impl", correctUsePath, false, false, false);
            expect(classification.status).toBe("correct");
        });

        it("State 1b (✅): Function is found in rust code and import is correct (root re-export)", () => {
            const line = "use crate::lean_array_to_list_impl;";
            const classification = classifyRustLine(line, "lean_array_to_list_impl", correctUsePath, false, false, false);
            expect(classification.status).toBe("correct");
        });

        it("State 1c (✅): Function is found in rust code and import is correct (cross-crate runtime resolution)", () => {
            const line = "use lean_runtime::lean_array_to_list_impl;";
            const classification = classifyRustLine(line, "lean_array_to_list_impl", correctUsePath, false, false, false);
            expect(classification.status).toBe("correct");
        });

        it("State 2 (⚠️): Function is found in rust code, but import is wrong", () => {
            const line = "use wrong::module::path::lean_array_to_list_impl;";
            const classification = classifyRustLine(line, "lean_array_to_list_impl", correctUsePath, false, false, false);
            expect(classification.status).toBe("wrong_import");
            expect(classification.currentImport).toBe(line);
        });

        it("State 3 (🛠️): Function is found in rust code, but is defined directly in Rust", () => {
            const line = "pub fn lean_array_to_list_impl() { return 0; }";
            const classification = classifyRustLine(line, "lean_array_to_list_impl", correctUsePath, true, true, false);
            expect(classification.status).toBe("defined_in_rust");
        });

        it("State 4 (🔌): Function is found inside of standard extern C signature block", () => {
            const line = "fn lean_array_to_list_impl();";
            const classification = classifyRustLine(line, "lean_array_to_list_impl", correctUsePath, false, true, false);
            expect(classification.status).toBe("extern_c");
        });

        it("State 4b (🔌): Function is resolved via link_name attribute", () => {
            const line = '#[link_name = "lean_array_to_list_impl"]';
            const classification = classifyRustLine(line, "lean_array_to_list_impl", correctUsePath, false, false, false);
            expect(classification.status).toBe("extern_c");
        });

        it("State 5 (🔍): Function is resolved via dynamic string lookup", () => {
            const line = 'c_char_ptr(b"lean_array_to_list_impl\\0")';
            const classification = classifyRustLine(line, "lean_array_to_list_impl", correctUsePath, false, false, true);
            expect(classification.status).toBe("dynamic_lookup");
        });
    });
});



/**
 * Replicates the Rust indexing routine used in the main CLI entry script
 */
function buildMockRustIndex(content: string, targetSymbols: Set<string>): Map<string, RustSearchResult[]> {
    const mockIndex = new Map<string, RustSearchResult[]>();
    for (const item of findSymbolsInRust("mock_rust_file.rs", content, targetSymbols)) {
        if (!mockIndex.has(item.symbol)) {
            mockIndex.set(item.symbol, []);
        }
        mockIndex.get(item.symbol)!.push(item.result);
    }
    return mockIndex;
}

describe("FFI Checker Parser & Classification Engine", () => {

    describe("Comment Stripping Logic", () => {
        it("should strip single and block comments from Lean code", () => {
            const code = `-- this is a line comment\n@[extern] def foo : Nat\n/- block comment -/`;
            const stripped = stripLeanComments(code);
            expect(stripped).not.toContain("this is a line comment");
            expect(stripped).not.toContain("block comment");
            expect(stripped).toContain("def foo");
        });

        it("should strip single and block comments from Rust code", () => {
            const code = `// this is a line comment\nfn foo() {}\n/* block comment */`;
            const stripped = stripRustComments(code);
            expect(stripped).not.toContain("this is a line comment");
            expect(stripped).not.toContain("block comment");
            expect(stripped).toContain("fn foo");
        });
    });

    describe("Correct Rust Use Path Generation", () => {
        it("should map a file path and matching symbol name to a Rust module path", () => {
            const leanFile = "src/Init/Data/Array/Basic.lean";
            const path = getCorrectRustUsePath(leanFile, "lean_array_to_list_impl");
            expect(path).toBe("crate::Init::Data::Array::Basic::lean_array_to_list_impl");
        });
    });

    describe("E2E Lean to Rust (extern) Pipeline - 3 Verification States", () => {
        const leanSource = `
      -- Case 1: Standard attribute extern with matching Rust implementation (has body)
      attribute [extern "lean_mk_thunk"] Thunk.mk

      -- Case 2: Decorator extern with empty Rust declaration inside an extern block
      @[extern "lean_task_spawn"] def Task.spawn (fn : Unit -> Unit) : Task Unit

      -- Case 3: Completely missing from Rust code
      @[extern "lean_strict_or"] def strictOr (b1 b2 : Bool) : Bool
    `;

        const rustSource = `
      // Implemented function (has body)
      pub fn lean_mk_thunk(a: usize) -> usize {
          a + 1
      }

      extern "C" {
          // Declared signature, empty body
          pub fn lean_task_spawn(fn_ptr: usize);
      }
    `;

        it("should identify, match, and classify all 3 extern cases", () => {
            const occurrences = Array.from(scanLeanFile(leanSource));
            const targetSymbols = new Set(occurrences.map(o => o.symbolName));
            const rustIndex = buildMockRustIndex(rustSource, targetSymbols);

            const results = occurrences.map(occ => {
                const matches = rustIndex.get(occ.symbolName) || [];
                const bestMatch = matches[0] || null;

                const isOk = !!(bestMatch && bestMatch.isDefinition && bestMatch.hasBody);
                const isEmpty = !!(bestMatch && bestMatch.isDefinition && !bestMatch.hasBody);

                return {
                    symbolName: occ.symbolName,
                    matchFound: !!bestMatch,
                    isOk,
                    isEmpty,
                };
            });

            // 1. lean_mk_thunk (State 1: ✅)
            const case1 = results.find(r => r.symbolName === "lean_mk_thunk");
            expect(case1).toBeDefined();
            expect(case1?.matchFound).toBe(true);
            expect(case1?.isOk).toBe(true);
            expect(case1?.isEmpty).toBe(false);

            // 2. lean_task_spawn (State 2: ⚠️)
            const case2 = results.find(r => r.symbolName === "lean_task_spawn");
            expect(case2).toBeDefined();
            expect(case2?.matchFound).toBe(true);
            expect(case2?.isOk).toBe(false);
            expect(case2?.isEmpty).toBe(true);

            // 3. lean_strict_or (State 3: ❌)
            const case3 = results.find(r => r.symbolName === "lean_strict_or");
            expect(case3).toBeDefined();
            expect(case3?.matchFound).toBe(false);
        });
    });

    describe("E2E Rust to Lean (export) Pipeline - Scenarios", () => {
        const leanFilePath = "src/Init/Data/Array/Basic.lean";
        const leanSource = `
      @[export lean_array_to_list_impl] def Array.toList (a : Array α) : List α
      @[export lean_array_mk] def Array.mk (l : List α) : Array α
      @[export lean_array_size] def Array.size (a : Array α) : Nat
      @[export lean_array_get] def Array.get (a : Array α) (i : Nat) : α
      @[export lean_array_set] def Array.set (a : Array α) (i : Nat) (v : α) : Array α
    `;

        const rustSource = `
      // Case 1: Correct import path
      use crate::Init::Data::Array::Basic::lean_array_to_list_impl;

      // Case 2: Incorrect import path
      use wrong::module::path::lean_array_mk;

      // Case 3: Defined directly in Rust with a body (conflicting implementation)
      pub fn lean_array_size(arr: usize) -> usize {
          0
      }

      extern "C" {
          // Case 4: Declared inside extern "C" block (no body)
          pub fn lean_array_get(arr: usize) -> usize;
      }

      // Case 5: lean_array_set is entirely missing from Rust code
    `;

        it("should classify export scenarios based on the generated indexes", () => {
            const occurrences = Array.from(scanLeanFile(leanSource));
            const targetSymbols = new Set(occurrences.map(o => o.symbolName));
            const rustIndex = buildMockRustIndex(rustSource, targetSymbols);

            const results = occurrences.map(occ => {
                const matches = rustIndex.get(occ.symbolName) || [];
                const bestMatch = matches[0] || null;
                const correctUsePath = getCorrectRustUsePath(leanFilePath, occ.symbolName);

                if (!bestMatch) {
                    return { symbolName: occ.symbolName, status: "missing", correctUsePath };
                }

                const classification = classifyRustLine(
                    bestMatch.snippet,
                    occ.symbolName,
                    correctUsePath,
                    bestMatch.hasBody,
                    bestMatch.isDefinition,
                    bestMatch.isStringLiteral
                );

                return {
                    symbolName: occ.symbolName,
                    status: classification.status,
                    correctUsePath,
                    snippet: classification.snippet,
                };
            });

            // 1. lean_array_to_list_impl (State 1: ✅)
            const case1 = results.find(r => r.symbolName === "lean_array_to_list_impl");
            expect(case1).toBeDefined();
            expect(case1?.status).toBe("correct");

            // 2. lean_array_mk (State 2: ⚠️)
            const case2 = results.find(r => r.symbolName === "lean_array_mk");
            expect(case2).toBeDefined();
            expect(case2?.status).toBe("wrong_import");

            // 3. lean_array_size (State 3: 🛠️)
            const case3 = results.find(r => r.symbolName === "lean_array_size");
            expect(case3).toBeDefined();
            expect(case3?.status).toBe("defined_in_rust");

            // 4. lean_array_get (State 4: 🔌)
            const case4 = results.find(r => r.symbolName === "lean_array_get");
            expect(case4).toBeDefined();
            expect(case4?.status).toBe("extern_c");

            // 5. lean_array_set (State 5: ❌)
            const case5 = results.find(r => r.symbolName === "lean_array_set");
            expect(case5).toBeDefined();
            expect(case5?.status).toBe("missing");
        });
    });
});
