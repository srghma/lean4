# Cargo-Only Lean Runtime and Generated Code

## Summary

Move Lean to a Rust/Cargo distribution model: no source .h/C++ compatibility surface, no .a/.o/.dynlib Lean module pipeline, and no direct extern "C" imports in Lean-owned Rust crates. Toolchains (next toolchain will be /home/srghma/.elan/toolchains/leanprover--lean4---v5.0.0) ship Rust crates/rlibs, and users must have Cargo installed.

## Key Changes

- Repair the current compile break first by reverting invalid use crate::lean_... imports where the target symbol is generated Lean code, but only as a short-lived bootstrap step.
  - Do not keep this as the final architecture.
  - Restore buildability, remove duplicate/broken edits, and compare behavior with origin-master-src when runtime semantics are unclear.

- Split crates so Rust dependencies are acyclic:
  - lean_runtime_core: pure Rust runtime/kernel primitives, object model, alloc/refcount/task logic.
  - lean_runtime_sysdeps: wrappers around Cargo system crates such as libuv-sys and gmp-mpfr-sys; Lean-owned crates do not declare raw foreign imports.
  - lean_generated_abi: shared object/layout/helper API used by EmitRust output.
  - Generated crates: lean_init, lean_std, lean_lean, lean_lake.
  - lean_shell / executables depend on generated crates plus runtime core.

- Replace remaining C dependency imports:
  - GMP direct extern "C" declarations become calls through gmp-mpfr-sys.
  - libuv direct declarations become calls through libuv-sys.
  - Platform C APIs are migrated later to Rust crates or std APIs; while migrating, isolate them in lean_runtime_sysdeps.
  - No Lean-owned module should manually declare third-party symbols.

- Change EmitRust output:
  - Emit package modules into Cargo crate source trees instead of standalone Rust files linked like C outputs.
  - Cross-module calls become normal Rust imports between generated crates.
  - Generated code imports runtime helpers through lean_runtime_core / lean_generated_abi, not extern "C".
  - Initializers/finalizers become normal Rust functions and registry calls, not exported C symbols.

- Replace Lake/leanc build flow:
  - Lake invokes Cargo for Lean packages targeting Rust.
  - Toolchain install includes crate sources or prebuilt rlibs under the elan toolchain directory.
  - leanc Rust mode becomes a Cargo/rustc wrapper only for compatibility; it should not produce C objects or static archives.
  - Remove generated lean.h from the final target; tests that include it must be rewritten to Rust FFI/package examples or removed.

## Test Plan

- Bootstrap repair:
  - cargo check --manifest-path src/rust/Cargo.toml --package lean_runtime
  - make -C build/release lean_runtime_rust lean -j"$(nproc)"
  - Run 3-5 focused tests covering shell startup, kernel/type-checker, IO/task/libuv, and generated Rust execution.

- Migration validation:
  - Build lean_init, lean_std, lean_lean, lean_lake with Cargo.
  - Assert no Lean-owned .rs file contains direct third-party extern "C" import blocks.
  - Assert fd "\\.h$" ./src is empty and Lean stdlib build emits no .o, .a, or shared module artifacts in the Rust path.
  - Run focused Lake/package tests using Cargo-backed builds.

## Assumptions

- Users installing future Lean toolchains are allowed to require Cargo.
- extern "C" inside upstream crates like libuv-sys and gmp-mpfr-sys is acceptable; Lean-owned code should not declare those imports manually.
- Public C/C++ compatibility is intentionally dropped for this Rust-only backend.
- Any semantic porting ambiguity must be checked against origin-master-src.


-----

# List of all functions that lean imports from rust

```sh
 ~/projects/lean4   rust-rewrite ±✚  ag -s 'attribute \[extern|@\[extern|, extern' ./src/**/*.lean          <<<
src/Init/Core.lean
130:attribute [extern "lean_mk_thunk"] Thunk.mk
137:@[extern "lean_thunk_pure"] protected def Thunk.pure (a : α) : Thunk α :=
147:@[extern "lean_thunk_get_own"] protected def Thunk.get (x : @& Thunk α) : α :=
646:attribute [extern "lean_task_pure"] Task.pure
647:attribute [extern "lean_task_get_own"] Task.get
686:@[noinline, extern "lean_task_spawn"]
701:@[noinline, extern "lean_task_map"]
717:@[noinline, extern "lean_task_bind"]
757:@[extern "lean_strict_or"] def strictOr  (b₁ b₂ : Bool) := b₁ || b₂
763:@[extern "lean_strict_and"] def strictAnd (b₁ b₂ : Bool) := b₁ && b₂

src/Init/Data/Array/Basic.lean
165:@[extern "lean_array_size", simp, expose]
173:@[extern "lean_array_uget", simp, expose]
182:@[extern "lean_array_uget_borrowed"]
192:@[extern "lean_array_uset", expose]
205:@[extern "lean_array_pop", expose]
224:@[extern "lean_mk_array", expose]
238:@[extern "lean_array_fswap", expose]
261:@[extern "lean_array_swap", expose]

src/Init/Data/Array/Set.lean
29:@[extern "lean_array_fset", expose]
54:@[extern "lean_array_set", expose]

src/Init/Data/BitVec/Basic.lean
250:and should be replaced via an `@[extern]` with a native implementation.

src/Init/Data/ByteArray/Basic.lean
23:@[extern "lean_sarray_dec_eq"]
32:@[extern "lean_sarray_dec_eq"]
50:@[extern "lean_sarray_size", simp]
61:@[extern "lean_byte_array_uget"]
68:@[extern "lean_byte_array_get"]
78:@[extern "lean_byte_array_fget"]
95:@[extern "lean_byte_array_set"]
107:@[extern "lean_byte_array_fset"]
111:@[extern "lean_byte_array_uset", inherit_doc ByteArray.set]
118:@[extern "lean_byte_array_hash"]
135:@[extern "lean_byte_array_copy_slice"]

src/Init/Data/Float32.lean
51:@[extern "lean_float32_add"] opaque Float32.add : Float32 → Float32 → Float32
57:@[extern "lean_float32_sub"] opaque Float32.sub : Float32 → Float32 → Float32
63:@[extern "lean_float32_mul"] opaque Float32.mul : Float32 → Float32 → Float32
72:@[extern "lean_float32_div"] opaque Float32.div : Float32 → Float32 → Float32
79:@[extern "lean_float32_negate"] opaque Float32.neg : Float32 → Float32
104:@[extern "lean_float32_of_bits"] opaque Float32.ofBits : UInt32 → Float32
119:@[extern "lean_float32_to_bits"] opaque Float32.toBits : Float32 → UInt32
138:@[extern "lean_float32_beq"] opaque Float32.beq (a b : Float32) : Bool
147:@[extern "lean_float32_decLt", instance] opaque Float32.decLt (a b : Float32) : Decidable (a < b) :=
156:@[extern "lean_float32_decLe", instance] opaque Float32.decLe (a b : Float32) : Decidable (a ≤ b) :=
165:@[extern "lean_float32_to_string"] opaque Float32.toString : Float32 → String
175:@[extern "lean_float32_to_uint8"] opaque Float32.toUInt8 : Float32 → UInt8
185:@[extern "lean_float32_to_uint16"] opaque Float32.toUInt16 : Float32 → UInt16
195:@[extern "lean_float32_to_uint32"] opaque Float32.toUInt32 : Float32 → UInt32
205:@[extern "lean_float32_to_uint64"] opaque Float32.toUInt64 : Float32 → UInt64
215:@[extern "lean_float32_to_usize"] opaque Float32.toUSize : Float32 → USize
224:@[extern "lean_float32_isnan"] opaque Float32.isNaN : Float32 → Bool
231:@[extern "lean_float32_isfinite"] opaque Float32.isFinite : Float32 → Bool
238:@[extern "lean_float32_isinf"] opaque Float32.isInf : Float32 → Bool
246:@[extern "lean_float32_frexp"] opaque Float32.frExp : Float32 → Float32 × Int
252:@[extern "lean_uint8_to_float32"] opaque UInt8.toFloat32 (n : UInt8) : Float32
254:@[extern "lean_uint16_to_float32"] opaque UInt16.toFloat32 (n : UInt16) : Float32
265:@[extern "lean_uint32_to_float32"] opaque UInt32.toFloat32 (n : UInt32) : Float32
276:@[extern "lean_uint64_to_float32"] opaque UInt64.toFloat32 (n : UInt64) : Float32
286:@[extern "lean_usize_to_float32"] opaque USize.toFloat32 (n : USize) : Float32
305:@[extern "sinf"] opaque Float32.sin : Float32 → Float32
312:@[extern "cosf"] opaque Float32.cos : Float32 → Float32
319:@[extern "tanf"] opaque Float32.tan : Float32 → Float32
326:@[extern "asinf"] opaque Float32.asin : Float32 → Float32
333:@[extern "acosf"] opaque Float32.acos : Float32 → Float32
340:@[extern "atanf"] opaque Float32.atan : Float32 → Float32
348:@[extern "atan2f"] opaque Float32.atan2 : Float32 → Float32 → Float32
355:@[extern "sinhf"] opaque Float32.sinh : Float32 → Float32
362:@[extern "coshf"] opaque Float32.cosh : Float32 → Float32
369:@[extern "tanhf"] opaque Float32.tanh : Float32 → Float32
376:@[extern "asinhf"] opaque Float32.asinh : Float32 → Float32
383:@[extern "acoshf"] opaque Float32.acosh : Float32 → Float32
390:@[extern "atanhf"] opaque Float32.atanh : Float32 → Float32
397:@[extern "expf"] opaque Float32.exp : Float32 → Float32
404:@[extern "exp2f"] opaque Float32.exp2 : Float32 → Float32
411:@[extern "logf"] opaque Float32.log : Float32 → Float32
418:@[extern "log2f"] opaque Float32.log2 : Float32 → Float32
425:@[extern "log10f"] opaque Float32.log10 : Float32 → Float32
432:@[extern "powf"] opaque Float32.pow : Float32 → Float32 → Float32
439:@[extern "sqrtf"] opaque Float32.sqrt : Float32 → Float32
446:@[extern "cbrtf"] opaque Float32.cbrt : Float32 → Float32
458:@[extern "ceilf"] opaque Float32.ceil : Float32 → Float32
470:@[extern "floorf"] opaque Float32.floor : Float32 → Float32
477:@[extern "roundf"] opaque Float32.round : Float32 → Float32
484:@[extern "fabsf"] opaque Float32.abs : Float32 → Float32
497:@[extern "lean_float32_scaleb"]
505:@[extern "lean_float32_to_float"] opaque Float32.toFloat : Float32 → Float
512:@[extern "lean_float_to_float32"] opaque Float.toFloat32 : Float → Float32

src/Init/Data/FloatArray/Basic.lean
20:attribute [extern "lean_float_array_mk"] FloatArray.mk
21:attribute [extern "lean_float_array_data"] FloatArray.data
29:@[extern "lean_mk_empty_float_array"]
42:@[extern "lean_float_array_push"]
46:@[extern "lean_float_array_size", tagged_return]
50:@[extern "lean_sarray_size", simp]
54:@[extern "lean_float_array_uget"]
58:@[extern "lean_float_array_fget"]
62:@[extern "lean_float_array_get"]
78:@[extern "lean_float_array_uset"]
82:@[extern "lean_float_array_fset"]
86:@[extern "lean_float_array_set"]

src/Init/Data/Float.lean
58:@[extern "lean_float_add"] opaque Float.add : Float → Float → Float
64:@[extern "lean_float_sub"] opaque Float.sub : Float → Float → Float
70:@[extern "lean_float_mul"] opaque Float.mul : Float → Float → Float
79:@[extern "lean_float_div"] opaque Float.div : Float → Float → Float
86:@[extern "lean_float_negate"] opaque Float.neg : Float → Float
111:@[extern "lean_float_of_bits"] opaque Float.ofBits : UInt64 → Float
123:@[extern "lean_float_to_bits"] opaque Float.toBits : Float → UInt64
142:@[extern "lean_float_beq"] opaque Float.beq (a b : Float) : Bool
151:@[extern "lean_float_decLt"] opaque Float.decLt (a b : Float) : Decidable (a < b) :=
160:@[extern "lean_float_decLe"] opaque Float.decLe (a b : Float) : Decidable (a ≤ b) :=
171:@[extern "lean_float_to_string"] opaque Float.toString : Float → String
182:@[extern "lean_float_to_uint8"] opaque Float.toUInt8 : Float → UInt8
192:@[extern "lean_float_to_uint16"] opaque Float.toUInt16 : Float → UInt16
202:@[extern "lean_float_to_uint32"] opaque Float.toUInt32 : Float → UInt32
212:@[extern "lean_float_to_uint64"] opaque Float.toUInt64 : Float → UInt64
222:@[extern "lean_float_to_usize"] opaque Float.toUSize : Float → USize
231:@[extern "lean_float_isnan"] opaque Float.isNaN : Float → Bool
239:@[extern "lean_float_isfinite"] opaque Float.isFinite : Float → Bool
247:@[extern "lean_float_isinf"] opaque Float.isInf : Float → Bool
256:@[extern "lean_float_frexp"] opaque Float.frExp : Float → Float × Int
262:@[extern "lean_uint8_to_float"] opaque UInt8.toFloat (n : UInt8) : Float
264:@[extern "lean_uint16_to_float"] opaque UInt16.toFloat (n : UInt16) : Float
266:@[extern "lean_uint32_to_float"] opaque UInt32.toFloat (n : UInt32) : Float
277:@[extern "lean_uint64_to_float"] opaque UInt64.toFloat (n : UInt64) : Float
288:@[extern "lean_usize_to_float"] opaque USize.toFloat (n : USize) : Float
307:@[extern "sin"] opaque Float.sin : Float → Float
314:@[extern "cos"] opaque Float.cos : Float → Float
321:@[extern "tan"] opaque Float.tan : Float → Float
328:@[extern "asin"] opaque Float.asin : Float → Float
335:@[extern "acos"] opaque Float.acos : Float → Float
342:@[extern "atan"] opaque Float.atan : Float → Float
350:@[extern "atan2"] opaque Float.atan2 (y x : Float) : Float
357:@[extern "sinh"] opaque Float.sinh : Float → Float
364:@[extern "cosh"] opaque Float.cosh : Float → Float
371:@[extern "tanh"] opaque Float.tanh : Float → Float
378:@[extern "asinh"] opaque Float.asinh : Float → Float
385:@[extern "acosh"] opaque Float.acosh : Float → Float
392:@[extern "atanh"] opaque Float.atanh : Float → Float
399:@[extern "exp"] opaque Float.exp (x : Float) : Float
406:@[extern "exp2"] opaque Float.exp2 (x : Float) : Float
413:@[extern "log"] opaque Float.log (x : Float) : Float
420:@[extern "log2"] opaque Float.log2 : Float → Float
427:@[extern "log10"] opaque Float.log10 : Float → Float
434:@[extern "pow"] opaque Float.pow : Float → Float → Float
441:@[extern "sqrt"] opaque Float.sqrt : Float → Float
448:@[extern "cbrt"] opaque Float.cbrt : Float → Float
460:@[extern "ceil"] opaque Float.ceil : Float → Float
472:@[extern "floor"] opaque Float.floor : Float → Float
479:@[extern "round"] opaque Float.round : Float → Float
486:@[extern "fabs"] opaque Float.abs : Float → Float
499:@[extern "lean_float_scaleb"]

src/Init/Data/Int/Basic.lean
60:attribute [extern "lean_nat_to_int"] Int.ofNat
61:attribute [extern "lean_int_neg_succ_of_nat"] Int.negSucc
118:@[extern "lean_int_neg"]
160:@[extern "lean_int_add"]
183:@[extern "lean_int_mul"]
206:@[extern "lean_int_sub"]
253:@[extern "lean_int_dec_eq"]
278:@[extern "lean_int_dec_nonneg"]
297:@[extern "lean_int_dec_le"]
310:@[extern "lean_int_dec_lt"]
326:@[extern "lean_nat_abs"]

src/Init/Data/Int/DivMod/Basic.lean
72:@[extern "lean_int_ediv"]
102:@[extern "lean_int_emod"]
145:@[extern "lean_int_div_exact"]
177:@[extern "lean_int_div"]
210:@[extern "lean_int_mod"]

src/Init/Data/Nat/Bitwise/Basic.lean
49:@[extern "lean_nat_land"]
57:@[extern "lean_nat_lor"]
65:@[extern "lean_nat_lxor"]
78:@[extern "lean_nat_shiftl", expose]
94:@[extern "lean_nat_shiftr", expose]

src/Init/Data/Nat/Div/Basic.lean
109:@[extern "lean_nat_div_exact"]

src/Init/Data/Nat/Gcd.lean
34:@[extern "lean_nat_gcd"]

src/Init/Data/Nat/Log2.lean
41:@[expose, extern "lean_nat_log2"]

src/Init/Data/Ord/String.lean
31:@[extern "lean_string_compare"]

src/Init/Data/Repr.lean
230:@[extern "lean_string_of_usize"]

src/Init/Data/SInt/Basic.lean
112:@[extern "lean_int8_of_int"]
125:@[extern "lean_int8_of_nat"]
154:@[extern "lean_int8_to_int", tagged_return]
170:@[extern "lean_int8_neg"]
213:@[extern "lean_int8_add"]
221:@[extern "lean_int8_sub"]
229:@[extern "lean_int8_mul"]
246:@[extern "lean_int8_div"]
278:@[extern "lean_int8_mod"]
288:@[extern "lean_int8_land"]
298:@[extern "lean_int8_lor"]
308:@[extern "lean_int8_xor"]
317:@[extern "lean_int8_shift_left"]
326:@[extern "lean_int8_shift_right"]
337:@[extern "lean_int8_complement"]
347:@[extern "lean_int8_abs"]
361:@[extern "lean_int8_dec_eq"]
403:@[extern "lean_bool_to_int8"]
417:@[extern "lean_int8_dec_lt", implicit_reducible]
433:@[extern "lean_int8_dec_le", implicit_reducible]
468:@[extern "lean_int16_of_int"]
481:@[extern "lean_int16_of_nat"]
511:@[extern "lean_int16_to_int", tagged_return]
528:@[extern "lean_int16_to_int8"]
535:@[extern "lean_int8_to_int16"]
542:@[extern "lean_int16_neg"]
586:@[extern "lean_int16_add"]
594:@[extern "lean_int16_sub"]
602:@[extern "lean_int16_mul"]
619:@[extern "lean_int16_div"]
651:@[extern "lean_int16_mod"]
661:@[extern "lean_int16_land"]
671:@[extern "lean_int16_lor"]
681:@[extern "lean_int16_xor"]
690:@[extern "lean_int16_shift_left"]
699:@[extern "lean_int16_shift_right"]
710:@[extern "lean_int16_complement"]
720:@[extern "lean_int16_abs"]
734:@[extern "lean_int16_dec_eq"]
776:@[extern "lean_bool_to_int16"]
790:@[extern "lean_int16_dec_lt", implicit_reducible]
806:@[extern "lean_int16_dec_le", implicit_reducible]
842:@[extern "lean_int32_of_int"]
855:@[extern "lean_int32_of_nat"]
885:@[extern "lean_int32_to_int"]
902:@[extern "lean_int32_to_int8"]
910:@[extern "lean_int32_to_int16"]
917:@[extern "lean_int8_to_int32"]
924:@[extern "lean_int16_to_int32"]
931:@[extern "lean_int32_neg"]
975:@[extern "lean_int32_add"]
983:@[extern "lean_int32_sub"]
991:@[extern "lean_int32_mul"]
1008:@[extern "lean_int32_div"]
1040:@[extern "lean_int32_mod"]
1050:@[extern "lean_int32_land"]
1060:@[extern "lean_int32_lor"]
1070:@[extern "lean_int32_xor"]
1079:@[extern "lean_int32_shift_left"]
1088:@[extern "lean_int32_shift_right"]
1099:@[extern "lean_int32_complement"]
1109:@[extern "lean_int32_abs"]
1123:@[extern "lean_int32_dec_eq"]
1165:@[extern "lean_bool_to_int32"]
1179:@[extern "lean_int32_dec_lt", implicit_reducible]
1195:@[extern "lean_int32_dec_le", implicit_reducible]
1231:@[extern "lean_int64_of_int"]
1246:@[extern "lean_int64_of_nat"]
1279:@[extern "lean_int64_to_int_sint"]
1296:@[extern "lean_int64_to_int8"]
1304:@[extern "lean_int64_to_int16"]
1312:@[extern "lean_int64_to_int32"]
1319:@[extern "lean_int8_to_int64"]
1326:@[extern "lean_int16_to_int64"]
1333:@[extern "lean_int32_to_int64"]
1340:@[extern "lean_int64_neg"]
1384:@[extern "lean_int64_add"]
1392:@[extern "lean_int64_sub"]
1400:@[extern "lean_int64_mul"]
1417:@[extern "lean_int64_div"]
1449:@[extern "lean_int64_mod"]
1459:@[extern "lean_int64_land"]
1469:@[extern "lean_int64_lor"]
1479:@[extern "lean_int64_xor"]
1488:@[extern "lean_int64_shift_left"]
1497:@[extern "lean_int64_shift_right"]
1508:@[extern "lean_int64_complement"]
1518:@[extern "lean_int64_abs"]
1532:@[extern "lean_int64_dec_eq"]
1574:@[extern "lean_bool_to_int64"]
1588:@[extern "lean_int64_dec_lt", implicit_reducible]
1603:@[extern "lean_int64_dec_le", implicit_reducible]
1632:@[extern "lean_isize_of_int"]
1640:@[extern "lean_isize_of_nat"]
1650:@[extern "lean_isize_to_int"]
1666:@[extern "lean_isize_to_int8"]
1673:@[extern "lean_isize_to_int16"]
1684:@[extern "lean_isize_to_int32"]
1692:@[extern "lean_isize_to_int64"]
1700:@[extern "lean_int8_to_isize"]
1708:@[extern "lean_int16_to_isize"]
1716:@[extern "lean_int32_to_isize"]
1724:@[extern "lean_int64_to_isize"]
1731:@[extern "lean_isize_neg"]
1776:@[extern "lean_isize_add"]
1784:@[extern "lean_isize_sub"]
1792:@[extern "lean_isize_mul"]
1809:@[extern "lean_isize_div"]
1841:@[extern "lean_isize_mod"]
1851:@[extern "lean_isize_land"]
1861:@[extern "lean_isize_lor"]
1871:@[extern "lean_isize_xor"]
1880:@[extern "lean_isize_shift_left"]
1890:@[extern "lean_isize_shift_right"]
1901:@[extern "lean_isize_complement"]
1912:@[extern "lean_isize_abs"]
1926:@[extern "lean_isize_dec_eq"]
1968:@[extern "lean_bool_to_isize"]
1982:@[extern "lean_isize_dec_lt", implicit_reducible]
1998:@[extern "lean_isize_dec_le", implicit_reducible]

src/Init/Data/SInt/Float32.lean
25:@[extern "lean_float32_to_int8"] opaque Float32.toInt8 : Float32 → Int8
36:@[extern "lean_float32_to_int16"] opaque Float32.toInt16 : Float32 → Int16
47:@[extern "lean_float32_to_int32"] opaque Float32.toInt32 : Float32 → Int32
58:@[extern "lean_float32_to_int64"] opaque Float32.toInt64 : Float32 → Int64
69:@[extern "lean_float32_to_isize"] opaque Float32.toISize : Float32 → ISize
76:@[extern "lean_int8_to_float32"] opaque Int8.toFloat32 (n : Int8) : Float32
82:@[extern "lean_int16_to_float32"] opaque Int16.toFloat32 (n : Int16) : Float32
92:@[extern "lean_int32_to_float32"] opaque Int32.toFloat32 (n : Int32) : Float32
102:@[extern "lean_int64_to_float32"] opaque Int64.toFloat32 (n : Int64) : Float32
112:@[extern "lean_isize_to_float32"] opaque ISize.toFloat32 (n : ISize) : Float32

src/Init/Data/SInt/Float.lean
25:@[extern "lean_float_to_int8"] opaque Float.toInt8 : Float → Int8
36:@[extern "lean_float_to_int16"] opaque Float.toInt16 : Float → Int16
47:@[extern "lean_float_to_int32"] opaque Float.toInt32 : Float → Int32
58:@[extern "lean_float_to_int64"] opaque Float.toInt64 : Float → Int64
69:@[extern "lean_float_to_isize"] opaque Float.toISize : Float → ISize
76:@[extern "lean_int8_to_float"] opaque Int8.toFloat (n : Int8) : Float
82:@[extern "lean_int16_to_float"] opaque Int16.toFloat (n : Int16) : Float
88:@[extern "lean_int32_to_float"] opaque Int32.toFloat (n : Int32) : Float
99:@[extern "lean_int64_to_float"] opaque Int64.toFloat (n : Int64) : Float
109:@[extern "lean_isize_to_float"] opaque ISize.toFloat (n : ISize) : Float

src/Init/Data/String/Basic.lean
88:@[expose, extern "lean_string_validate_utf8"]
240:@[extern "lean_string_data", expose]
255:@[extern "lean_string_data", expose, deprecated String.toList (since := "2025-10-30")]
424:@[extern "lean_string_dec_lt"]
666:@[extern "lean_string_is_valid_pos", expose]
786:@[extern "lean_string_utf8_extract"]
1152:@[extern "lean_string_utf8_get_fast", expose]
1665:@[expose, extern "lean_string_utf8_next_fast", tagged_return]
1892:@[extern "lean_string_utf8_get", expose]
1896:@[extern "lean_string_utf8_get", expose, deprecated Pos.Raw.get (since := "2025-10-14")]
1924:@[extern "lean_string_utf8_get_opt", expose]
1928:@[extern "lean_string_utf8_get_opt", expose, deprecated Pos.Raw.get? (since := "2025-10-14")]
1946:@[extern "lean_string_utf8_get_bang", expose]
1951:@[extern "lean_string_utf8_get_bang", expose, deprecated Pos.Raw.get! (since := "2025-10-14")]
2813:@[extern "lean_string_utf8_next", expose]
2818:@[extern "lean_string_utf8_next", expose, deprecated Pos.Raw.next (since := "2025-10-14")]
2850:@[extern "lean_string_utf8_prev", expose]
2854:@[extern "lean_string_utf8_prev", expose, deprecated Pos.Raw.prev (since := "2025-10-14")]
2871:@[extern "lean_string_utf8_at_end", expose]
2875:@[extern "lean_string_utf8_at_end", expose, deprecated Pos.Raw.atEnd (since := "2025-10-14")]
2902:@[extern "lean_string_utf8_get_fast", expose]
2907:@[extern "lean_string_utf8_get_fast", expose, deprecated Pos.Raw.get' (since := "2025-10-14")]
2932:@[extern "lean_string_utf8_next_fast", expose, tagged_return]
2937:@[extern "lean_string_utf8_next_fast", expose, deprecated Pos.Raw.next' (since := "2025-10-14")]
3012:@[extern "lean_string_utf8_extract", expose]

src/Init/Data/String/Bootstrap.lean
32:@[extern "lean_string_push", expose]
59:@[extern "lean_string_posof"]
63:@[extern "lean_string_offsetofpos"]
66:@[extern "lean_string_utf8_extract"]
69:@[extern "lean_string_length"]
73:@[extern "lean_string_pushn"]
76:@[extern "lean_string_append"]
79:@[extern "lean_string_utf8_next"]
83:@[extern "lean_string_isempty"]
87:@[extern "lean_string_foldl"]
91:@[extern "lean_string_isprefixof"]
95:@[extern "lean_string_any"]
99:@[extern "lean_string_contains"]
102:@[extern "lean_string_utf8_get"]
106:@[extern "lean_string_capitalize"]
109:@[extern "lean_string_utf8_at_end"]
113:@[extern "lean_string_nextwhile"]
117:@[extern "lean_string_trim"]
121:@[extern "lean_string_intercalate"]
125:@[extern "lean_string_front"]
129:@[extern "lean_string_drop"]
133:@[extern "lean_string_dropright"]
136:@[extern "lean_string_get_byte_fast"]
141:@[extern "lean_string_mk", expose, deprecated String.ofList (since := "2025-10-30")]
160:@[extern "lean_substring_tostring"]
164:@[extern "lean_substring_drop"]
168:@[extern "lean_substring_front"]
172:@[extern "lean_substring_takewhile"]
176:@[extern "lean_substring_extract"]
180:@[extern "lean_substring_all"]
184:@[extern "lean_substring_beq"]
188:@[extern "lean_substring_isempty"]
192:@[extern "lean_substring_get"]
196:@[extern "lean_substring_prev"]
204:@[extern "lean_string_pos_sub"]
208:@[extern "lean_string_pos_min"]

src/Init/Data/String/Defs.lean
75:@[extern "lean_string_to_utf8"]
93:@[extern "lean_string_append", expose]

src/Init/Data/String/Length.lean
24:@[extern "lean_string_length", expose, tagged_return]

src/Init/Data/String/Modify.lean
34:@[extern "lean_string_utf8_set", expose]
160:@[extern "lean_string_utf8_set", expose]
164:@[extern "lean_string_utf8_set", expose, deprecated Pos.Raw.set (since := "2025-10-14")]

src/Init/Data/String/Pattern/Basic.lean
299:@[extern "lean_string_memcmp"]

src/Init/Data/String/PosRaw.lean
107:@[extern "lean_string_get_byte_fast", expose]
111:@[deprecated getUTF8Byte (since := "2025-10-01"), extern "lean_string_get_byte_fast"]

src/Init/Data/String/Slice.lean
86:@[extern "lean_slice_hash"]
96:@[extern "lean_slice_dec_lt"]

src/Init/Data/UInt/BasicAux.lean
66:@[extern "lean_uint8_to_nat", tagged_return]
85:@[extern "lean_uint16_of_nat"]
121:@[extern "lean_uint16_to_nat", tagged_return]
128:@[extern "lean_uint16_to_uint8"]
135:@[extern "lean_uint8_to_uint16"]
153:@[extern "lean_uint32_of_nat"]
188:@[extern "lean_uint32_to_uint8"]
195:@[extern "lean_uint32_to_uint16"]
202:@[extern "lean_uint8_to_uint32"]
209:@[extern "lean_uint16_to_uint32"]
231:@[extern "lean_uint32_add"]
240:@[extern "lean_uint32_sub"]
260:@[extern "lean_uint64_of_nat"]
294:@[extern "lean_uint64_to_nat"]
301:@[extern "lean_uint64_to_uint8"]
308:@[extern "lean_uint64_to_uint16"]
315:@[extern "lean_uint64_to_uint32"]
322:@[extern "lean_uint8_to_uint64"]
329:@[extern "lean_uint16_to_uint64"]
336:@[extern "lean_uint32_to_uint64"]
350:@[extern "lean_usize_of_nat"]
374:@[extern "lean_usize_to_nat"]
382:@[extern "lean_usize_add"]
390:@[extern "lean_usize_sub"]
422:@[extern "lean_usize_dec_lt", implicit_reducible]
438:@[extern "lean_usize_dec_le", implicit_reducible]

src/Init/Data/UInt/Basic.lean
32:@[extern "lean_uint8_add"]
40:@[extern "lean_uint8_sub"]
48:@[extern "lean_uint8_mul"]
58:@[extern "lean_uint8_div"]
84:@[extern "lean_uint8_mod"]
98:@[extern "lean_uint8_land"]
108:@[extern "lean_uint8_lor"]
118:@[extern "lean_uint8_xor"]
125:@[extern "lean_uint8_shift_left"]
132:@[extern "lean_uint8_shift_right"]
154:@[extern "lean_uint8_complement"]
163:@[extern "lean_uint8_neg"]
177:@[extern "lean_bool_to_uint8"]
203:@[extern "lean_uint16_add"]
211:@[extern "lean_uint16_sub"]
219:@[extern "lean_uint16_mul"]
229:@[extern "lean_uint16_div"]
255:@[extern "lean_uint16_mod"]
269:@[extern "lean_uint16_land"]
279:@[extern "lean_uint16_lor"]
289:@[extern "lean_uint16_xor"]
296:@[extern "lean_uint16_shift_left"]
303:@[extern "lean_uint16_shift_right"]
337:@[extern "lean_uint16_complement"]
346:@[extern "lean_uint16_neg"]
360:@[extern "lean_bool_to_uint16"]
375:@[extern "lean_uint16_dec_lt", implicit_reducible]
392:@[extern "lean_uint16_dec_le", implicit_reducible]
413:@[extern "lean_uint32_mul"]
423:@[extern "lean_uint32_div"]
449:@[extern "lean_uint32_mod"]
463:@[extern "lean_uint32_land"]
473:@[extern "lean_uint32_lor"]
483:@[extern "lean_uint32_xor"]
490:@[extern "lean_uint32_shift_left"]
497:@[extern "lean_uint32_shift_right"]
530:@[extern "lean_uint32_complement"]
539:@[extern "lean_uint32_neg"]
553:@[extern "lean_bool_to_uint32"]
568:@[extern "lean_uint64_add"]
576:@[extern "lean_uint64_sub"]
584:@[extern "lean_uint64_mul"]
594:@[extern "lean_uint64_div"]
620:@[extern "lean_uint64_mod"]
634:@[extern "lean_uint64_land"]
644:@[extern "lean_uint64_lor"]
654:@[extern "lean_uint64_xor"]
661:@[extern "lean_uint64_shift_left"]
668:@[extern "lean_uint64_shift_right"]
702:@[extern "lean_uint64_complement"]
711:@[extern "lean_uint64_neg"]
725:@[extern "lean_bool_to_uint64"]
739:@[extern "lean_uint64_dec_lt", implicit_reducible]
755:@[extern "lean_uint64_dec_le", implicit_reducible]
779:@[extern "lean_usize_mul"]
789:@[extern "lean_usize_div"]
815:@[extern "lean_usize_mod"]
829:@[extern "lean_usize_land"]
839:@[extern "lean_usize_lor"]
849:@[extern "lean_usize_xor"]
856:@[extern "lean_usize_shift_left"]
863:@[extern "lean_usize_shift_right"]
871:@[extern "lean_usize_of_nat"]
879:@[extern "lean_uint8_to_usize"]
887:@[extern "lean_usize_to_uint8"]
894:@[extern "lean_uint16_to_usize"]
902:@[extern "lean_usize_to_uint16"]
909:@[extern "lean_uint32_to_usize"]
917:@[extern "lean_usize_to_uint32"]
925:@[extern "lean_uint64_to_usize"]
933:@[extern "lean_usize_to_uint64"]
954:@[extern "lean_usize_complement"]
961:@[extern "lean_usize_neg"]
975:@[extern "lean_bool_to_usize"]

src/Init/Data/UInt/Log2.lean
29:@[extern "lean_uint8_log2"]
46:@[extern "lean_uint16_log2"]
63:@[extern "lean_uint32_log2"]
80:@[extern "lean_uint64_log2"]
97:@[extern "lean_usize_log2"]

src/Init/GetElem.lean
394:-- so that we use the `@[extern]` definition of `get!Internal`.

src/Init/Meta/Defs.lean
23:@[extern "lean_version_get_major"]
27:@[extern "lean_version_get_minor"]
31:@[extern "lean_version_get_patch"]
35:@[extern "lean_get_githash"]
39:@[extern "lean_version_get_is_release"]
44:@[extern "lean_version_get_special_desc"]
85:@[extern "lean_internal_is_stage0"]
94:@[extern "lean_internal_has_llvm_backend"]

src/Init/Prelude.lean
116:@[extern "lean_is_scalar"]
744:@[extern "lean_sorry", never_extract]
1755:@[extern "lean_nat_add", implicit_reducible]
1774:@[extern "lean_nat_mul", implicit_reducible]
1789:@[extern "lean_nat_pow"]
1803:@[extern "lean_nat_dec_eq"]
1853:@[reducible, extern "lean_nat_dec_eq"]
1873:@[extern "lean_nat_dec_le"]
1957:@[extern "lean_nat_pred"]
2070:@[extern "lean_nat_dec_le"]
2084:@[extern "lean_nat_dec_lt"]
2105:@[extern "lean_nat_sub", implicit_reducible]
2164:@[extern "lean_nat_div", irreducible]
2194:@[extern "lean_nat_mod"]
2252:@[extern "lean_nat_mod"]
2284:@[extern "lean_system_platform_nbits"] opaque System.Platform.getNumBits : Unit → Subtype fun (n : Nat) => Or (Eq n 32) (Eq n 64) :=
2429:attribute [extern "lean_uint8_of_nat_mk"] UInt8.ofBitVec
2430:attribute [extern "lean_uint8_to_nat"] UInt8.toBitVec
2438:@[extern "lean_uint8_of_nat"]
2454:@[extern "lean_uint8_of_nat"]
2469:@[extern "lean_uint8_dec_eq"]
2506:@[extern "lean_uint8_dec_lt", implicit_reducible]
2522:@[extern "lean_uint8_dec_le", implicit_reducible]
2547:attribute [extern "lean_uint16_of_nat_mk"] UInt16.ofBitVec
2548:attribute [extern "lean_uint16_to_nat"] UInt16.toBitVec
2556:@[extern "lean_uint16_of_nat"]
2573:@[extern "lean_uint16_dec_eq"]
2605:attribute [extern "lean_uint32_of_nat_mk"] UInt32.ofBitVec
2606:attribute [extern "lean_uint32_to_nat"] UInt32.toBitVec
2614:@[extern "lean_uint32_of_nat"]
2623:@[extern "lean_uint32_to_nat"]
2638:@[extern "lean_uint32_dec_eq"]
2666:@[extern "lean_uint32_dec_lt", implicit_reducible]
2682:@[extern "lean_uint32_dec_le", implicit_reducible]
2710:attribute [extern "lean_uint64_of_nat_mk"] UInt64.ofBitVec
2711:attribute [extern "lean_uint64_to_nat"] UInt64.toBitVec
2719:@[extern "lean_uint64_of_nat"]
2736:@[extern "lean_uint64_dec_eq"]
2781:attribute [extern "lean_usize_of_nat_mk"] USize.ofBitVec
2782:attribute [extern "lean_usize_to_nat"] USize.toBitVec
2790:@[extern "lean_usize_of_nat"]
2806:@[extern "lean_usize_dec_eq"]
2853:@[extern "lean_uint32_of_nat"]
3189:attribute [extern "lean_array_to_list"] Array.toList
3190:attribute [extern "lean_array_mk"] Array.mk
3210:@[extern "lean_mk_empty_array_with_capacity"]
3217:@[extern "lean_mk_empty_array_with_capacity"]
3236:@[extern "lean_array_get_size", tagged_return, implicit_reducible]
3245:@[extern "lean_array_fget_borrowed"]
3259:@[extern "lean_array_fget"]
3283:@[extern "lean_array_get_borrowed"]
3291:@[extern "lean_array_get"]
3305:@[extern "lean_array_push"]
3402:attribute [extern "lean_byte_array_mk"] ByteArray.mk
3403:attribute [extern "lean_byte_array_data"] ByteArray.data
3408:@[extern "lean_mk_empty_byte_array"]
3425:@[extern "lean_byte_array_push"]
3444:@[extern "lean_byte_array_size", tagged_return]
3512:attribute [extern "lean_string_to_utf8"] String.toByteArray
3513:attribute [extern "lean_string_from_utf8_unchecked"] String.ofByteArray
3523:@[extern "lean_string_mk"]
3533:@[extern "lean_string_dec_eq"]
3603:@[extern "lean_string_utf8_byte_size", tagged_return]
3671:@[never_extract, extern "lean_panic_fn_borrowed"]
4643:@[extern "lean_uint64_mix_hash"]
4652:@[extern "lean_string_hash"]
4781:@[extern "lean_name_eq"]

src/Init/ShareCommon.lean
42:@[extern "lean_sharecommon_eq"]
45:@[extern "lean_sharecommon_hash"]
86:@[extern "lean_state_sharecommon"]
116:@[extern "lean_sharecommon_quick"]

src/Init/System/IO.lean
218:@[extern "lean_io_timeit"] opaque timeit (msg : @& String) (fn : IO α) : IO α
220:@[extern "lean_io_allocprof"] opaque allocprof (msg : @& String) (fn : IO α) : IO α
229:@[extern "lean_io_initializing"] opaque IO.initializing : BaseIO Bool
244:@[extern "lean_io_as_task"]
257:@[extern "lean_io_map_task"]
271:@[extern "lean_io_bind_task"]
415:@[extern "lean_io_mono_ms_now"] opaque monoMsNow : BaseIO Nat
421:@[extern "lean_io_mono_nanos_now"] opaque monoNanosNow : BaseIO Nat
428:@[extern "lean_io_get_random_bytes"] opaque getRandomBytes (nBytes : USize) : IO ByteArray
505:@[extern "lean_io_check_canceled"] opaque checkCanceled : BaseIO Bool
511:@[extern "lean_io_cancel"] opaque cancel : @& Task α → BaseIO Unit
555:@[extern "lean_io_get_task_state"] opaque getTaskState : @& Task α → BaseIO TaskState
567:@[extern "lean_io_wait"] opaque wait (t : Task α) : BaseIO α :=
573:@[extern "lean_io_wait_any"] opaque waitAny (tasks : @& List (Task α))
594:@[extern "lean_io_get_num_heartbeats"] opaque getNumHeartbeats : BaseIO Nat
600:@[extern "lean_io_set_heartbeats"] opaque setNumHeartbeats (count : Nat) : BaseIO Unit
742:@[extern "lean_get_stdin"] opaque getStdin  : BaseIO FS.Stream
748:@[extern "lean_get_stdout"] opaque getStdout : BaseIO FS.Stream
754:@[extern "lean_get_stderr"] opaque getStderr : BaseIO FS.Stream
761:@[extern "lean_get_set_stdin"] opaque setStdin  : FS.Stream → BaseIO FS.Stream
767:@[extern "lean_get_set_stdout"] opaque setStdout : FS.Stream → BaseIO FS.Stream
773:@[extern "lean_get_set_stderr"] opaque setStderr : FS.Stream → BaseIO FS.Stream
795:@[extern "lean_io_prim_handle_mk"] opaque mk (fn : @& FilePath) (mode : FS.Mode) : IO Handle
803:@[extern "lean_io_prim_handle_lock"] opaque lock (h : @& Handle) (exclusive := true) : IO Unit
811:@[extern "lean_io_prim_handle_try_lock"] opaque tryLock (h : @& Handle) (exclusive := true) : IO Bool
815:@[extern "lean_io_prim_handle_unlock"] opaque unlock (h : @& Handle) : IO Unit
820:@[extern "lean_io_prim_handle_is_tty"] opaque isTty (h : @& Handle) : BaseIO Bool
826:@[extern "lean_io_prim_handle_flush"] opaque flush (h : @& Handle) : IO Unit
830:@[extern "lean_io_prim_handle_rewind"] opaque rewind (h : @& Handle) : IO Unit
840:@[extern "lean_io_prim_handle_truncate"] opaque truncate (h : @& Handle) : IO Unit
847:@[extern "lean_io_prim_handle_read"] opaque read (h : @& Handle) (bytes : USize) : IO ByteArray
854:@[extern "lean_io_prim_handle_write"] opaque write (h : @& Handle) (buffer : @& ByteArray) : IO Unit
862:@[extern "lean_io_prim_handle_get_line"] opaque getLine (h : @& Handle) : IO String
869:@[extern "lean_io_prim_handle_put_str"] opaque putStr (h : @& Handle) (s : @& String) : IO Unit
879:@[extern "lean_io_realpath"] opaque realPath (fname : FilePath) : IO FilePath
886:@[extern "lean_io_remove_file"] opaque removeFile (fname : @& FilePath) : IO Unit
894:@[extern "lean_io_remove_dir"] opaque removeDir : @& FilePath → IO Unit
900:@[extern "lean_io_create_dir"] opaque createDir : @& FilePath → IO Unit
909:@[extern "lean_io_rename"] opaque rename (old new : @& FilePath) : IO Unit
921:@[extern "lean_io_hard_link"] opaque hardLink (orig link : @& FilePath) : IO Unit
933:@[extern "lean_io_create_tempfile"] opaque createTempFile : IO (Handle × FilePath)
943:@[extern "lean_io_create_tempdir"] opaque createTempDir : IO FilePath
951:@[extern "lean_io_getenv"] opaque getEnv (var : @& String) : BaseIO (Option String)
955:@[extern "lean_io_app_path"] opaque appPath : IO FilePath
959:@[extern "lean_io_current_dir"] opaque currentDir : IO FilePath
1141:@[extern "lean_io_read_dir"]
1148:@[extern "lean_io_metadata"]
1155:@[extern "lean_io_symlink_metadata"]
1383:@[extern "lean_io_process_get_current_dir"] opaque getCurrentDir : IO FilePath
1386:@[extern "lean_io_process_set_current_dir"] opaque setCurrentDir (path : @& FilePath) : IO Unit
1389:@[extern "lean_io_process_get_pid"] opaque getPID : BaseIO UInt32
1489:@[extern "lean_io_process_spawn"] opaque spawn (args : SpawnArgs) : IO (Child args.toStdioConfig)
1494:@[extern "lean_io_process_child_wait"] opaque Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32
1500:@[extern "lean_io_process_child_try_wait"] opaque Child.tryWait {cfg : @& StdioConfig} : @& Child cfg →
1508:@[extern "lean_io_process_child_kill"] opaque Child.kill {cfg : @& StdioConfig} : @& Child cfg → IO Unit
1520:@[extern "lean_io_process_child_take_stdin"] opaque Child.takeStdin {cfg : @& StdioConfig} : Child cfg →
1524:@[extern "lean_io_process_child_pid"] opaque Child.pid {cfg : @& StdioConfig} : Child cfg → UInt32
1579:@[extern "lean_io_exit"] opaque exit : UInt8 → IO α
1588:@[extern "lean_io_force_exit"] opaque forceExit : UInt8 → IO α
1593:@[extern "lean_io_get_tid"] opaque getTID : BaseIO UInt64
1650:@[extern "lean_chmod"] opaque Prim.setAccessRights (filename : @& FilePath) (mode : UInt32) : IO Unit
1826:@[extern "lean_runtime_mark_multi_threaded"]
1839:@[extern "lean_runtime_mark_persistent"]
1850:@[extern "lean_runtime_forget"]
1859:@[extern "lean_runtime_hold"]

src/Init/System/Platform.lean
22:@[extern "lean_system_platform_windows"] opaque getIsWindows : Unit → Bool
26:@[extern "lean_system_platform_osx"] opaque getIsOSX : Unit → Bool
30:@[extern "lean_system_platform_emscripten"] opaque getIsEmscripten : Unit → Bool
51:@[extern "lean_system_platform_target"] opaque getTarget : Unit → String

src/Init/System/Promise.lean
40:@[extern "lean_io_promise_new"]
48:@[extern "lean_io_promise_resolve"]
54:@[extern "lean_io_promise_result_opt"]
58:@[extern "lean_option_get_or_block"]

src/Init/System/ST.lean
22:@[extern "lean_void_mk", never_extract]
186:@[extern "lean_st_mk_ref"]
188:@[extern "lean_st_ref_get"]
190:@[extern "lean_st_ref_set"]
192:@[extern "lean_st_ref_swap"]
194:@[extern "lean_st_ref_take"]
196:@[extern "lean_st_ref_ptr_eq"]

src/Init/Util.lean
18:@[never_extract, extern "lean_dbg_trace"]
26:@[never_extract, extern "lean_dbg_trace_if_shared"]
30:@[never_extract, extern "lean_dbg_stack_trace"]
41:@[extern "lean_dbg_sleep"]
89:@[extern "lean_ptr_addr"]
98:@[extern "lean_is_exclusive_obj"]

src/lake/Lake/Config/LeanConfig.lean
243:  (e.g., precompiled modules, external libraries) from a module's trace,

src/lake/Lake/Config/LeanLibConfig.lean
78:  metaprograms and enables the interpreter to run functions marked `@[extern]`.

src/lake/Lake/Config/PackageConfig.lean
38:  metaprograms and enables the interpreter to run functions marked `@[extern]`.

src/lake/Lake/DSL/Syntax.lean
454:One can use this command to specify, for example, external library targets

src/lake/Lake/Load/Lean/Elab.lean
96:@[extern "lake_environment_add"]

src/Lean/CompactedRegion.lean
21:@[extern "lean_compacted_region_is_memory_mapped"]
25:@[extern "lean_compacted_region_size"]
32:@[extern "lean_compacted_region_free"]
69:@[extern "lean_compacted_region_save"]
83:@[extern "lean_compacted_region_read"]

src/Lean/Compiler/ExportAttr.lean
40:The opposite of this is `@[extern]`, which allows Lean functions to refer to functions from other

src/Lean/Compiler/ExternAttr.lean
28:- `@[extern]`
30:- `@[extern "level_hash"]`
32:- `@[extern cpp "lean::string_size" llvm "lean_str_size"]`
34:- `@[extern cpp inline "#1 + #2"]`
36:- `@[extern cpp "foo" llvm adhoc]`

src/Lean/Compiler/FFI.lean
18:@[extern "lean_get_leanc_extra_flags"]
35:@[extern "lean_get_leanc_internal_flags"]
42:@[extern "lean_get_linker_flags"]
56:@[extern "lean_get_internal_linker_flags"]

src/Lean/Compiler/InitAttr.lean
32:@[extern "lean_run_mod_init_core"]
44:@[extern "lean_run_init"]

src/Lean/Compiler/IR/Checker.lean
15:@[extern "lean_get_max_ctor_fields"]
19:@[extern "lean_get_max_ctor_scalars_size"]
23:@[extern "lean_get_max_ctor_tag"]
27:@[extern "lean_get_usize_size"]

src/Lean/Compiler/IR/LLVMBindings.lean
95:@[extern "lean_llvm_get_value_name2"]
102:@[extern "lean_llvm_initialize_target_info"]
105:@[extern "lean_llvm_create_context"]
108:@[extern "lean_llvm_create_module"]
111:@[extern "lean_llvm_module_to_string"]
114:@[extern "lean_llvm_write_bitcode_to_file"]
117:@[extern "lean_llvm_add_function"]
120:@[extern "lean_llvm_get_first_function"]
123:@[extern "lean_llvm_get_next_function"]
126:@[extern "lean_llvm_get_named_function"]
129:@[extern "lean_llvm_add_global"]
132:@[extern "lean_llvm_get_named_global"]
135:@[extern "lean_llvm_get_first_global"]
138:@[extern "lean_llvm_get_next_global"]
141:@[extern "lean_llvm_build_global_string"]
144:@[extern "llvm_is_declaration"]
147:@[extern "lean_llvm_set_initializer"]
150:@[extern "lean_llvm_function_type"]
153:@[extern "lean_llvm_void_type_in_context"]
156:@[extern "lean_llvm_int_type_in_context"]
159:@[extern "lean_llvm_opaque_pointer_type_in_context"]
162:@[extern "lean_llvm_float_type_in_context"]
165:@[extern "lean_llvm_double_type_in_context"]
168:@[extern "lean_llvm_pointer_type"]
171:@[extern "lean_llvm_array_type"]
174:@[extern "lean_llvm_const_array"]
178:@[extern "lean_llvm_const_string"]
181:@[extern "lean_llvm_const_pointer_null"]
184:@[extern "lean_llvm_get_undef"]
187:@[extern "lean_llvm_create_builder_in_context"]
190:@[extern "lean_llvm_append_basic_block_in_context"]
193:@[extern "lean_llvm_count_basic_blocks"]
196:@[extern "lean_llvm_get_entry_basic_block"]
199:@[extern "lean_llvm_get_first_instruction"]
202:@[extern "lean_llvm_position_builder_before"]
205:@[extern "lean_llvm_position_builder_at_end"]
208:@[extern "lean_llvm_build_call2"]
211:@[extern "lean_llvm_set_tail_call"]
214:@[extern "lean_llvm_build_cond_br"]
217:@[extern "lean_llvm_build_br"]
220:@[extern "lean_llvm_build_alloca"]
223:@[extern "lean_llvm_build_load2"]
226:@[extern "lean_llvm_build_store"]
229:@[extern "lean_llvm_build_ret"]
232:@[extern "lean_llvm_build_unreachable"]
235:@[extern "lean_llvm_build_gep2"]
238:@[extern "lean_llvm_build_inbounds_gep2"]
241:@[extern "lean_llvm_build_sext"]
244:@[extern "lean_llvm_build_zext"]
247:@[extern "lean_llvm_build_sext_or_trunc"]
250:@[extern "lean_llvm_build_switch"]
253:@[extern "lean_llvm_build_ptr_to_int"]
256:@[extern "lean_llvm_build_mul"]
259:@[extern "lean_llvm_build_add"]
262:@[extern "lean_llvm_build_sub"]
265:@[extern "lean_llvm_build_not"]
268:@[extern "lean_llvm_build_icmp"]
271:@[extern "lean_llvm_add_case"]
274:@[extern "lean_llvm_get_insert_block"]
277:@[extern "lean_llvm_clear_insertion_position"]
280:@[extern "lean_llvm_get_basic_block_parent"]
283:@[extern "lean_llvm_type_of"]
286:@[extern "lean_llvm_const_int"]
289:@[extern "lean_llvm_print_module_to_string"]
292:@[extern "lean_llvm_print_module_to_file"]
295:@[extern "llvm_count_params"]
298:@[extern "llvm_get_param"]
301:@[extern "lean_llvm_create_memory_buffer_with_contents_of_file"]
304:@[extern "lean_llvm_parse_bitcode"]
307:@[extern "lean_llvm_link_modules"]
310:@[extern "lean_llvm_get_default_target_triple"]
313:@[extern "lean_llvm_get_target_from_triple"]
316:@[extern "lean_llvm_create_target_machine"]
319:@[extern "lean_llvm_target_machine_emit_to_file"]
323:@[extern "lean_llvm_create_pass_manager"]
326:@[extern "lean_llvm_dispose_pass_manager"]
329:@[extern "lean_llvm_run_pass_manager"]
332:@[extern "lean_llvm_create_pass_manager_builder"]
335:@[extern "lean_llvm_dispose_pass_manager_builder"]
338:@[extern "lean_llvm_pass_manager_builder_set_opt_level"]
341:@[extern "lean_llvm_pass_manager_builder_populate_module_pass_manager"]
345:@[extern "lean_llvm_dispose_target_machine"]
348:@[extern "lean_llvm_dispose_module"]
351:@[extern "lean_llvm_verify_module"]
354:@[extern "lean_llvm_create_string_attribute"]
357:@[extern "lean_llvm_add_attribute_at_index"]
369:@[extern "lean_llvm_set_visibility"]
380:@[extern "lean_llvm_set_dll_storage_class"]
421:@[extern "lean_llvm_set_linkage"]

src/Lean/Compiler/LCNF/EmitRust.lean
763:  -- 1. Local functions with @[extern "name"] need a declaration (they won't be defined here).
771:  -- 2. Other-module @[extern "name"] functions still need explicit declarations while
791:  --    (Skip those that have @[extern "name"] — already declared in section 2.)

src/Lean/Compiler/Old.lean
33:  | .axiomDecl { name, .. }  => #[name] -- axiom may be tagged with `@[extern ...]`

src/Lean/DocString/Links.lean
23:@[extern "lean_manual_get_root"]

src/Lean/Elab/Tactic/Try.lean
661:@[extern "lean_eval_suggest_tactic"] -- forward definition to avoid mutual block

src/Lean/Environment.lean
296:@[extern "lean_add_decl"]
307:@[extern "lean_add_decl_without_checking"]
687:@[extern "lean_elab_add_decl"]
691:@[extern "lean_elab_add_decl_without_checking"]
756:@[extern "lean_is_reserved_name"]
1797:@[extern "lean_get_ir_extra_const_names"]
1855:@[extern "lean_ir_export_entries"]
1925:@[extern "lean_update_env_attributes"] opaque updateEnvAttributes : Environment → IO Environment
1929:@[extern "lean_get_num_attributes"] opaque getNumBuiltinAttributes : IO Nat
1932:@[extern "lean_run_init_attrs"]
2451:@[extern "lean_eval_const"]
2455:@[extern "lean_eval_check_meta"]
2719:@[extern "lean_kernel_is_def_eq"]
2731:@[extern "lean_kernel_whnf"]
2740:@[extern "lean_kernel_check"]

src/Lean/Expr.lean
163:@[extern "lean_uint8_to_uint64"]
170:@[extern "lean_expr_mk_data"]
175:@[extern "lean_expr_mk_app_data"]
471:  @[computed_field, extern "lean_expr_data"]
778:@[extern "lean_expr_dbg_to_string"]
782:@[extern "lean_expr_quick_lt"]
786:@[extern "lean_expr_lt"]
798:@[extern "lean_expr_eqv"]
808:@[extern "lean_expr_equal"]
1319:@[extern "lean_expr_has_loose_bvar"]
1346:@[extern "lean_expr_lower_loose_bvars"]
1351:@[extern "lean_expr_lift_loose_bvars"]
1418:@[extern "lean_expr_instantiate"]
1435:@[extern "lean_expr_instantiate1"]
1449:@[extern "lean_expr_instantiate_rev"]
1461:@[extern "lean_expr_instantiate_range"]
1473:@[extern "lean_expr_instantiate_rev_range"]
1483:@[extern "lean_expr_abstract"]
1487:@[extern "lean_expr_abstract_range"]

src/Lean/Level.lean
48:@[extern "lean_level_mk_data"]
254:@[extern "lean_level_eq"]

src/Lean/Linter/UnusedVariables.lean
228:* `@[extern "bla"] def foo (unused : Nat) : Nat := ...`

src/Lean/LoadDynlib.lean
33:@[extern "lean_dynlib_load"]
37:@[extern "lean_dynlib_get"]
53:@[extern "lean_dynlib_symbol_run_as_init"]
58:the Lean interpreter (e.g., for interpreting `@[extern]` declarations).

src/Lean/Meta/Basic.lean
777:@[extern "lean_whnf"] opaque whnf : Expr → MetaM Expr
832:@[extern "lean_infer_type"] opaque inferType : Expr → MetaM Expr
834:@[extern "lean_is_expr_def_eq"] opaque isExprDefEqAux : Expr → Expr → MetaM Bool
836:@[extern "lean_is_level_def_eq"] opaque isLevelDefEqAux : Level → Level → MetaM Bool
838:@[extern "lean_synth_pending"] protected opaque synthPending : MVarId → MetaM Bool
2525:@[extern "lean_checked_assign"]

src/Lean/Meta/Match/MatchEqsExt.lean
50:@[extern "lean_get_match_equations_for"]
57:@[extern "lean_get_congr_match_equations_for"]

src/Lean/Meta/Match/Match.lean
1187:       @[extern "lean_int_neg"] def neg (n : @& Int) : Int :=

src/Lean/Meta/Sym/DSimp/DSimpM.lean
103:@[extern "lean_sym_dsimp"] -- Forward declaration

src/Lean/Meta/Sym/Pattern.lean
673:@[extern "lean_sym_def_eq"] -- Forward definition

src/Lean/Meta/Sym/Simp/SimpM.lean
270:@[extern "lean_sym_simp"] -- Forward declaration

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean
233:@[extern "lean_cutsat_eq_cnstr_to_proof"] -- forward definition

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Util.lean
46:@[extern "lean_grind_cutsat_mk_var"] -- forward definition
67:@[extern "lean_grind_cutsat_assert_eq"] -- forward definition
120:@[extern "lean_grind_cutsat_assert_le"] -- forward definition

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Var.lean
16:@[extern "lean_cutsat_propagate_nonlinear"]

src/Lean/Meta/Tactic/Grind/Types.lean
1432:@[extern "lean_grind_mk_eq_proof"]
1441:@[extern "lean_grind_mk_heq_proof"]
1446:@[extern "lean_grind_process_new_facts"]
1451:@[extern "lean_grind_internalize"]
1456:@[extern "lean_grind_preprocess"]

src/Lean/Meta/Tactic/Grind/Util.lean
136:@[extern "lean_grind_normalize"] -- forward definition

src/Lean/Meta/Tactic/Simp/Types.lean
302:@[extern "lean_simp"]
306:@[extern "lean_dsimp"]

src/Lean/MetavarContext.lean
568:@[extern "lean_instantiate_level_mvars"]
576:@[extern "lean_instantiate_expr_mvars"]

src/Lean/Meta/WHNF.lean
45:@[extern "lean_get_structural_rec_arg_pos"]

src/Lean/MonadEnv.lean
178:@[extern "lean_has_compile_error"]

src/Lean/Parser/Term.lean
391:Indicates that an argument to a function marked `@[extern]` is borrowed.
393:Being borrowed only affects the ABI and runtime behavior of the function when compiled or interpreted. From the perspective of Lean's type system, this annotation has no effect. It similarly has no effect on functions not marked `@[extern]`.

src/Lean/PrettyPrinter/Formatter.lean
238:@[extern "lean_mk_antiquot_formatter"]
243:@[extern "lean_pretty_printer_formatter_interpret_parser_descr"]

src/Lean/PrettyPrinter/Parenthesizer.lean
312:@[extern "lean_mk_antiquot_parenthesizer"]
320:@[extern "lean_pretty_printer_parenthesizer_interpret_parser_descr"]

src/Lean/Runtime.lean
15:@[extern "lean_closure_max_args"]
18:@[extern "lean_max_small_nat"]
21:@[extern "lean_libuv_version"]

src/Lean/Setup.lean
37:@[extern "lean_idbg_client_loop"]

src/Lean/Shell.lean
31:@[extern "lean_decode_lossy_utf8"]
35:@[extern "lean_eval_main"]
42:@[extern "lean_init_llvm"]
49:@[extern "lean_emit_llvm"]
53:@[extern "lean_internal_has_address_sanitizer"]
57:@[extern "lean_internal_is_multi_thread"]
61:@[extern "lean_internal_is_debug"]
65:@[extern "lean_internal_get_build_type"]
72:@[extern "lean_internal_get_default_max_memory"]
76:@[extern "lean_internal_set_max_memory"]
83:@[extern "lean_internal_get_default_max_heartbeat"]
87:@[extern "lean_internal_set_max_heartbeat"]
91:@[extern "lean_internal_get_default_verbose"]
95:@[extern "lean_internal_set_exit_on_panic"]
99:@[extern "lean_internal_set_thread_stack_size"]
103:@[extern "lean_internal_enable_debug"]
202:@[extern "lean_internal_get_default_options"]
211:@[extern "lean_internal_get_believer_trust_level"]
219:@[extern "lean_internal_get_hardware_concurrency"]

src/Lean/Util/FindExpr.lean
16:@[extern "lean_find_expr"]
33:@[extern "lean_find_ext_expr"]

src/Lean/Util/Profile.lean
37:@[extern "lean_profileit"]
53:@[extern "lean_display_cumulative_profiling_times"]

src/Lean/Util/ReplaceExpr.lean
16:@[extern "lean_replace_expr"]

src/Lean/Util/TestExtern.lean
37:        throwError "test_extern: {f} does not have an @[extern] attribute or @[implemented_by] attribute"

src/Std/Data/ByteSlice.lean
185:@[extern "lean_byteslice_beq"]

src/Std/Internal/UV/DNS.lean
25:@[extern "lean_uv_dns_get_info"]
32:@[extern "lean_uv_dns_get_name"]

src/Std/Internal/UV/Loop.lean
36:@[extern "lean_uv_event_loop_configure"]
42:@[extern "lean_uv_event_loop_alive"]

src/Std/Internal/UV/Signal.lean
46:@[extern "lean_uv_signal_mk"]
67:@[extern "lean_uv_signal_next"]
77:@[extern "lean_uv_signal_stop"]
86:@[extern "lean_uv_signal_cancel"]

src/Std/Internal/UV/System.lean
98:@[extern "lean_uv_get_process_title"]
104:@[extern "lean_uv_set_process_title"]
110:@[extern "lean_uv_uptime"]
116:@[extern "lean_uv_os_getpid"]
122:@[extern "lean_uv_os_getppid"]
128:@[extern "lean_uv_cpu_info"]
134:@[extern "lean_uv_cwd"]
140:@[extern "lean_uv_chdir"]
146:@[extern "lean_uv_os_homedir"]
152:@[extern "lean_uv_os_tmpdir"]
158:@[extern "lean_uv_os_get_passwd"]
164:@[extern "lean_uv_os_get_group"]
170:@[extern "lean_uv_os_environ"]
176:@[extern "lean_uv_os_getenv"]
182:@[extern "lean_uv_os_setenv"]
188:@[extern "lean_uv_os_unsetenv"]
194:@[extern "lean_uv_os_gethostname"]
200:@[extern "lean_uv_os_getpriority"]
206:@[extern "lean_uv_os_setpriority"]
212:@[extern "lean_uv_os_uname"]
218:@[extern "lean_uv_hrtime"]
224:@[extern "lean_uv_random"]
230:@[extern "lean_uv_getrusage"]
236:@[extern "lean_uv_exepath"]
242:@[extern "lean_uv_get_free_memory"]
248:@[extern "lean_uv_get_total_memory"]
254:@[extern "lean_uv_get_constrained_memory"]
260:@[extern "lean_uv_get_available_memory"]

src/Std/Internal/UV/TCP.lean
36:@[extern "lean_uv_tcp_new"]
42:@[extern "lean_uv_tcp_connect"]
48:@[extern "lean_uv_tcp_send"]
58:@[extern "lean_uv_tcp_recv"]
66:@[extern "lean_uv_tcp_wait_readable"]
77:@[extern "lean_uv_tcp_cancel_recv"]
83:@[extern "lean_uv_tcp_bind"]
89:@[extern "lean_uv_tcp_listen"]
95:@[extern "lean_uv_tcp_accept"]
101:@[extern "lean_uv_tcp_try_accept"]
107:@[extern "lean_uv_tcp_cancel_accept"]
113:@[extern "lean_uv_tcp_shutdown"]
119:@[extern "lean_uv_tcp_getpeername"]
125:@[extern "lean_uv_tcp_getsockname"]
131:@[extern "lean_uv_tcp_nodelay"]
137:@[extern "lean_uv_tcp_keepalive"]

src/Std/Internal/UV/Timer.lean
44:@[extern "lean_uv_timer_mk"]
63:@[extern "lean_uv_timer_next"]
74:@[extern "lean_uv_timer_reset"]
83:@[extern "lean_uv_timer_stop"]
92:@[extern "lean_uv_timer_cancel"]

src/Std/Internal/UV/UDP.lean
35:@[extern "lean_uv_udp_new"]
42:@[extern "lean_uv_udp_bind"]
49:@[extern "lean_uv_udp_connect"]
56:@[extern "lean_uv_udp_send"]
64:@[extern "lean_uv_udp_recv"]
71:@[extern "lean_uv_udp_wait_readable"]
81:@[extern "lean_uv_udp_cancel_recv"]
89:@[extern "lean_uv_udp_getpeername"]
95:@[extern "lean_uv_udp_getsockname"]
101:@[extern "lean_uv_udp_set_broadcast"]
107:@[extern "lean_uv_udp_set_multicast_loop"]
113:@[extern "lean_uv_udp_set_multicast_ttl"]
120:@[extern "lean_uv_udp_set_membership"]
126:@[extern "lean_uv_udp_set_multicast_interface"]
132:@[extern "lean_uv_udp_set_ttl"]

src/Std/Net/Addr.lean
108:@[extern "lean_uv_pton_v4"]
114:@[extern "lean_uv_ntop_v4"]
147:@[extern "lean_uv_pton_v6"]
154:@[extern "lean_uv_ntop_v6"]
257:@[extern "lean_uv_interface_addresses"]

src/Std/Sync/Mutex.lean
28:@[extern "lean_io_basemutex_new"]
38:@[extern "lean_io_basemutex_lock"]
51:@[extern "lean_io_basemutex_try_lock"]
61:@[extern "lean_io_basemutex_unlock"]
92:@[extern "lean_io_condvar_new"]
96:@[extern "lean_io_condvar_wait"]
100:@[extern "lean_io_condvar_notify_one"]
104:@[extern "lean_io_condvar_notify_all"]

src/Std/Sync/RecursiveMutex.lean
27:@[extern "lean_io_baserecmutex_new"]
34:@[extern "lean_io_baserecmutex_lock"]
44:@[extern "lean_io_baserecmutex_try_lock"]
54:@[extern "lean_io_baserecmutex_unlock"]

src/Std/Sync/SharedMutex.lean
27:@[extern "lean_io_basesharedmutex_new"]
37:@[extern "lean_io_basesharedmutex_write"]
47:@[extern "lean_io_basesharedmutex_try_write"]
56:@[extern "lean_io_basesharedmutex_unlock_write"]
67:@[extern "lean_io_basesharedmutex_read"]
77:@[extern "lean_io_basesharedmutex_try_read"]
86:@[extern "lean_io_basesharedmutex_unlock_read"]

src/Std/Time/DateTime/Timestamp.lean
70:@[extern "lean_get_current_time"]

src/Std/Time/Zoned/Database/Windows.lean
26:@[extern "lean_windows_get_next_transition"]
32:@[extern "lean_get_windows_local_timezone_id_at"]
```


# list of all functions that rust imports from lean

```sh
 ~/projects/lean4   rust-rewrite ±✚  ag -s 'attribute \[export|@\[export|, export' ./src/**/*.lean          <<<
src/Init/Data/Array/Basic.lean
1436:@[export lean_array_to_list_impl]

src/Init/Data/List/ToArrayImpl.lean
35:@[inline, expose, match_pattern, pp_nodot, export lean_list_to_array]

src/Init/Data/OfScientific.lean
71:@[export lean_float_of_nat]
116:@[export lean_float32_of_nat]

src/Init/Data/String/Basic.lean
3056:@[export lean_string_offsetofpos]

src/Init/Data/String/Defs.lean
222:@[export lean_string_pushn]
239:@[export lean_string_isempty]
271:@[export lean_string_intercalate]

src/Init/Data/String/Iterate.lean
474:@[export lean_string_foldl]

src/Init/Data/String/Modify.lean
249:@[export lean_string_capitalize]

src/Init/Data/String/PosRaw.lean
32:@[export lean_string_pos_sub]
306:@[export lean_string_pos_min]

src/Init/Data/String/Search.lean
194:@[export lean_string_posof]
303:@[export lean_string_contains]
310:@[export lean_string_any]
472:@[export lean_string_front]

src/Init/Data/String/Substring.lean
51:@[export lean_substring_isempty]
61:@[export lean_substring_tostring]
76:@[export lean_substring_get]
113:@[export lean_substring_prev]
150:@[export lean_substring_front]
170:@[export lean_substring_drop]
222:@[export lean_substring_extract]
289:@[export lean_substring_all]
317:@[export lean_substring_takewhile]
462:@[export lean_substring_beq]

src/Init/Data/String/TakeDrop.lean
45:@[export lean_string_drop]
75:@[export lean_string_dropright]
322:@[export lean_string_isprefixof]
445:@[export lean_string_trim]
466:@[export lean_string_nextwhile]

src/Init/Meta/Defs.lean
152:@[export lean_is_inaccessible_user_name]
316:@[export lean_name_append_after]
322:@[export lean_name_append_index_after]
328:@[export lean_name_append_before]
750:@[export lean_mk_syntax_ident]

src/Init/Prelude.lean
4729:@[export lean_name_mk_string]
4736:@[export lean_name_mk_numeral]
5610:@[export lean_erase_macro_scopes]
5621:@[export lean_simp_macro_scopes]

src/Init/System/CancelToken.lean
78:@[export lean_io_cancel_token_is_set]

src/Init/System/IOError.lean
150:@[export lean_mk_io_user_error]
158:@[export lean_mk_io_error_already_exists_file]
162:@[export lean_mk_io_error_eof]
166:@[export lean_mk_io_error_inappropriate_type_file]
170:@[export lean_mk_io_error_interrupted]
174:@[export lean_mk_io_error_invalid_argument_file]
178:@[export lean_mk_io_error_no_file_or_directory]
182:@[export lean_mk_io_error_no_such_thing_file]
186:@[export lean_mk_io_error_permission_denied_file]
190:@[export lean_mk_io_error_resource_exhausted_file]
194:@[export lean_mk_io_error_unsupported_operation]
198:@[export lean_mk_io_error_resource_exhausted]
202:@[export lean_mk_io_error_already_exists]
206:@[export lean_mk_io_error_inappropriate_type]
210:@[export lean_mk_io_error_no_such_thing]
214:@[export lean_mk_io_error_resource_vanished]
218:@[export lean_mk_io_error_resource_busy]
222:@[export lean_mk_io_error_invalid_argument]
226:@[export lean_mk_io_error_other_error]
230:@[export lean_mk_io_error_permission_denied]
234:@[export lean_mk_io_error_hardware_fault]
238:@[export lean_mk_io_error_unsatisfied_constraints]
242:@[export lean_mk_io_error_illegal_operation]
246:@[export lean_mk_io_error_protocol_error]
250:@[export lean_mk_io_error_time_expired]
271:@[export lean_io_error_to_string]

src/Init/System/IO.lean
1294:@[export lean_io_eprint]
1298:@[export lean_io_eprintln]
1682:@[export lean_stream_of_handle]

src/Lean/AddDecl.lean
128:      trace[addDecl] "private decl under `privateInPublic`, exporting as is"
138:      trace[addDecl] "no matching exporting rules, exporting as is"

src/Lean/Attributes.lean
461:@[export lean_is_attribute]
475:@[export lean_attribute_application_time]
510:@[export lean_update_env_attributes]
522:@[export lean_get_num_attributes] def getNumBuiltinAttributesImpl : IO Nat :=

src/Lean/Class.lean
77:@[export lean_is_class]
86:@[export lean_has_out_params]
136:@[export lean_mk_outparam_args_implicit]

src/Lean/Compiler/ExportAttr.lean
30:@[export lean_color_from_map]
55:@[export lean_get_export_name_for]

src/Lean/Compiler/InitAttr.lean
121:@[export lean_get_regular_init_fn_name_for]
125:@[export lean_get_init_fn_name_for]
159:@[export lean_run_init_attrs]

src/Lean/Compiler/IR/CompilerM.lean
120:@[export lean_ir_export_entries]
145:@[export lean_ir_find_env_decl]
157:@[export lean_ir_find_env_decl_boxed]
172:@[export lean_has_compile_error]
221:@[export lean_decl_get_sorry_dep]
228:@[export lean_get_ir_extra_const_names]

src/Lean/Compiler/IR/EmitLLVM.lean
1639:@[export lean_ir_emit_llvm]

src/Lean/Compiler/IR/Format.lean
111:@[export lean_ir_format_fn_body_head]

src/Lean/Compiler/IR/Meta.lean
56:@[export lean_eval_check_meta]

src/Lean/Compiler/LCNF/EmitRust.lean
764:  -- Skip if the name is also locally exported (via @[export]): the definition is in this file.
773:  --    Skip if the name is locally exported (@[export]) — the definition is already in this file.

src/Lean/Compiler/LCNF/InferBorrow.lean
216:  /-- Annotated as an owned parameter (currently only triggerable through `@[export]`)-/

src/Lean/Compiler/ModPkgExt.lean
61:(e.g., {lit}`main` and definitions with {lit}`@[export]`).
63:@[export lean_get_symbol_stem]

src/Lean/Compiler/NameDemangling.lean
18:line parsing. Called from the C runtime via `@[export]` for backtrace display. -/
335:@[export lean_demangle_bt_line_cstr]

src/Lean/Compiler/NameMangling.lean
144:@[export lean_mk_mangled_boxed_name]

src/Lean/Data/KVMap.lean
27:@[export lean_data_value_beq]
31:@[export lean_mk_bool_data_value] def mkBoolDataValueEx (b : Bool) : DataValue := DataValue.ofBool b
32:@[export lean_data_value_bool] def DataValue.getBoolEx : DataValue → Bool
45:@[export lean_data_value_to_string]

src/Lean/Data/Name.lean
21:@[export lean_name_hash_exported] def hashEx : Name → UInt64 :=

src/Lean/Data/Options.lean
32:@[export lean_options_get_empty]
115:@[export lean_register_option]
126:@[export lean_get_option_decls_array]
200:@[export lean_options_get_bool]
210:@[export lean_options_update_bool]

src/Lean/Declaration.lean
52:@[export lean_mk_reducibility_hints_regular]
56:@[export lean_reducibility_hints_get_height]
105:@[export lean_mk_axiom_val]
113:@[export lean_axiom_val_is_unsafe] def AxiomVal.isUnsafeEx (v : AxiomVal) : Bool :=
134:@[export lean_mk_definition_val]
139:@[export lean_definition_val_get_safety] def DefinitionVal.getSafetyEx (v : DefinitionVal) : DefinitionSafety :=
150:@[export lean_mk_theorem_val]
165:@[export lean_mk_opaque_val]
170:@[export lean_opaque_val_is_unsafe] def OpaqueVal.isUnsafeEx (v : OpaqueVal) : Bool :=
195:@[export lean_mk_inductive_decl]
199:@[export lean_is_unsafe_inductive_decl]
304:@[export lean_mk_inductive_val]
320:@[export lean_inductive_val_is_rec] def InductiveVal.isRecEx (v : InductiveVal) : Bool := v.isRec
321:@[export lean_inductive_val_is_unsafe] def InductiveVal.isUnsafeEx (v : InductiveVal) : Bool := v.isUnsafe
322:@[export lean_inductive_val_is_reflexive] def InductiveVal.isReflexiveEx (v : InductiveVal) : Bool := v.isReflexive
340:@[export lean_mk_constructor_val]
345:@[export lean_constructor_val_is_unsafe] def ConstructorVal.isUnsafeEx (v : ConstructorVal) : Bool := v.isUnsafe
383:@[export lean_mk_recursor_val]
390:@[export lean_recursor_k] def RecursorVal.kEx (v : RecursorVal) : Bool := v.k
391:@[export lean_recursor_is_unsafe] def RecursorVal.isUnsafeEx (v : RecursorVal) : Bool := v.isUnsafe
421:@[export lean_mk_quot_val]
426:@[export lean_quot_val_kind] def QuotVal.kindEx (v : QuotVal) : QuotKind := v.kind

src/Lean/Elab/Idbg.lean
238:@[nospecialize, export lean_idbg_client_loop] def idbgClientLoopImpl

src/Lean/Elab/PreDefinition/Structural/Eqns.lean
190:@[export lean_get_structural_rec_arg_pos]

src/Lean/Elab/Tactic/Try.lean
837:@[export lean_eval_suggest_tactic]

src/Lean/Environment.lean
282:@[export lean_environment_find]
287:@[export lean_environment_mark_quot_init]
291:@[export lean_environment_quot_init]
310:@[export lean_environment_add]
314:@[export lean_kernel_diag_is_enabled]
328:@[export lean_kernel_record_unfold]
336:@[export lean_kernel_get_diag]
340:@[export lean_kernel_set_diag]
644:@[export lean_elab_environment_of_kernel_env]
648:@[export lean_elab_environment_to_kernel_env]
742:@[export lake_environment_add]
1051:    constName, kind, exportedKind?
1496:@[export lean_mk_empty_environment]
1768:@[noinline, export lean_environment_free_regions]
2413:@[export lean_elab_environment_update_base_after_kernel_add]

src/Lean/Expr.lean
607:@[export lean_expr_hash] def hashEx : Expr → UInt64 := hash
608:@[export lean_expr_has_fvar] def hasFVarEx : Expr → Bool := hasFVar
609:@[export lean_expr_has_expr_mvar] def hasExprMVarEx : Expr → Bool := hasExprMVar
610:@[export lean_expr_has_level_mvar] def hasLevelMVarEx : Expr → Bool := hasLevelMVar
611:@[export lean_expr_has_mvar] def hasMVarEx : Expr → Bool := hasMVar
612:@[export lean_expr_has_level_param] def hasLevelParamEx : Expr → Bool := hasLevelParam
613:@[export lean_expr_loose_bvar_range] def looseBVarRangeEx (e : Expr) : UInt32 := e.data.looseBVarRange
614:@[export lean_expr_binder_info] def binderInfoEx : Expr → BinderInfo := binderInfo
627:@[export lean_lit_type]
746:@[export lean_expr_mk_bvar] def mkBVarEx : Nat → Expr := mkBVar
747:@[export lean_expr_mk_fvar] def mkFVarEx : FVarId → Expr := mkFVar
748:@[export lean_expr_mk_mvar] def mkMVarEx : MVarId → Expr := mkMVar
749:@[export lean_expr_mk_sort] def mkSortEx : Level → Expr := mkSort
750:@[export lean_expr_mk_const] def mkConstEx (c : Name) (lvls : List Level) : Expr := mkConst c lvls
751:@[export lean_expr_mk_app] def mkAppEx : Expr → Expr → Expr := mkApp
752:@[export lean_expr_mk_lambda] def mkLambdaEx (n : Name) (d b : Expr) (bi : BinderInfo) : Expr := mkLambda n bi d b
753:@[export lean_expr_mk_forall] def mkForallEx (n : Name) (d b : Expr) (bi : BinderInfo) : Expr := mkForall n bi d b
754:@[export lean_expr_mk_let] def mkLetEx (n : Name) (t v b : Expr) (nondep : Bool) : Expr := mkLet n t v b nondep
755:@[export lean_expr_mk_lit] def mkLitEx : Literal → Expr := mkLit
756:@[export lean_expr_mk_mdata] def mkMDataEx : MData → Expr → Expr := mkMData
757:@[export lean_expr_mk_proj] def mkProjEx : Name → Nat → Expr → Expr := mkProj
908:@[export lean_expr_is_have] def isHaveEx : Expr → Bool := isHave
1699:@[export lean_is_out_param]
1729:@[export lean_expr_consume_type_annotations]

src/Lean/ImportingFlag.lean
30:@[export lean_enable_initializer_execution]

src/Lean/Level.lean
125:@[export lean_level_hash] def hashEx (u : Level) : UInt32 := hash u |>.toUInt32
126:@[export lean_level_has_mvar] def hasMVarEx : Level → Bool := hasMVar
127:@[export lean_level_has_param] def hasParamEx : Level → Bool := hasParam
128:@[export lean_level_depth] def depthEx (u : Level) : UInt32 := u.data.depth
155:@[export lean_level_mk_zero] def mkLevelZeroEx : Unit → Level := fun _ => .zero
156:@[export lean_level_mk_succ] def mkLevelSuccEx : Level → Level := mkLevelSucc
157:@[export lean_level_mk_mvar] def mkLevelMVarEx : LMVarId → Level := mkLevelMVar
158:@[export lean_level_mk_param] def mkLevelParamEx : Name → Level := mkLevelParam
159:@[export lean_level_mk_max] def mkLevelMaxEx : Level → Level → Level := mkLevelMax
160:@[export lean_level_mk_imax] def mkLevelIMaxEx : Level → Level → Level := mkLevelIMax

src/Lean/LoadDynlib.lean
66:@[export lean_load_dynlib]
94:@[export lean_load_plugin]

src/Lean/LocalContext.lean
89:@[export lean_mk_local_decl]
92:@[export lean_mk_let_decl]
95:@[export lean_local_decl_binder_info]
273:@[export lean_mk_empty_local_ctx]
278:@[export lean_local_ctx_is_empty]
294:@[export lean_local_ctx_mk_local_decl]
306:@[export lean_local_ctx_mk_let_decl]
330:@[export lean_local_ctx_find]
370:@[export lean_local_ctx_erase]
482:@[export lean_local_ctx_num_indices]

src/Lean/Meta/ExprDefEq.lean
1164:@[export lean_checked_assign]
2271:@[export lean_is_expr_def_eq]

src/Lean/Meta/InferType.lean
235:@[export lean_infer_type]

src/Lean/Meta/LevelDefEq.lean
144:  @[export lean_is_level_def_eq]

src/Lean/Meta/Match/MatchEqs.lean
142:@[export lean_get_match_equations_for]
262:@[export lean_get_congr_match_equations_for]

src/Lean/Meta/Match/MatcherInfo.lean
162:@[export lean_is_matcher]

src/Lean/Meta/Match/MatchPatternAttr.lean
41:@[export lean_has_match_pattern_attribute]

src/Lean/Meta/Sym/DSimp/Main.lean
37:@[export lean_sym_dsimp]

src/Lean/Meta/Sym/Pattern.lean
883:@[export lean_sym_def_eq]

src/Lean/Meta/Sym/Simp/Main.lean
44:@[export lean_sym_simp]

src/Lean/Meta/SynthInstance.lean
948:@[export lean_synth_pending]

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/EqCnstr.lean
280:@[export lean_cutsat_propagate_nonlinear]
343:@[export lean_grind_cutsat_assert_eq]

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/LeCnstr.lean
103:@[export lean_grind_cutsat_assert_le]

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean
331:@[export lean_cutsat_eq_cnstr_to_proof]

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Var.lean
68:@[export lean_grind_cutsat_mk_var]

src/Lean/Meta/Tactic/Grind/Core.lean
364:@[export lean_grind_process_new_facts]

src/Lean/Meta/Tactic/Grind/Internalize.lean
539:@[export lean_grind_internalize]

src/Lean/Meta/Tactic/Grind/Proof.lean
336:@[export lean_grind_mk_eq_proof]
343:@[export lean_grind_mk_heq_proof]

src/Lean/Meta/Tactic/Grind/Simp.lean
50:@[export lean_grind_preprocess]

src/Lean/Meta/Tactic/Grind/SimpUtil.lean
206:@[export lean_grind_normalize]

src/Lean/Meta/Tactic/Simp/Main.lean
516:@[export lean_dsimp]
715:@[export lean_simp]

src/Lean/MetavarContext.lean
398:@[export lean_get_lmvar_assignment]
405:@[export lean_get_mvar_assignment]
415:@[export lean_get_delayed_mvar_assignment]
419:@[export lean_delayed_mvar_assignment_fvars]
422:@[export lean_delayed_mvar_assignment_mvar_id_pending]
522:@[export lean_assign_lmvar]
535:@[export lean_assign_mvar]

src/Lean/Meta/WHNF.lean
1103:@[export lean_whnf]

src/Lean/Parser.lean
70:@[export lean_mk_antiquot_parenthesizer]
85:@[export lean_pretty_printer_parenthesizer_interpret_parser_descr]
107:@[export lean_mk_antiquot_formatter]
120:@[export lean_pretty_printer_formatter_interpret_parser_descr]

src/Lean/PrivateName.lean
37:@[export lean_is_private_name]
62:@[export lean_private_to_user_name]
75:@[export lean_private_prefix]

src/Lean/ProjFns.lean
30:@[export lean_mk_projection_info]
33:@[export lean_projection_info_from_class]

src/Lean/ReducibilityAttrs.lean
73:@[export lean_get_reducibility_status]
98:@[export lean_set_reducibility_status]

src/Lean/ResolveName.lean
51:@[export lean_is_reserved_name]
75:@[export lean_add_alias] def addAlias (env : Environment) (a : Name) (e : Name) : Environment :=

src/Lean/Shell.lean
252:@[export lean_shell_options_mk]
255:@[export lean_shell_options_get_run]
259:@[export lean_shell_options_get_profiler]
263:@[export lean_shell_options_get_num_threads]
292:@[export lean_shell_options_process]
449:@[export lean_shell_main]

src/Lean/Util/Path.lean
112:@[export lean_init_search_path]

src/Lean/Util/Profile.lean
28:@[export lean_get_profiler]
32:@[export lean_get_profiler_threshold]

src/Lean/Util/Trace.lean
121:@[export lean_is_trace_class_enabled]
```
