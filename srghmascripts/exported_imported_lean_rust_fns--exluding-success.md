Scanning Lean codebase under: /home/srghma/projects/lean4/src...
Processed 135 Lean files with symbols (2429 total Lean files) and indexed 107 Rust files.

# List of all functions that lean imports from rust

src/Init/Prelude.lean
  Line 2429: [extern "lean_uint8_of_nat_mk"] UInt8.ofBitVec <- src/rust/leanh/src/in_emit_rust.rs:732 (lean_uint8_of_nat_mk,) 🔍 (Referenced in Rust)
  Line 2430: [extern "lean_uint8_to_nat"] UInt8.toBitVec <- src/rust/leanh/src/in_emit_rust.rs:733 (lean_uint8_to_nat,) 🔍 (Referenced in Rust)
  Line 2547: [extern "lean_uint16_of_nat_mk"] UInt16.ofBitVec <- src/rust/leanh/src/in_emit_rust.rs:742 (lean_uint16_of_nat_mk,) 🔍 (Referenced in Rust)
  Line 2548: [extern "lean_uint16_to_nat"] UInt16.toBitVec <- src/rust/leanh/src/in_emit_rust.rs:743 (lean_uint16_to_nat,) 🔍 (Referenced in Rust)
  Line 2605: [extern "lean_uint32_of_nat_mk"] UInt32.ofBitVec <- src/rust/leanh/src/in_emit_rust.rs:752 (lean_uint32_of_nat_mk,) 🔍 (Referenced in Rust)
  Line 2606: [extern "lean_uint32_to_nat"] UInt32.toBitVec <- src/rust/leanh/src/in_emit_rust.rs:753 (lean_uint32_to_nat,) 🔍 (Referenced in Rust)
  Line 2710: [extern "lean_uint64_of_nat_mk"] UInt64.ofBitVec <- src/rust/leanh/src/in_emit_rust.rs:762 (lean_uint64_of_nat_mk,) 🔍 (Referenced in Rust)
  Line 2711: [extern "lean_uint64_to_nat"] UInt64.toBitVec <- src/rust/leanh/src/in_emit_rust.rs:763 (lean_uint64_to_nat,) 🔍 (Referenced in Rust)
  Line 2781: [extern "lean_usize_of_nat_mk"] USize.ofBitVec <- ❌ (Rust does not define this function)
  Line 2782: [extern "lean_usize_to_nat"] USize.toBitVec <- src/rust/runtime/src/runtime_object_string.rs:85 (unsafe fn lean_usize_to_nat(n: usize) -> *mut LeanObject {) ✅
  Line 3189: [extern "lean_array_to_list"] Array.toList <- src/rust/runtime/src/runtime_object_array.rs:260 (pub unsafe fn lean_array_to_list(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 3190: [extern "lean_array_mk"] Array.mk <- src/rust/runtime/src/runtime_object_array.rs:240 (pub unsafe fn lean_array_mk(lst: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 3402: [extern "lean_byte_array_mk"] ByteArray.mk <- src/rust/runtime/src/runtime_object_array.rs:114 (pub unsafe fn lean_byte_array_mk(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 3403: [extern "lean_byte_array_data"] ByteArray.data <- src/rust/runtime/src/runtime_object_array.rs:126 (pub unsafe fn lean_byte_array_data(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 3512: [extern "lean_string_to_utf8"] String.toByteArray <- src/rust/runtime/src/runtime_object_string.rs:228 (pub unsafe fn lean_string_to_utf8(s: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 3513: [extern "lean_string_from_utf8_unchecked"] String.ofByteArray <- src/rust/runtime/src/runtime_object_string.rs:213 (pub unsafe fn lean_string_from_utf8_unchecked(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 116: [extern "lean_is_scalar"] isScalarObj <- src/rust/leanh/src/in_emit_rust.rs:499 (pub fn lean_is_scalar(obj: *mut LeanObject) -> u8 {) ✅
  Line 744: [extern "lean_sorry"] sorryAx <- src/rust/runtime/src/runtime_object_panic.rs:65 (pub unsafe fn lean_sorry(_: u8) -> *mut LeanObject {) ✅
  Line 1755: [extern "lean_nat_add"] Nat.add <- src/rust/runtime/src/runtime_object_string.rs:95 (unsafe fn lean_nat_add(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1774: [extern "lean_nat_mul"] Nat.mul <- src/rust/runtime/src/kernel_type_checker.rs:694 (pub unsafe fn lean_nat_mul(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1789: [extern "lean_nat_pow"] Nat.pow <- src/rust/runtime/src/runtime_object_nat_int.rs:449 (pub unsafe fn lean_nat_pow(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1803: [extern "lean_nat_dec_eq"] Nat.beq <- ❌ (Rust does not define this function)
  Line 1853: [extern "lean_nat_dec_eq"] Nat.decEq <- ❌ (Rust does not define this function)
  Line 1873: [extern "lean_nat_dec_le"] Nat.ble <- ❌ (Rust does not define this function)
  Line 1957: [extern "lean_nat_pred"] Nat.pred <- ❌ (Rust does not define this function)
  Line 2070: [extern "lean_nat_dec_le"] Nat.decLe <- ❌ (Rust does not define this function)
  Line 2084: [extern "lean_nat_dec_lt"] Nat.decLt <- ❌ (Rust does not define this function)
  Line 2105: [extern "lean_nat_sub"] Nat.sub <- src/rust/runtime/src/runtime_object_string.rs:104 (unsafe fn lean_nat_sub(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 2164: [extern "lean_nat_div"] Nat.div <- src/rust/runtime/src/kernel_type_checker.rs:713 (pub unsafe fn lean_nat_div(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 2194: [extern "lean_nat_mod"] Nat.modCore <- src/rust/runtime/src/kernel_type_checker.rs:724 (pub unsafe fn lean_nat_mod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 2252: [extern "lean_nat_mod"] Nat.mod <- src/rust/runtime/src/kernel_type_checker.rs:724 (pub unsafe fn lean_nat_mod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 2284: [extern "lean_system_platform_nbits"] System.Platform.getNumBits <- src/rust/runtime/src/base.rs:1002 (pub unsafe fn lean_system_platform_nbits(_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 2438: [extern "lean_uint8_of_nat"] UInt8.ofNatLT <- src/rust/leanh/src/in_emit_rust.rs:731 (lean_uint8_of_nat,) 🔍 (Referenced in Rust)
  Line 2454: [extern "lean_uint8_of_nat"] UInt8.ofNat <- src/rust/leanh/src/in_emit_rust.rs:731 (lean_uint8_of_nat,) 🔍 (Referenced in Rust)
  Line 2469: [extern "lean_uint8_dec_eq"] UInt8.decEq <- src/rust/leanh/src/in_emit_rust.rs:734 (lean_uint8_dec_eq,) 🔍 (Referenced in Rust)
  Line 2506: [extern "lean_uint8_dec_lt"] UInt8.decLt <- src/rust/leanh/src/in_emit_rust.rs:735 (lean_uint8_dec_lt,) 🔍 (Referenced in Rust)
  Line 2522: [extern "lean_uint8_dec_le"] UInt8.decLe <- src/rust/leanh/src/in_emit_rust.rs:736 (lean_uint8_dec_le) 🔍 (Referenced in Rust)
  Line 2556: [extern "lean_uint16_of_nat"] UInt16.ofNatLT <- src/rust/leanh/src/in_emit_rust.rs:741 (lean_uint16_of_nat,) 🔍 (Referenced in Rust)
  Line 2573: [extern "lean_uint16_dec_eq"] UInt16.decEq <- src/rust/leanh/src/in_emit_rust.rs:744 (lean_uint16_dec_eq,) 🔍 (Referenced in Rust)
  Line 2614: [extern "lean_uint32_of_nat"] UInt32.ofNatLT <- src/rust/leanh/src/in_emit_rust.rs:751 (lean_uint32_of_nat,) 🔍 (Referenced in Rust)
  Line 2623: [extern "lean_uint32_to_nat"] UInt32.toNat <- src/rust/leanh/src/in_emit_rust.rs:753 (lean_uint32_to_nat,) 🔍 (Referenced in Rust)
  Line 2638: [extern "lean_uint32_dec_eq"] UInt32.decEq <- src/rust/leanh/src/in_emit_rust.rs:754 (lean_uint32_dec_eq,) 🔍 (Referenced in Rust)
  Line 2666: [extern "lean_uint32_dec_lt"] UInt32.decLt <- src/rust/leanh/src/in_emit_rust.rs:755 (lean_uint32_dec_lt,) 🔍 (Referenced in Rust)
  Line 2682: [extern "lean_uint32_dec_le"] UInt32.decLe <- src/rust/leanh/src/in_emit_rust.rs:756 (lean_uint32_dec_le) 🔍 (Referenced in Rust)
  Line 2719: [extern "lean_uint64_of_nat"] UInt64.ofNatLT <- src/rust/runtime/src/library_ir_interpreter.rs:345 (unsafe fn lean_uint64_of_nat(a: *mut LeanObject) -> u64 {) ✅
  Line 2736: [extern "lean_uint64_dec_eq"] UInt64.decEq <- src/rust/leanh/src/in_emit_rust.rs:764 (lean_uint64_dec_eq,) 🔍 (Referenced in Rust)
  Line 2790: [extern "lean_usize_of_nat"] USize.ofNatLT <- src/rust/runtime/src/library_ir_interpreter.rs:354 (unsafe fn lean_usize_of_nat(a: *mut LeanObject) -> usize {) ✅
  Line 2806: [extern "lean_usize_dec_eq"] USize.decEq <- ❌ (Rust does not define this function)
  Line 2853: [extern "lean_uint32_of_nat"] Char.ofNatAux <- src/rust/leanh/src/in_emit_rust.rs:751 (lean_uint32_of_nat,) 🔍 (Referenced in Rust)
  Line 3210: [extern "lean_mk_empty_array_with_capacity"] Array.mkEmpty <- ❌ (Rust does not define this function)
  Line 3217: [extern "lean_mk_empty_array_with_capacity"] Array.emptyWithCapacity <- ❌ (Rust does not define this function)
  Line 3236: [extern "lean_array_get_size"] Array.size <- ❌ (Rust does not define this function)
  Line 3245: [extern "lean_array_fget_borrowed"] Array.getInternalBorrowed <- ❌ (Rust does not define this function)
  Line 3259: [extern "lean_array_fget"] Array.getInternal <- ❌ (Rust does not define this function)
  Line 3283: [extern "lean_array_get_borrowed"] Array.get <- ❌ (Rust does not define this function)
  Line 3291: [extern "lean_array_get"] Array.get <- src/rust/runtime/src/base.rs:132 (pub(crate) unsafe fn lean_array_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {) ✅
  Line 3305: [extern "lean_array_push"] Array.push <- src/rust/runtime/src/runtime_object_array.rs:345 (pub unsafe fn lean_array_push(a: *mut LeanObject, v: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 3408: [extern "lean_mk_empty_byte_array"] ByteArray.emptyWithCapacity <- ❌ (Rust does not define this function)
  Line 3425: [extern "lean_byte_array_push"] ByteArray.push <- src/rust/runtime/src/runtime_object_array.rs:138 (pub unsafe fn lean_byte_array_push(a: *mut LeanObject, b: u8) -> *mut LeanObject {) ✅
  Line 3444: [extern "lean_byte_array_size"] ByteArray.size <- ❌ (Rust does not define this function)
  Line 3523: [extern "lean_string_mk"] String.ofList <- src/rust/runtime/src/runtime_object_string.rs:645 (pub unsafe fn lean_string_mk(cs: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 3533: [extern "lean_string_dec_eq"] String.decEq <- ❌ (Rust does not define this function)
  Line 3603: [extern "lean_string_utf8_byte_size"] String.utf8ByteSize <- ❌ (Rust does not define this function)
  Line 3671: [extern "lean_panic_fn_borrowed"] panicCore <- src/rust/runtime/src/runtime_object_panic.rs:57 (pub unsafe fn lean_panic_fn_borrowed() ✅
  Line 4643: [extern "lean_uint64_mix_hash"] mixHash <- src/rust/runtime/src/runtime_object_nat_int.rs:854 (pub unsafe fn lean_uint64_mix_hash(a1: u64, a2: u64) -> u64 {) ✅
  Line 4652: [extern "lean_string_hash"] String.hash <- src/rust/runtime/src/runtime_object_string.rs:589 (pub unsafe fn lean_string_hash(s: *mut LeanObject) -> u64 {) ✅
  Line 4781: [extern "lean_name_eq"] beq <- src/rust/leanh/src/runtime_object_name.rs:22 (pub(crate) unsafe fn lean_name_eq(mut n1: *mut LeanObject, mut n2: *mut LeanObject) -> u8 {) ✅

src/Lean/Runtime.lean
  Line 15: [extern "lean_closure_max_args"] closureMaxArgsFn <- src/rust/runtime/src/runtime_debug.rs:130 (pub unsafe fn lean_closure_max_args(_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 18: [extern "lean_max_small_nat"] maxSmallNatFn <- src/rust/runtime/src/runtime_debug.rs:134 (pub unsafe fn lean_max_small_nat(_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 21: [extern "lean_libuv_version"] libUVVersionFn <- src/rust/runtime/src/runtime_libuv.rs:25 (pub unsafe fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject {) ✅

src/Init/Data/Array/Set.lean
  Line 29: [extern "lean_array_fset"] Array.set <- ❌ (Rust does not define this function)
  Line 54: [extern "lean_array_set"] Array.set <- src/rust/runtime/src/runtime_system.rs:61 (unsafe fn lean_array_set(obj: *mut LeanObject, idx: usize, value: *mut LeanObject) {) ✅

src/Init/Core.lean
  Line 130: [extern "lean_mk_thunk"] Thunk.mk <- ❌ (Rust does not define this function)
  Line 646: [extern "lean_task_pure"] Task.pure <- src/rust/runtime/src/runtime_object_task.rs:132 (pub unsafe fn lean_task_pure(value: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 647: [extern "lean_task_get_own"] Task.get <- src/rust/runtime/src/runtime_object_task.rs:434 (unsafe fn lean_task_get_own(t: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 137: [extern "lean_thunk_pure"] Thunk.pure <- ❌ (Rust does not define this function)
  Line 147: [extern "lean_thunk_get_own"] Thunk.get <- ❌ (Rust does not define this function)
  Line 686: [extern "lean_task_spawn"] spawn <- ❌ (Rust does not define this function)
  Line 701: [extern "lean_task_map"] map <- ❌ (Rust does not define this function)
  Line 717: [extern "lean_task_bind"] bind <- ❌ (Rust does not define this function)
  Line 757: [extern "lean_strict_or"] strictOr <- ❌ (Rust does not define this function)
  Line 763: [extern "lean_strict_and"] strictAnd <- ❌ (Rust does not define this function)

src/Init/Data/Nat/Div/Basic.lean
  Line 109: [extern "lean_nat_div_exact"] divExact <- ❌ (Rust does not define this function)

src/Init/Data/Nat/Bitwise/Basic.lean
  Line 49: [extern "lean_nat_land"] land <- src/rust/runtime/src/kernel_type_checker.rs:736 (pub unsafe fn lean_nat_land(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 57: [extern "lean_nat_lor"] lor <- src/rust/runtime/src/kernel_type_checker.rs:745 (pub unsafe fn lean_nat_lor(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 65: [extern "lean_nat_lxor"] xor <- ❌ (Rust does not define this function)
  Line 78: [extern "lean_nat_shiftl"] shiftLeft <- src/rust/runtime/src/runtime_object_nat_int.rs:408 (pub unsafe fn lean_nat_shiftl(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 94: [extern "lean_nat_shiftr"] shiftRight <- src/rust/runtime/src/kernel_type_checker.rs:764 (pub unsafe fn lean_nat_shiftr(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {) ✅

src/Init/Data/UInt/BasicAux.lean
  Line 66: [extern "lean_uint8_to_nat"] UInt8.toNat <- src/rust/leanh/src/in_emit_rust.rs:733 (lean_uint8_to_nat,) 🔍 (Referenced in Rust)
  Line 85: [extern "lean_uint16_of_nat"] UInt16.ofNat <- src/rust/leanh/src/in_emit_rust.rs:741 (lean_uint16_of_nat,) 🔍 (Referenced in Rust)
  Line 121: [extern "lean_uint16_to_nat"] UInt16.toNat <- src/rust/leanh/src/in_emit_rust.rs:743 (lean_uint16_to_nat,) 🔍 (Referenced in Rust)
  Line 128: [extern "lean_uint16_to_uint8"] UInt16.toUInt8 <- ❌ (Rust does not define this function)
  Line 135: [extern "lean_uint8_to_uint16"] UInt8.toUInt16 <- ❌ (Rust does not define this function)
  Line 153: [extern "lean_uint32_of_nat"] UInt32.ofNat <- src/rust/leanh/src/in_emit_rust.rs:751 (lean_uint32_of_nat,) 🔍 (Referenced in Rust)
  Line 188: [extern "lean_uint32_to_uint8"] UInt32.toUInt8 <- ❌ (Rust does not define this function)
  Line 195: [extern "lean_uint32_to_uint16"] UInt32.toUInt16 <- ❌ (Rust does not define this function)
  Line 202: [extern "lean_uint8_to_uint32"] UInt8.toUInt32 <- ❌ (Rust does not define this function)
  Line 209: [extern "lean_uint16_to_uint32"] UInt16.toUInt32 <- ❌ (Rust does not define this function)
  Line 231: [extern "lean_uint32_add"] UInt32.add <- ❌ (Rust does not define this function)
  Line 240: [extern "lean_uint32_sub"] UInt32.sub <- ❌ (Rust does not define this function)
  Line 260: [extern "lean_uint64_of_nat"] UInt64.ofNat <- src/rust/runtime/src/library_ir_interpreter.rs:345 (unsafe fn lean_uint64_of_nat(a: *mut LeanObject) -> u64 {) ✅
  Line 294: [extern "lean_uint64_to_nat"] UInt64.toNat <- src/rust/leanh/src/in_emit_rust.rs:763 (lean_uint64_to_nat,) 🔍 (Referenced in Rust)
  Line 301: [extern "lean_uint64_to_uint8"] UInt64.toUInt8 <- ❌ (Rust does not define this function)
  Line 308: [extern "lean_uint64_to_uint16"] UInt64.toUInt16 <- ❌ (Rust does not define this function)
  Line 315: [extern "lean_uint64_to_uint32"] UInt64.toUInt32 <- ❌ (Rust does not define this function)
  Line 322: [extern "lean_uint8_to_uint64"] UInt8.toUInt64 <- ❌ (Rust does not define this function)
  Line 329: [extern "lean_uint16_to_uint64"] UInt16.toUInt64 <- ❌ (Rust does not define this function)
  Line 336: [extern "lean_uint32_to_uint64"] UInt32.toUInt64 <- ❌ (Rust does not define this function)
  Line 350: [extern "lean_usize_of_nat"] USize.ofNat <- src/rust/runtime/src/library_ir_interpreter.rs:354 (unsafe fn lean_usize_of_nat(a: *mut LeanObject) -> usize {) ✅
  Line 374: [extern "lean_usize_to_nat"] USize.toNat <- src/rust/runtime/src/runtime_object_string.rs:85 (unsafe fn lean_usize_to_nat(n: usize) -> *mut LeanObject {) ✅
  Line 382: [extern "lean_usize_add"] USize.add <- ❌ (Rust does not define this function)
  Line 390: [extern "lean_usize_sub"] USize.sub <- ❌ (Rust does not define this function)
  Line 422: [extern "lean_usize_dec_lt"] USize.decLt <- ❌ (Rust does not define this function)
  Line 438: [extern "lean_usize_dec_le"] USize.decLe <- ❌ (Rust does not define this function)

src/Init/Data/Int/Basic.lean
  Line 60: [extern "lean_nat_to_int"] Int.ofNat <- ❌ (Rust does not define this function)
  Line 61: [extern "lean_int_neg_succ_of_nat"] Int.negSucc <- ❌ (Rust does not define this function)
  Line 118: [extern "lean_int_neg"] neg <- ❌ (Rust does not define this function)
  Line 160: [extern "lean_int_add"] add <- ❌ (Rust does not define this function)
  Line 183: [extern "lean_int_mul"] mul <- ❌ (Rust does not define this function)
  Line 206: [extern "lean_int_sub"] sub <- ❌ (Rust does not define this function)
  Line 253: [extern "lean_int_dec_eq"] decEq <- ❌ (Rust does not define this function)
  Line 278: [extern "lean_int_dec_nonneg"] decNonneg <- ❌ (Rust does not define this function)
  Line 297: [extern "lean_int_dec_le"] decLe <- ❌ (Rust does not define this function)
  Line 310: [extern "lean_int_dec_lt"] decLt <- ❌ (Rust does not define this function)
  Line 326: [extern "lean_nat_abs"] natAbs <- ❌ (Rust does not define this function)

src/Init/Data/Int/DivMod/Basic.lean
  Line 72: [extern "lean_int_ediv"] ediv <- ❌ (Rust does not define this function)
  Line 102: [extern "lean_int_emod"] emod <- ❌ (Rust does not define this function)
  Line 145: [extern "lean_int_div_exact"] divExact <- ❌ (Rust does not define this function)
  Line 177: [extern "lean_int_div"] tdiv <- ❌ (Rust does not define this function)
  Line 210: [extern "lean_int_mod"] tmod <- ❌ (Rust does not define this function)

src/Init/Data/String/Bootstrap.lean
  Line 32: [extern "lean_string_push"] push <- src/rust/runtime/src/runtime_object_string.rs:243 (pub unsafe fn lean_string_push(s: *mut LeanObject, c: u32) -> *mut LeanObject {) ✅
  Line 59: [extern "lean_string_posof"] posOf <- ❌ (Rust does not define this function)
  Line 63: [extern "lean_string_offsetofpos"] offsetOfPos <- ❌ (Rust does not define this function)
  Line 66: [extern "lean_string_utf8_extract"] extract <- src/rust/runtime/src/runtime_object_string.rs:476 (pub unsafe fn lean_string_utf8_extract() ✅
  Line 69: [extern "lean_string_length"] length <- ❌ (Rust does not define this function)
  Line 73: [extern "lean_string_pushn"] pushn <- ❌ (Rust does not define this function)
  Line 76: [extern "lean_string_append"] append <- src/rust/runtime/src/runtime_object_string.rs:261 (pub unsafe fn lean_string_append(s1: *mut LeanObject, s2: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 79: [extern "lean_string_utf8_next"] next <- src/rust/runtime/src/runtime_object_string.rs:418 (pub unsafe fn lean_string_utf8_next() ✅
  Line 83: [extern "lean_string_isempty"] isEmpty <- ❌ (Rust does not define this function)
  Line 87: [extern "lean_string_foldl"] foldl <- ❌ (Rust does not define this function)
  Line 91: [extern "lean_string_isprefixof"] isPrefixOf <- ❌ (Rust does not define this function)
  Line 95: [extern "lean_string_any"] any <- ❌ (Rust does not define this function)
  Line 99: [extern "lean_string_contains"] contains <- ❌ (Rust does not define this function)
  Line 102: [extern "lean_string_utf8_get"] get <- src/rust/runtime/src/runtime_object_string.rs:328 (pub unsafe fn lean_string_utf8_get(s: *mut LeanObject, i0: *mut LeanObject) -> u32 {) ✅
  Line 106: [extern "lean_string_capitalize"] capitalize <- ❌ (Rust does not define this function)
  Line 109: [extern "lean_string_utf8_at_end"] atEnd <- ❌ (Rust does not define this function)
  Line 113: [extern "lean_string_nextwhile"] nextWhile <- ❌ (Rust does not define this function)
  Line 117: [extern "lean_string_trim"] trim <- ❌ (Rust does not define this function)
  Line 121: [extern "lean_string_intercalate"] intercalate <- ❌ (Rust does not define this function)
  Line 125: [extern "lean_string_front"] front <- ❌ (Rust does not define this function)
  Line 129: [extern "lean_string_drop"] drop <- ❌ (Rust does not define this function)
  Line 133: [extern "lean_string_dropright"] dropRight <- ❌ (Rust does not define this function)
  Line 136: [extern "lean_string_get_byte_fast"] getUTF8Byte <- ❌ (Rust does not define this function)
  Line 141: [extern "lean_string_mk"] String.mk <- src/rust/runtime/src/runtime_object_string.rs:645 (pub unsafe fn lean_string_mk(cs: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 160: [extern "lean_substring_tostring"] toString <- ❌ (Rust does not define this function)
  Line 164: [extern "lean_substring_drop"] drop <- ❌ (Rust does not define this function)
  Line 168: [extern "lean_substring_front"] front <- ❌ (Rust does not define this function)
  Line 172: [extern "lean_substring_takewhile"] takeWhile <- ❌ (Rust does not define this function)
  Line 176: [extern "lean_substring_extract"] extract <- ❌ (Rust does not define this function)
  Line 180: [extern "lean_substring_all"] all <- ❌ (Rust does not define this function)
  Line 184: [extern "lean_substring_beq"] beq <- ❌ (Rust does not define this function)
  Line 188: [extern "lean_substring_isempty"] isEmpty <- ❌ (Rust does not define this function)
  Line 192: [extern "lean_substring_get"] get <- ❌ (Rust does not define this function)
  Line 196: [extern "lean_substring_prev"] prev <- ❌ (Rust does not define this function)
  Line 204: [extern "lean_string_pos_sub"] sub <- ❌ (Rust does not define this function)
  Line 208: [extern "lean_string_pos_min"] min <- ❌ (Rust does not define this function)

src/Init/System/Platform.lean
  Line 22: [extern "lean_system_platform_windows"] getIsWindows <- src/rust/runtime/src/base.rs:1006 (pub fn lean_system_platform_windows(_: *mut LeanObject) -> u8 {) ✅
  Line 26: [extern "lean_system_platform_osx"] getIsOSX <- src/rust/runtime/src/base.rs:1010 (pub fn lean_system_platform_osx(_: *mut LeanObject) -> u8 {) ✅
  Line 30: [extern "lean_system_platform_emscripten"] getIsEmscripten <- src/rust/runtime/src/base.rs:1014 (pub fn lean_system_platform_emscripten(_: *mut LeanObject) -> u8 {) ✅
  Line 51: [extern "lean_system_platform_target"] getTarget <- ❌ (Rust does not define this function)

src/Init/Data/Repr.lean
  Line 230: [extern "lean_string_of_usize"] _root_.USize.repr <- src/rust/runtime/src/runtime_object_string.rs:610 (pub unsafe fn lean_string_of_usize(n: usize) -> *mut LeanObject {) ✅

src/Init/Data/Float.lean
  Line 58: [extern "lean_float_add"] Float.add <- ❌ (Rust does not define this function)
  Line 64: [extern "lean_float_sub"] Float.sub <- ❌ (Rust does not define this function)
  Line 70: [extern "lean_float_mul"] Float.mul <- ❌ (Rust does not define this function)
  Line 79: [extern "lean_float_div"] Float.div <- ❌ (Rust does not define this function)
  Line 86: [extern "lean_float_negate"] Float.neg <- ❌ (Rust does not define this function)
  Line 111: [extern "lean_float_of_bits"] Float.ofBits <- src/rust/runtime/src/runtime_float.rs:84 (pub fn lean_float_of_bits(bits: u64) -> f64 {) ✅
  Line 123: [extern "lean_float_to_bits"] Float.toBits <- src/rust/runtime/src/runtime_float.rs:89 (pub fn lean_float_to_bits(mut value: f64) -> u64 {) ✅
  Line 142: [extern "lean_float_beq"] Float.beq <- ❌ (Rust does not define this function)
  Line 151: [extern "lean_float_decLt"] Float.decLt <- ❌ (Rust does not define this function)
  Line 160: [extern "lean_float_decLe"] Float.decLe <- ❌ (Rust does not define this function)
  Line 171: [extern "lean_float_to_string"] Float.toString <- src/rust/runtime/src/runtime_float.rs:54 (pub fn lean_float_to_string(value: f64) -> *mut LeanObject {) ✅
  Line 182: [extern "lean_float_to_uint8"] Float.toUInt8 <- ❌ (Rust does not define this function)
  Line 192: [extern "lean_float_to_uint16"] Float.toUInt16 <- ❌ (Rust does not define this function)
  Line 202: [extern "lean_float_to_uint32"] Float.toUInt32 <- ❌ (Rust does not define this function)
  Line 212: [extern "lean_float_to_uint64"] Float.toUInt64 <- ❌ (Rust does not define this function)
  Line 222: [extern "lean_float_to_usize"] Float.toUSize <- ❌ (Rust does not define this function)
  Line 231: [extern "lean_float_isnan"] Float.isNaN <- src/rust/runtime/src/runtime_float.rs:72 (pub fn lean_float_isnan(value: f64) -> u8 {) ✅
  Line 239: [extern "lean_float_isfinite"] Float.isFinite <- src/rust/runtime/src/runtime_float.rs:76 (pub fn lean_float_isfinite(value: f64) -> u8 {) ✅
  Line 247: [extern "lean_float_isinf"] Float.isInf <- src/rust/runtime/src/runtime_float.rs:80 (pub fn lean_float_isinf(value: f64) -> u8 {) ✅
  Line 256: [extern "lean_float_frexp"] Float.frExp <- src/rust/runtime/src/runtime_float.rs:96 (pub unsafe fn lean_float_frexp(value: f64) -> *mut LeanObject {) ✅
  Line 262: [extern "lean_uint8_to_float"] UInt8.toFloat <- ❌ (Rust does not define this function)
  Line 264: [extern "lean_uint16_to_float"] UInt16.toFloat <- ❌ (Rust does not define this function)
  Line 266: [extern "lean_uint32_to_float"] UInt32.toFloat <- ❌ (Rust does not define this function)
  Line 277: [extern "lean_uint64_to_float"] UInt64.toFloat <- ❌ (Rust does not define this function)
  Line 288: [extern "lean_usize_to_float"] USize.toFloat <- ❌ (Rust does not define this function)
  Line 307: [extern "sin"] Float.sin <- ❌ (Rust does not define this function)
  Line 314: [extern "cos"] Float.cos <- ❌ (Rust does not define this function)
  Line 321: [extern "tan"] Float.tan <- ❌ (Rust does not define this function)
  Line 328: [extern "asin"] Float.asin <- ❌ (Rust does not define this function)
  Line 335: [extern "acos"] Float.acos <- ❌ (Rust does not define this function)
  Line 342: [extern "atan"] Float.atan <- ❌ (Rust does not define this function)
  Line 350: [extern "atan2"] Float.atan2 <- ❌ (Rust does not define this function)
  Line 357: [extern "sinh"] Float.sinh <- ❌ (Rust does not define this function)
  Line 364: [extern "cosh"] Float.cosh <- ❌ (Rust does not define this function)
  Line 371: [extern "tanh"] Float.tanh <- ❌ (Rust does not define this function)
  Line 378: [extern "asinh"] Float.asinh <- ❌ (Rust does not define this function)
  Line 385: [extern "acosh"] Float.acosh <- ❌ (Rust does not define this function)
  Line 392: [extern "atanh"] Float.atanh <- ❌ (Rust does not define this function)
  Line 399: [extern "exp"] Float.exp <- src/rust/runtime/src/runtime_object_nat_int.rs:453 (let exp = lean_unbox(a2) as c_ulong;) 🔍 (Referenced in Rust)
  Line 406: [extern "exp2"] Float.exp2 <- ❌ (Rust does not define this function)
  Line 413: [extern "log"] Float.log <- ❌ (Rust does not define this function)
  Line 420: [extern "log2"] Float.log2 <- ❌ (Rust does not define this function)
  Line 427: [extern "log10"] Float.log10 <- ❌ (Rust does not define this function)
  Line 434: [extern "pow"] Float.pow <- src/rust/runtime/src/runtime_object_nat_int.rs:451 (lean_internal_panic(b"Nat.pow exponent is too big\0".as_ptr() as *const c_char);) 🔍 (Referenced in Rust)
  Line 441: [extern "sqrt"] Float.sqrt <- ❌ (Rust does not define this function)
  Line 448: [extern "cbrt"] Float.cbrt <- ❌ (Rust does not define this function)
  Line 460: [extern "ceil"] Float.ceil <- ❌ (Rust does not define this function)
  Line 472: [extern "floor"] Float.floor <- ❌ (Rust does not define this function)
  Line 479: [extern "round"] Float.round <- ❌ (Rust does not define this function)
  Line 486: [extern "fabs"] Float.abs <- ❌ (Rust does not define this function)
  Line 499: [extern "lean_float_scaleb"] Float.scaleB <- src/rust/runtime/src/runtime_float.rs:62 (pub unsafe fn lean_float_scaleb(value: f64, scale: *mut LeanObject) -> f64 {) ✅

src/Init/Util.lean
  Line 18: [extern "lean_dbg_trace"] dbgTrace <- src/rust/runtime/src/runtime_debug.rs:138 (pub unsafe fn lean_dbg_trace(msg: *mut LeanObject, action: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 26: [extern "lean_dbg_trace_if_shared"] dbgTraceIfShared <- src/rust/runtime/src/runtime_debug.rs:148 (pub unsafe fn lean_dbg_trace_if_shared() ✅
  Line 30: [extern "lean_dbg_stack_trace"] dbgStackTrace <- src/rust/runtime/src/runtime_object_panic.rs:69 (pub unsafe fn lean_dbg_stack_trace(fn_obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 41: [extern "lean_dbg_sleep"] dbgSleep <- src/rust/runtime/src/runtime_debug.rs:143 (pub unsafe fn lean_dbg_sleep(ms: u32, action: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 89: [extern "lean_ptr_addr"] ptrAddrUnsafe <- ❌ (Rust does not define this function)
  Line 98: [extern "lean_is_exclusive_obj"] isExclusiveUnsafe <- ❌ (Rust does not define this function)

src/Init/Data/Float32.lean
  Line 51: [extern "lean_float32_add"] Float32.add <- ❌ (Rust does not define this function)
  Line 57: [extern "lean_float32_sub"] Float32.sub <- ❌ (Rust does not define this function)
  Line 63: [extern "lean_float32_mul"] Float32.mul <- ❌ (Rust does not define this function)
  Line 72: [extern "lean_float32_div"] Float32.div <- ❌ (Rust does not define this function)
  Line 79: [extern "lean_float32_negate"] Float32.neg <- ❌ (Rust does not define this function)
  Line 104: [extern "lean_float32_of_bits"] Float32.ofBits <- src/rust/runtime/src/runtime_float.rs:136 (pub fn lean_float32_of_bits(bits: u32) -> f32 {) ✅
  Line 119: [extern "lean_float32_to_bits"] Float32.toBits <- src/rust/runtime/src/runtime_float.rs:141 (pub fn lean_float32_to_bits(mut value: f32) -> u32 {) ✅
  Line 138: [extern "lean_float32_beq"] Float32.beq <- ❌ (Rust does not define this function)
  Line 147: [extern "lean_float32_decLt"] Float32.decLt <- ❌ (Rust does not define this function)
  Line 156: [extern "lean_float32_decLe"] Float32.decLe <- ❌ (Rust does not define this function)
  Line 165: [extern "lean_float32_to_string"] Float32.toString <- src/rust/runtime/src/runtime_float.rs:106 (pub fn lean_float32_to_string(value: f32) -> *mut LeanObject {) ✅
  Line 175: [extern "lean_float32_to_uint8"] Float32.toUInt8 <- ❌ (Rust does not define this function)
  Line 185: [extern "lean_float32_to_uint16"] Float32.toUInt16 <- ❌ (Rust does not define this function)
  Line 195: [extern "lean_float32_to_uint32"] Float32.toUInt32 <- ❌ (Rust does not define this function)
  Line 205: [extern "lean_float32_to_uint64"] Float32.toUInt64 <- ❌ (Rust does not define this function)
  Line 215: [extern "lean_float32_to_usize"] Float32.toUSize <- ❌ (Rust does not define this function)
  Line 224: [extern "lean_float32_isnan"] Float32.isNaN <- src/rust/runtime/src/runtime_float.rs:124 (pub fn lean_float32_isnan(value: f32) -> u8 {) ✅
  Line 231: [extern "lean_float32_isfinite"] Float32.isFinite <- src/rust/runtime/src/runtime_float.rs:128 (pub fn lean_float32_isfinite(value: f32) -> u8 {) ✅
  Line 238: [extern "lean_float32_isinf"] Float32.isInf <- src/rust/runtime/src/runtime_float.rs:132 (pub fn lean_float32_isinf(value: f32) -> u8 {) ✅
  Line 246: [extern "lean_float32_frexp"] Float32.frExp <- src/rust/runtime/src/runtime_float.rs:148 (pub unsafe fn lean_float32_frexp(value: f32) -> *mut LeanObject {) ✅
  Line 252: [extern "lean_uint8_to_float32"] UInt8.toFloat32 <- ❌ (Rust does not define this function)
  Line 254: [extern "lean_uint16_to_float32"] UInt16.toFloat32 <- ❌ (Rust does not define this function)
  Line 265: [extern "lean_uint32_to_float32"] UInt32.toFloat32 <- ❌ (Rust does not define this function)
  Line 276: [extern "lean_uint64_to_float32"] UInt64.toFloat32 <- ❌ (Rust does not define this function)
  Line 286: [extern "lean_usize_to_float32"] USize.toFloat32 <- ❌ (Rust does not define this function)
  Line 305: [extern "sinf"] Float32.sin <- ❌ (Rust does not define this function)
  Line 312: [extern "cosf"] Float32.cos <- ❌ (Rust does not define this function)
  Line 319: [extern "tanf"] Float32.tan <- ❌ (Rust does not define this function)
  Line 326: [extern "asinf"] Float32.asin <- ❌ (Rust does not define this function)
  Line 333: [extern "acosf"] Float32.acos <- ❌ (Rust does not define this function)
  Line 340: [extern "atanf"] Float32.atan <- ❌ (Rust does not define this function)
  Line 348: [extern "atan2f"] Float32.atan2 <- ❌ (Rust does not define this function)
  Line 355: [extern "sinhf"] Float32.sinh <- ❌ (Rust does not define this function)
  Line 362: [extern "coshf"] Float32.cosh <- ❌ (Rust does not define this function)
  Line 369: [extern "tanhf"] Float32.tanh <- ❌ (Rust does not define this function)
  Line 376: [extern "asinhf"] Float32.asinh <- ❌ (Rust does not define this function)
  Line 383: [extern "acoshf"] Float32.acosh <- ❌ (Rust does not define this function)
  Line 390: [extern "atanhf"] Float32.atanh <- ❌ (Rust does not define this function)
  Line 397: [extern "expf"] Float32.exp <- ❌ (Rust does not define this function)
  Line 404: [extern "exp2f"] Float32.exp2 <- ❌ (Rust does not define this function)
  Line 411: [extern "logf"] Float32.log <- ❌ (Rust does not define this function)
  Line 418: [extern "log2f"] Float32.log2 <- ❌ (Rust does not define this function)
  Line 425: [extern "log10f"] Float32.log10 <- ❌ (Rust does not define this function)
  Line 432: [extern "powf"] Float32.pow <- ❌ (Rust does not define this function)
  Line 439: [extern "sqrtf"] Float32.sqrt <- ❌ (Rust does not define this function)
  Line 446: [extern "cbrtf"] Float32.cbrt <- ❌ (Rust does not define this function)
  Line 458: [extern "ceilf"] Float32.ceil <- ❌ (Rust does not define this function)
  Line 470: [extern "floorf"] Float32.floor <- ❌ (Rust does not define this function)
  Line 477: [extern "roundf"] Float32.round <- ❌ (Rust does not define this function)
  Line 484: [extern "fabsf"] Float32.abs <- ❌ (Rust does not define this function)
  Line 497: [extern "lean_float32_scaleb"] Float32.scaleB <- src/rust/runtime/src/runtime_float.rs:114 (pub unsafe fn lean_float32_scaleb(value: f32, scale: *mut LeanObject) -> f32 {) ✅
  Line 505: [extern "lean_float32_to_float"] Float32.toFloat <- ❌ (Rust does not define this function)
  Line 512: [extern "lean_float_to_float32"] Float.toFloat32 <- ❌ (Rust does not define this function)

src/Init/Data/Array/Basic.lean
  Line 165: [extern "lean_array_size"] usize <- src/rust/leanh/src/not_in_emit_rust.rs:55 (pub unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {) ✅
  Line 173: [extern "lean_array_uget"] uget <- ❌ (Rust does not define this function)
  Line 182: [extern "lean_array_uget_borrowed"] ugetBorrowed <- ❌ (Rust does not define this function)
  Line 192: [extern "lean_array_uset"] uset <- ❌ (Rust does not define this function)
  Line 205: [extern "lean_array_pop"] pop <- ❌ (Rust does not define this function)
  Line 224: [extern "lean_mk_array"] replicate <- src/rust/runtime/src/runtime_object_array.rs:225 (pub unsafe fn lean_mk_array(n: *mut LeanObject, v: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 238: [extern "lean_array_fswap"] swap <- ❌ (Rust does not define this function)
  Line 261: [extern "lean_array_swap"] swapIfInBounds <- ❌ (Rust does not define this function)

src/Init/Meta/Defs.lean
  Line 23: [extern "lean_version_get_major"] version.getMajor <- ❌ (Rust does not define this function)
  Line 27: [extern "lean_version_get_minor"] version.getMinor <- ❌ (Rust does not define this function)
  Line 31: [extern "lean_version_get_patch"] version.getPatch <- ❌ (Rust does not define this function)
  Line 35: [extern "lean_get_githash"] getGithash <- src/rust/runtime/src/base.rs:1029 (pub unsafe fn lean_get_githash(_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 39: [extern "lean_version_get_is_release"] version.getIsRelease <- ❌ (Rust does not define this function)
  Line 44: [extern "lean_version_get_special_desc"] version.getSpecialDesc <- ❌ (Rust does not define this function)
  Line 85: [extern "lean_internal_is_stage0"] Internal.isStage0 <- ❌ (Rust does not define this function)
  Line 94: [extern "lean_internal_has_llvm_backend"] Internal.hasLLVMBackend <- src/rust/runtime/src/base.rs:1033 (pub fn lean_internal_has_llvm_backend(_: *mut LeanObject) -> u8 {) ✅

src/Init/Data/Nat/Log2.lean
  Line 41: [extern "lean_nat_log2"] log2 <- src/rust/runtime/src/runtime_object_nat_int.rs:488 (pub unsafe fn lean_nat_log2(a: *mut LeanObject) -> *mut LeanObject {) ✅

src/Init/Data/Nat/Gcd.lean
  Line 34: [extern "lean_nat_gcd"] gcd <- src/rust/runtime/src/runtime_object_nat_int.rs:467 (pub unsafe fn lean_nat_gcd(a1: *mut LeanObject, a2: *mut LeanObject) -> *mut LeanObject {) ✅

src/Init/System/ST.lean
  Line 22: [extern "lean_void_mk"] Void.mk <- ❌ (Rust does not define this function)
  Line 186: [extern "lean_st_mk_ref"] mkRef <- src/rust/runtime/src/runtime_io_ref.rs:53 (pub unsafe fn lean_st_mk_ref(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 188: [extern "lean_st_ref_get"] Ref.get <- src/rust/runtime/src/runtime_io_ref.rs:62 (pub unsafe fn lean_st_ref_get(ref_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 190: [extern "lean_st_ref_set"] Ref.set <- src/rust/runtime/src/runtime_io_ref.rs:103 (pub unsafe fn lean_st_ref_set(ref_: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 192: [extern "lean_st_ref_swap"] Ref.swap <- src/rust/runtime/src/runtime_io_ref.rs:122 (pub unsafe fn lean_st_ref_swap(ref_: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 194: [extern "lean_st_ref_take"] Ref.take <- src/rust/runtime/src/runtime_io_ref.rs:85 (pub unsafe fn lean_st_ref_take(ref_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 196: [extern "lean_st_ref_ptr_eq"] Ref.ptrEq <- src/rust/runtime/src/runtime_io_ref.rs:143 (pub unsafe fn lean_st_ref_ptr_eq(ref1: *mut LeanObject, ref2: *mut LeanObject) -> u8 {) ✅

src/Init/Data/UInt/Log2.lean
  Line 29: [extern "lean_uint8_log2"] UInt8.log2 <- ❌ (Rust does not define this function)
  Line 46: [extern "lean_uint16_log2"] UInt16.log2 <- ❌ (Rust does not define this function)
  Line 63: [extern "lean_uint32_log2"] UInt32.log2 <- ❌ (Rust does not define this function)
  Line 80: [extern "lean_uint64_log2"] UInt64.log2 <- ❌ (Rust does not define this function)
  Line 97: [extern "lean_usize_log2"] USize.log2 <- ❌ (Rust does not define this function)

src/Init/Data/UInt/Basic.lean
  Line 32: [extern "lean_uint8_add"] UInt8.add <- ❌ (Rust does not define this function)
  Line 40: [extern "lean_uint8_sub"] UInt8.sub <- ❌ (Rust does not define this function)
  Line 48: [extern "lean_uint8_mul"] UInt8.mul <- ❌ (Rust does not define this function)
  Line 58: [extern "lean_uint8_div"] UInt8.div <- ❌ (Rust does not define this function)
  Line 84: [extern "lean_uint8_mod"] UInt8.mod <- ❌ (Rust does not define this function)
  Line 98: [extern "lean_uint8_land"] UInt8.land <- ❌ (Rust does not define this function)
  Line 108: [extern "lean_uint8_lor"] UInt8.lor <- ❌ (Rust does not define this function)
  Line 118: [extern "lean_uint8_xor"] UInt8.xor <- ❌ (Rust does not define this function)
  Line 125: [extern "lean_uint8_shift_left"] UInt8.shiftLeft <- ❌ (Rust does not define this function)
  Line 132: [extern "lean_uint8_shift_right"] UInt8.shiftRight <- ❌ (Rust does not define this function)
  Line 154: [extern "lean_uint8_complement"] UInt8.complement <- ❌ (Rust does not define this function)
  Line 163: [extern "lean_uint8_neg"] UInt8.neg <- ❌ (Rust does not define this function)
  Line 177: [extern "lean_bool_to_uint8"] Bool.toUInt8 <- ❌ (Rust does not define this function)
  Line 203: [extern "lean_uint16_add"] UInt16.add <- ❌ (Rust does not define this function)
  Line 211: [extern "lean_uint16_sub"] UInt16.sub <- ❌ (Rust does not define this function)
  Line 219: [extern "lean_uint16_mul"] UInt16.mul <- ❌ (Rust does not define this function)
  Line 229: [extern "lean_uint16_div"] UInt16.div <- ❌ (Rust does not define this function)
  Line 255: [extern "lean_uint16_mod"] UInt16.mod <- ❌ (Rust does not define this function)
  Line 269: [extern "lean_uint16_land"] UInt16.land <- ❌ (Rust does not define this function)
  Line 279: [extern "lean_uint16_lor"] UInt16.lor <- ❌ (Rust does not define this function)
  Line 289: [extern "lean_uint16_xor"] UInt16.xor <- ❌ (Rust does not define this function)
  Line 296: [extern "lean_uint16_shift_left"] UInt16.shiftLeft <- ❌ (Rust does not define this function)
  Line 303: [extern "lean_uint16_shift_right"] UInt16.shiftRight <- ❌ (Rust does not define this function)
  Line 337: [extern "lean_uint16_complement"] UInt16.complement <- ❌ (Rust does not define this function)
  Line 346: [extern "lean_uint16_neg"] UInt16.neg <- ❌ (Rust does not define this function)
  Line 360: [extern "lean_bool_to_uint16"] Bool.toUInt16 <- ❌ (Rust does not define this function)
  Line 375: [extern "lean_uint16_dec_lt"] UInt16.decLt <- src/rust/leanh/src/in_emit_rust.rs:745 (lean_uint16_dec_lt,) 🔍 (Referenced in Rust)
  Line 392: [extern "lean_uint16_dec_le"] UInt16.decLe <- src/rust/leanh/src/in_emit_rust.rs:746 (lean_uint16_dec_le) 🔍 (Referenced in Rust)
  Line 413: [extern "lean_uint32_mul"] UInt32.mul <- ❌ (Rust does not define this function)
  Line 423: [extern "lean_uint32_div"] UInt32.div <- ❌ (Rust does not define this function)
  Line 449: [extern "lean_uint32_mod"] UInt32.mod <- ❌ (Rust does not define this function)
  Line 463: [extern "lean_uint32_land"] UInt32.land <- ❌ (Rust does not define this function)
  Line 473: [extern "lean_uint32_lor"] UInt32.lor <- ❌ (Rust does not define this function)
  Line 483: [extern "lean_uint32_xor"] UInt32.xor <- ❌ (Rust does not define this function)
  Line 490: [extern "lean_uint32_shift_left"] UInt32.shiftLeft <- ❌ (Rust does not define this function)
  Line 497: [extern "lean_uint32_shift_right"] UInt32.shiftRight <- ❌ (Rust does not define this function)
  Line 530: [extern "lean_uint32_complement"] UInt32.complement <- ❌ (Rust does not define this function)
  Line 539: [extern "lean_uint32_neg"] UInt32.neg <- ❌ (Rust does not define this function)
  Line 553: [extern "lean_bool_to_uint32"] Bool.toUInt32 <- ❌ (Rust does not define this function)
  Line 568: [extern "lean_uint64_add"] UInt64.add <- ❌ (Rust does not define this function)
  Line 576: [extern "lean_uint64_sub"] UInt64.sub <- ❌ (Rust does not define this function)
  Line 584: [extern "lean_uint64_mul"] UInt64.mul <- ❌ (Rust does not define this function)
  Line 594: [extern "lean_uint64_div"] UInt64.div <- ❌ (Rust does not define this function)
  Line 620: [extern "lean_uint64_mod"] UInt64.mod <- ❌ (Rust does not define this function)
  Line 634: [extern "lean_uint64_land"] UInt64.land <- ❌ (Rust does not define this function)
  Line 644: [extern "lean_uint64_lor"] UInt64.lor <- ❌ (Rust does not define this function)
  Line 654: [extern "lean_uint64_xor"] UInt64.xor <- ❌ (Rust does not define this function)
  Line 661: [extern "lean_uint64_shift_left"] UInt64.shiftLeft <- ❌ (Rust does not define this function)
  Line 668: [extern "lean_uint64_shift_right"] UInt64.shiftRight <- ❌ (Rust does not define this function)
  Line 702: [extern "lean_uint64_complement"] UInt64.complement <- ❌ (Rust does not define this function)
  Line 711: [extern "lean_uint64_neg"] UInt64.neg <- ❌ (Rust does not define this function)
  Line 725: [extern "lean_bool_to_uint64"] Bool.toUInt64 <- ❌ (Rust does not define this function)
  Line 739: [extern "lean_uint64_dec_lt"] UInt64.decLt <- src/rust/leanh/src/in_emit_rust.rs:765 (lean_uint64_dec_lt,) 🔍 (Referenced in Rust)
  Line 755: [extern "lean_uint64_dec_le"] UInt64.decLe <- src/rust/leanh/src/in_emit_rust.rs:766 (lean_uint64_dec_le) 🔍 (Referenced in Rust)
  Line 779: [extern "lean_usize_mul"] USize.mul <- ❌ (Rust does not define this function)
  Line 789: [extern "lean_usize_div"] USize.div <- ❌ (Rust does not define this function)
  Line 815: [extern "lean_usize_mod"] USize.mod <- ❌ (Rust does not define this function)
  Line 829: [extern "lean_usize_land"] USize.land <- ❌ (Rust does not define this function)
  Line 839: [extern "lean_usize_lor"] USize.lor <- ❌ (Rust does not define this function)
  Line 849: [extern "lean_usize_xor"] USize.xor <- ❌ (Rust does not define this function)
  Line 856: [extern "lean_usize_shift_left"] USize.shiftLeft <- ❌ (Rust does not define this function)
  Line 863: [extern "lean_usize_shift_right"] USize.shiftRight <- ❌ (Rust does not define this function)
  Line 871: [extern "lean_usize_of_nat"] USize.ofNat32 <- src/rust/runtime/src/library_ir_interpreter.rs:354 (unsafe fn lean_usize_of_nat(a: *mut LeanObject) -> usize {) ✅
  Line 879: [extern "lean_uint8_to_usize"] UInt8.toUSize <- ❌ (Rust does not define this function)
  Line 887: [extern "lean_usize_to_uint8"] USize.toUInt8 <- ❌ (Rust does not define this function)
  Line 894: [extern "lean_uint16_to_usize"] UInt16.toUSize <- ❌ (Rust does not define this function)
  Line 902: [extern "lean_usize_to_uint16"] USize.toUInt16 <- ❌ (Rust does not define this function)
  Line 909: [extern "lean_uint32_to_usize"] UInt32.toUSize <- ❌ (Rust does not define this function)
  Line 917: [extern "lean_usize_to_uint32"] USize.toUInt32 <- ❌ (Rust does not define this function)
  Line 925: [extern "lean_uint64_to_usize"] UInt64.toUSize <- ❌ (Rust does not define this function)
  Line 933: [extern "lean_usize_to_uint64"] USize.toUInt64 <- ❌ (Rust does not define this function)
  Line 954: [extern "lean_usize_complement"] USize.complement <- ❌ (Rust does not define this function)
  Line 961: [extern "lean_usize_neg"] USize.neg <- ❌ (Rust does not define this function)
  Line 975: [extern "lean_bool_to_usize"] Bool.toUSize <- ❌ (Rust does not define this function)

src/Init/Data/ByteArray/Basic.lean
  Line 23: [extern "lean_sarray_dec_eq"] beq <- ❌ (Rust does not define this function)
  Line 32: [extern "lean_sarray_dec_eq"] decEq <- ❌ (Rust does not define this function)
  Line 50: [extern "lean_sarray_size"] usize <- src/rust/runtime/src/base.rs:194 (pub(crate) unsafe fn lean_sarray_size(obj: *mut LeanObject) -> Size {) ✅
  Line 61: [extern "lean_byte_array_uget"] uget <- ❌ (Rust does not define this function)
  Line 68: [extern "lean_byte_array_get"] get <- ❌ (Rust does not define this function)
  Line 78: [extern "lean_byte_array_fget"] get <- ❌ (Rust does not define this function)
  Line 95: [extern "lean_byte_array_set"] set <- ❌ (Rust does not define this function)
  Line 107: [extern "lean_byte_array_fset"] set <- ❌ (Rust does not define this function)
  Line 111: [extern "lean_byte_array_uset"] uset <- ❌ (Rust does not define this function)
  Line 118: [extern "lean_byte_array_hash"] hash <- src/rust/runtime/src/runtime_object_array.rs:181 (pub unsafe fn lean_byte_array_hash(a: *mut LeanObject) -> u64 {) ✅
  Line 135: [extern "lean_byte_array_copy_slice"] copySlice <- src/rust/runtime/src/runtime_object_array.rs:150 (pub unsafe fn lean_byte_array_copy_slice() ✅

src/Init/ShareCommon.lean
  Line 42: [extern "lean_sharecommon_eq"] Object.eq <- src/rust/runtime/src/runtime_sharecommon.rs:83 (pub unsafe fn lean_sharecommon_eq(o1: *mut LeanObject, o2: *mut LeanObject) -> u8 {) ✅
  Line 45: [extern "lean_sharecommon_hash"] Object.hash <- src/rust/runtime/src/runtime_sharecommon.rs:114 (pub unsafe fn lean_sharecommon_hash(o: *mut LeanObject) -> u64 {) ✅
  Line 86: [extern "lean_state_sharecommon"] State.shareCommon <- src/rust/runtime/src/runtime_sharecommon.rs:375 (pub unsafe fn lean_state_sharecommon() ✅
  Line 116: [extern "lean_sharecommon_quick"] ShareCommon.shareCommon' <- src/rust/runtime/src/runtime_sharecommon.rs:546 (pub unsafe fn lean_sharecommon_quick(a: *mut LeanObject) -> *mut LeanObject {) ✅

src/Init/Data/String/PosRaw.lean
  Line 107: [extern "lean_string_get_byte_fast"] getUTF8Byte <- ❌ (Rust does not define this function)
  Line 111: [extern "lean_string_get_byte_fast"] getUtf8Byte <- ❌ (Rust does not define this function)

src/Init/Data/String/Defs.lean
  Line 75: [extern "lean_string_to_utf8"] String.toUTF8 <- src/rust/runtime/src/runtime_object_string.rs:228 (pub unsafe fn lean_string_to_utf8(s: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 93: [extern "lean_string_append"] String.append <- src/rust/runtime/src/runtime_object_string.rs:261 (pub unsafe fn lean_string_append(s1: *mut LeanObject, s2: *mut LeanObject) -> *mut LeanObject {) ✅

src/Init/Data/String/Basic.lean
  Line 88: [extern "lean_string_validate_utf8"] ByteArray.validateUTF8 <- src/rust/runtime/src/runtime_object_string.rs:222 (pub unsafe fn lean_string_validate_utf8(a: *mut LeanObject) -> u8 {) ✅
  Line 240: [extern "lean_string_data"] String.toList <- src/rust/runtime/src/runtime_object_string.rs:664 (pub unsafe fn lean_string_data(s: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 255: [extern "lean_string_data"] String.data <- src/rust/runtime/src/runtime_object_string.rs:664 (pub unsafe fn lean_string_data(s: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 424: [extern "lean_string_dec_lt"] decidableLT <- ❌ (Rust does not define this function)
  Line 666: [extern "lean_string_is_valid_pos"] Pos.Raw.isValid <- src/rust/runtime/src/runtime_object_string.rs:460 (pub unsafe fn lean_string_is_valid_pos(s: *mut LeanObject, i0: *mut LeanObject) -> u8 {) ✅
  Line 786: [extern "lean_string_utf8_extract"] extract <- src/rust/runtime/src/runtime_object_string.rs:476 (pub unsafe fn lean_string_utf8_extract() ✅
  Line 1152: [extern "lean_string_utf8_get_fast"] decodeChar <- ❌ (Rust does not define this function)
  Line 1665: [extern "lean_string_utf8_next_fast"] Pos.next <- ❌ (Rust does not define this function)
  Line 1892: [extern "lean_string_utf8_get"] Pos.Raw.get <- src/rust/runtime/src/runtime_object_string.rs:328 (pub unsafe fn lean_string_utf8_get(s: *mut LeanObject, i0: *mut LeanObject) -> u32 {) ✅
  Line 1896: [extern "lean_string_utf8_get"] get <- src/rust/runtime/src/runtime_object_string.rs:328 (pub unsafe fn lean_string_utf8_get(s: *mut LeanObject, i0: *mut LeanObject) -> u32 {) ✅
  Line 1924: [extern "lean_string_utf8_get_opt"] Pos.Raw.get <- src/rust/runtime/src/runtime_object_string.rs:376 (pub unsafe fn lean_string_utf8_get_opt() ✅
  Line 1928: [extern "lean_string_utf8_get_opt"] get <- src/rust/runtime/src/runtime_object_string.rs:376 (pub unsafe fn lean_string_utf8_get_opt() ✅
  Line 1946: [extern "lean_string_utf8_get_bang"] Pos.Raw.get <- src/rust/runtime/src/runtime_object_string.rs:405 (pub unsafe fn lean_string_utf8_get_bang(s: *mut LeanObject, i0: *mut LeanObject) -> u32 {) ✅
  Line 1951: [extern "lean_string_utf8_get_bang"] get <- src/rust/runtime/src/runtime_object_string.rs:405 (pub unsafe fn lean_string_utf8_get_bang(s: *mut LeanObject, i0: *mut LeanObject) -> u32 {) ✅
  Line 2813: [extern "lean_string_utf8_next"] Pos.Raw.next <- src/rust/runtime/src/runtime_object_string.rs:418 (pub unsafe fn lean_string_utf8_next() ✅
  Line 2818: [extern "lean_string_utf8_next"] next <- src/rust/runtime/src/runtime_object_string.rs:418 (pub unsafe fn lean_string_utf8_next() ✅
  Line 2850: [extern "lean_string_utf8_prev"] Pos.Raw.prev <- src/rust/runtime/src/runtime_object_string.rs:505 (pub unsafe fn lean_string_utf8_prev() ✅
  Line 2854: [extern "lean_string_utf8_prev"] prev <- src/rust/runtime/src/runtime_object_string.rs:505 (pub unsafe fn lean_string_utf8_prev() ✅
  Line 2871: [extern "lean_string_utf8_at_end"] Pos.Raw.atEnd <- ❌ (Rust does not define this function)
  Line 2875: [extern "lean_string_utf8_at_end"] atEnd <- ❌ (Rust does not define this function)
  Line 2902: [extern "lean_string_utf8_get_fast"] Pos.Raw.get' <- ❌ (Rust does not define this function)
  Line 2907: [extern "lean_string_utf8_get_fast"] get' <- ❌ (Rust does not define this function)
  Line 2932: [extern "lean_string_utf8_next_fast"] Pos.Raw.next' <- ❌ (Rust does not define this function)
  Line 2937: [extern "lean_string_utf8_next_fast"] next' <- ❌ (Rust does not define this function)
  Line 3012: [extern "lean_string_utf8_extract"] Pos.Raw.extract <- src/rust/runtime/src/runtime_object_string.rs:476 (pub unsafe fn lean_string_utf8_extract() ✅

src/Init/Data/String/Length.lean
  Line 24: [extern "lean_string_length"] length <- ❌ (Rust does not define this function)

src/Init/Data/SInt/Basic.lean
  Line 112: [extern "lean_int8_of_int"] Int8.ofInt <- ❌ (Rust does not define this function)
  Line 125: [extern "lean_int8_of_nat"] Int8.ofNat <- ❌ (Rust does not define this function)
  Line 154: [extern "lean_int8_to_int"] Int8.toInt <- ❌ (Rust does not define this function)
  Line 170: [extern "lean_int8_neg"] Int8.neg <- ❌ (Rust does not define this function)
  Line 213: [extern "lean_int8_add"] Int8.add <- ❌ (Rust does not define this function)
  Line 221: [extern "lean_int8_sub"] Int8.sub <- ❌ (Rust does not define this function)
  Line 229: [extern "lean_int8_mul"] Int8.mul <- ❌ (Rust does not define this function)
  Line 246: [extern "lean_int8_div"] Int8.div <- ❌ (Rust does not define this function)
  Line 278: [extern "lean_int8_mod"] Int8.mod <- ❌ (Rust does not define this function)
  Line 288: [extern "lean_int8_land"] Int8.land <- ❌ (Rust does not define this function)
  Line 298: [extern "lean_int8_lor"] Int8.lor <- ❌ (Rust does not define this function)
  Line 308: [extern "lean_int8_xor"] Int8.xor <- ❌ (Rust does not define this function)
  Line 317: [extern "lean_int8_shift_left"] Int8.shiftLeft <- ❌ (Rust does not define this function)
  Line 326: [extern "lean_int8_shift_right"] Int8.shiftRight <- ❌ (Rust does not define this function)
  Line 337: [extern "lean_int8_complement"] Int8.complement <- ❌ (Rust does not define this function)
  Line 347: [extern "lean_int8_abs"] Int8.abs <- ❌ (Rust does not define this function)
  Line 361: [extern "lean_int8_dec_eq"] Int8.decEq <- ❌ (Rust does not define this function)
  Line 403: [extern "lean_bool_to_int8"] Bool.toInt8 <- ❌ (Rust does not define this function)
  Line 417: [extern "lean_int8_dec_lt"] Int8.decLt <- ❌ (Rust does not define this function)
  Line 433: [extern "lean_int8_dec_le"] Int8.decLe <- ❌ (Rust does not define this function)
  Line 468: [extern "lean_int16_of_int"] Int16.ofInt <- ❌ (Rust does not define this function)
  Line 481: [extern "lean_int16_of_nat"] Int16.ofNat <- ❌ (Rust does not define this function)
  Line 511: [extern "lean_int16_to_int"] Int16.toInt <- ❌ (Rust does not define this function)
  Line 528: [extern "lean_int16_to_int8"] Int16.toInt8 <- ❌ (Rust does not define this function)
  Line 535: [extern "lean_int8_to_int16"] Int8.toInt16 <- ❌ (Rust does not define this function)
  Line 542: [extern "lean_int16_neg"] Int16.neg <- ❌ (Rust does not define this function)
  Line 586: [extern "lean_int16_add"] Int16.add <- ❌ (Rust does not define this function)
  Line 594: [extern "lean_int16_sub"] Int16.sub <- ❌ (Rust does not define this function)
  Line 602: [extern "lean_int16_mul"] Int16.mul <- ❌ (Rust does not define this function)
  Line 619: [extern "lean_int16_div"] Int16.div <- ❌ (Rust does not define this function)
  Line 651: [extern "lean_int16_mod"] Int16.mod <- ❌ (Rust does not define this function)
  Line 661: [extern "lean_int16_land"] Int16.land <- ❌ (Rust does not define this function)
  Line 671: [extern "lean_int16_lor"] Int16.lor <- ❌ (Rust does not define this function)
  Line 681: [extern "lean_int16_xor"] Int16.xor <- ❌ (Rust does not define this function)
  Line 690: [extern "lean_int16_shift_left"] Int16.shiftLeft <- ❌ (Rust does not define this function)
  Line 699: [extern "lean_int16_shift_right"] Int16.shiftRight <- ❌ (Rust does not define this function)
  Line 710: [extern "lean_int16_complement"] Int16.complement <- ❌ (Rust does not define this function)
  Line 720: [extern "lean_int16_abs"] Int16.abs <- ❌ (Rust does not define this function)
  Line 734: [extern "lean_int16_dec_eq"] Int16.decEq <- ❌ (Rust does not define this function)
  Line 776: [extern "lean_bool_to_int16"] Bool.toInt16 <- ❌ (Rust does not define this function)
  Line 790: [extern "lean_int16_dec_lt"] Int16.decLt <- ❌ (Rust does not define this function)
  Line 806: [extern "lean_int16_dec_le"] Int16.decLe <- ❌ (Rust does not define this function)
  Line 842: [extern "lean_int32_of_int"] Int32.ofInt <- ❌ (Rust does not define this function)
  Line 855: [extern "lean_int32_of_nat"] Int32.ofNat <- ❌ (Rust does not define this function)
  Line 885: [extern "lean_int32_to_int"] Int32.toInt <- ❌ (Rust does not define this function)
  Line 902: [extern "lean_int32_to_int8"] Int32.toInt8 <- ❌ (Rust does not define this function)
  Line 910: [extern "lean_int32_to_int16"] Int32.toInt16 <- ❌ (Rust does not define this function)
  Line 917: [extern "lean_int8_to_int32"] Int8.toInt32 <- ❌ (Rust does not define this function)
  Line 924: [extern "lean_int16_to_int32"] Int16.toInt32 <- ❌ (Rust does not define this function)
  Line 931: [extern "lean_int32_neg"] Int32.neg <- ❌ (Rust does not define this function)
  Line 975: [extern "lean_int32_add"] Int32.add <- ❌ (Rust does not define this function)
  Line 983: [extern "lean_int32_sub"] Int32.sub <- ❌ (Rust does not define this function)
  Line 991: [extern "lean_int32_mul"] Int32.mul <- ❌ (Rust does not define this function)
  Line 1008: [extern "lean_int32_div"] Int32.div <- ❌ (Rust does not define this function)
  Line 1040: [extern "lean_int32_mod"] Int32.mod <- ❌ (Rust does not define this function)
  Line 1050: [extern "lean_int32_land"] Int32.land <- ❌ (Rust does not define this function)
  Line 1060: [extern "lean_int32_lor"] Int32.lor <- ❌ (Rust does not define this function)
  Line 1070: [extern "lean_int32_xor"] Int32.xor <- ❌ (Rust does not define this function)
  Line 1079: [extern "lean_int32_shift_left"] Int32.shiftLeft <- ❌ (Rust does not define this function)
  Line 1088: [extern "lean_int32_shift_right"] Int32.shiftRight <- ❌ (Rust does not define this function)
  Line 1099: [extern "lean_int32_complement"] Int32.complement <- ❌ (Rust does not define this function)
  Line 1109: [extern "lean_int32_abs"] Int32.abs <- ❌ (Rust does not define this function)
  Line 1123: [extern "lean_int32_dec_eq"] Int32.decEq <- ❌ (Rust does not define this function)
  Line 1165: [extern "lean_bool_to_int32"] Bool.toInt32 <- ❌ (Rust does not define this function)
  Line 1179: [extern "lean_int32_dec_lt"] Int32.decLt <- ❌ (Rust does not define this function)
  Line 1195: [extern "lean_int32_dec_le"] Int32.decLe <- ❌ (Rust does not define this function)
  Line 1231: [extern "lean_int64_of_int"] Int64.ofInt <- ❌ (Rust does not define this function)
  Line 1246: [extern "lean_int64_of_nat"] Int64.ofNat <- ❌ (Rust does not define this function)
  Line 1279: [extern "lean_int64_to_int_sint"] Int64.toInt <- ❌ (Rust does not define this function)
  Line 1296: [extern "lean_int64_to_int8"] Int64.toInt8 <- ❌ (Rust does not define this function)
  Line 1304: [extern "lean_int64_to_int16"] Int64.toInt16 <- ❌ (Rust does not define this function)
  Line 1312: [extern "lean_int64_to_int32"] Int64.toInt32 <- ❌ (Rust does not define this function)
  Line 1319: [extern "lean_int8_to_int64"] Int8.toInt64 <- ❌ (Rust does not define this function)
  Line 1326: [extern "lean_int16_to_int64"] Int16.toInt64 <- ❌ (Rust does not define this function)
  Line 1333: [extern "lean_int32_to_int64"] Int32.toInt64 <- ❌ (Rust does not define this function)
  Line 1340: [extern "lean_int64_neg"] Int64.neg <- ❌ (Rust does not define this function)
  Line 1384: [extern "lean_int64_add"] Int64.add <- ❌ (Rust does not define this function)
  Line 1392: [extern "lean_int64_sub"] Int64.sub <- ❌ (Rust does not define this function)
  Line 1400: [extern "lean_int64_mul"] Int64.mul <- ❌ (Rust does not define this function)
  Line 1417: [extern "lean_int64_div"] Int64.div <- ❌ (Rust does not define this function)
  Line 1449: [extern "lean_int64_mod"] Int64.mod <- ❌ (Rust does not define this function)
  Line 1459: [extern "lean_int64_land"] Int64.land <- ❌ (Rust does not define this function)
  Line 1469: [extern "lean_int64_lor"] Int64.lor <- ❌ (Rust does not define this function)
  Line 1479: [extern "lean_int64_xor"] Int64.xor <- ❌ (Rust does not define this function)
  Line 1488: [extern "lean_int64_shift_left"] Int64.shiftLeft <- ❌ (Rust does not define this function)
  Line 1497: [extern "lean_int64_shift_right"] Int64.shiftRight <- ❌ (Rust does not define this function)
  Line 1508: [extern "lean_int64_complement"] Int64.complement <- ❌ (Rust does not define this function)
  Line 1518: [extern "lean_int64_abs"] Int64.abs <- ❌ (Rust does not define this function)
  Line 1532: [extern "lean_int64_dec_eq"] Int64.decEq <- ❌ (Rust does not define this function)
  Line 1574: [extern "lean_bool_to_int64"] Bool.toInt64 <- ❌ (Rust does not define this function)
  Line 1588: [extern "lean_int64_dec_lt"] Int64.decLt <- ❌ (Rust does not define this function)
  Line 1603: [extern "lean_int64_dec_le"] Int64.decLe <- ❌ (Rust does not define this function)
  Line 1632: [extern "lean_isize_of_int"] ISize.ofInt <- ❌ (Rust does not define this function)
  Line 1640: [extern "lean_isize_of_nat"] ISize.ofNat <- ❌ (Rust does not define this function)
  Line 1650: [extern "lean_isize_to_int"] ISize.toInt <- ❌ (Rust does not define this function)
  Line 1666: [extern "lean_isize_to_int8"] ISize.toInt8 <- ❌ (Rust does not define this function)
  Line 1673: [extern "lean_isize_to_int16"] ISize.toInt16 <- ❌ (Rust does not define this function)
  Line 1684: [extern "lean_isize_to_int32"] ISize.toInt32 <- ❌ (Rust does not define this function)
  Line 1692: [extern "lean_isize_to_int64"] ISize.toInt64 <- ❌ (Rust does not define this function)
  Line 1700: [extern "lean_int8_to_isize"] Int8.toISize <- ❌ (Rust does not define this function)
  Line 1708: [extern "lean_int16_to_isize"] Int16.toISize <- ❌ (Rust does not define this function)
  Line 1716: [extern "lean_int32_to_isize"] Int32.toISize <- ❌ (Rust does not define this function)
  Line 1724: [extern "lean_int64_to_isize"] Int64.toISize <- ❌ (Rust does not define this function)
  Line 1731: [extern "lean_isize_neg"] ISize.neg <- ❌ (Rust does not define this function)
  Line 1776: [extern "lean_isize_add"] ISize.add <- ❌ (Rust does not define this function)
  Line 1784: [extern "lean_isize_sub"] ISize.sub <- ❌ (Rust does not define this function)
  Line 1792: [extern "lean_isize_mul"] ISize.mul <- ❌ (Rust does not define this function)
  Line 1809: [extern "lean_isize_div"] ISize.div <- ❌ (Rust does not define this function)
  Line 1841: [extern "lean_isize_mod"] ISize.mod <- ❌ (Rust does not define this function)
  Line 1851: [extern "lean_isize_land"] ISize.land <- ❌ (Rust does not define this function)
  Line 1861: [extern "lean_isize_lor"] ISize.lor <- ❌ (Rust does not define this function)
  Line 1871: [extern "lean_isize_xor"] ISize.xor <- ❌ (Rust does not define this function)
  Line 1880: [extern "lean_isize_shift_left"] ISize.shiftLeft <- ❌ (Rust does not define this function)
  Line 1890: [extern "lean_isize_shift_right"] ISize.shiftRight <- ❌ (Rust does not define this function)
  Line 1901: [extern "lean_isize_complement"] ISize.complement <- ❌ (Rust does not define this function)
  Line 1912: [extern "lean_isize_abs"] ISize.abs <- ❌ (Rust does not define this function)
  Line 1926: [extern "lean_isize_dec_eq"] ISize.decEq <- ❌ (Rust does not define this function)
  Line 1968: [extern "lean_bool_to_isize"] Bool.toISize <- ❌ (Rust does not define this function)
  Line 1982: [extern "lean_isize_dec_lt"] ISize.decLt <- ❌ (Rust does not define this function)
  Line 1998: [extern "lean_isize_dec_le"] ISize.decLe <- ❌ (Rust does not define this function)

src/Init/Data/FloatArray/Basic.lean
  Line 20: [extern "lean_float_array_mk"] FloatArray.mk <- src/rust/runtime/src/runtime_object_array.rs:189 (pub unsafe fn lean_float_array_mk(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 21: [extern "lean_float_array_data"] FloatArray.data <- src/rust/runtime/src/runtime_object_array.rs:201 (pub unsafe fn lean_float_array_data(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 29: [extern "lean_mk_empty_float_array"] emptyWithCapacity <- ❌ (Rust does not define this function)
  Line 42: [extern "lean_float_array_push"] push <- src/rust/runtime/src/runtime_object_array.rs:213 (pub unsafe fn lean_float_array_push(a: *mut LeanObject, d: f64) -> *mut LeanObject {) ✅
  Line 46: [extern "lean_float_array_size"] size <- ❌ (Rust does not define this function)
  Line 50: [extern "lean_sarray_size"] usize <- src/rust/runtime/src/base.rs:194 (pub(crate) unsafe fn lean_sarray_size(obj: *mut LeanObject) -> Size {) ✅
  Line 54: [extern "lean_float_array_uget"] uget <- ❌ (Rust does not define this function)
  Line 58: [extern "lean_float_array_fget"] get <- ❌ (Rust does not define this function)
  Line 62: [extern "lean_float_array_get"] get <- ❌ (Rust does not define this function)
  Line 78: [extern "lean_float_array_uset"] uset <- ❌ (Rust does not define this function)
  Line 82: [extern "lean_float_array_fset"] set <- ❌ (Rust does not define this function)
  Line 86: [extern "lean_float_array_set"] set <- ❌ (Rust does not define this function)

src/Init/Data/Ord/String.lean
  Line 31: [extern "lean_string_compare"] compare <- src/rust/runtime/src/runtime_object_string.rs:312 (pub unsafe fn lean_string_compare(s1: *mut LeanObject, s2: *mut LeanObject) -> u8 {) ✅

src/Std/Data/ByteSlice.lean
  Line 185: [extern "lean_byteslice_beq"] beq <- src/rust/runtime/src/base.rs:1265 (pub unsafe fn lean_byteslice_beq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {) ✅

src/Init/Data/SInt/Float.lean
  Line 25: [extern "lean_float_to_int8"] Float.toInt8 <- ❌ (Rust does not define this function)
  Line 36: [extern "lean_float_to_int16"] Float.toInt16 <- ❌ (Rust does not define this function)
  Line 47: [extern "lean_float_to_int32"] Float.toInt32 <- ❌ (Rust does not define this function)
  Line 58: [extern "lean_float_to_int64"] Float.toInt64 <- ❌ (Rust does not define this function)
  Line 69: [extern "lean_float_to_isize"] Float.toISize <- ❌ (Rust does not define this function)
  Line 76: [extern "lean_int8_to_float"] Int8.toFloat <- ❌ (Rust does not define this function)
  Line 82: [extern "lean_int16_to_float"] Int16.toFloat <- ❌ (Rust does not define this function)
  Line 88: [extern "lean_int32_to_float"] Int32.toFloat <- ❌ (Rust does not define this function)
  Line 99: [extern "lean_int64_to_float"] Int64.toFloat <- ❌ (Rust does not define this function)
  Line 109: [extern "lean_isize_to_float"] ISize.toFloat <- ❌ (Rust does not define this function)

src/Init/Data/SInt/Float32.lean
  Line 25: [extern "lean_float32_to_int8"] Float32.toInt8 <- ❌ (Rust does not define this function)
  Line 36: [extern "lean_float32_to_int16"] Float32.toInt16 <- ❌ (Rust does not define this function)
  Line 47: [extern "lean_float32_to_int32"] Float32.toInt32 <- ❌ (Rust does not define this function)
  Line 58: [extern "lean_float32_to_int64"] Float32.toInt64 <- ❌ (Rust does not define this function)
  Line 69: [extern "lean_float32_to_isize"] Float32.toISize <- ❌ (Rust does not define this function)
  Line 76: [extern "lean_int8_to_float32"] Int8.toFloat32 <- ❌ (Rust does not define this function)
  Line 82: [extern "lean_int16_to_float32"] Int16.toFloat32 <- ❌ (Rust does not define this function)
  Line 92: [extern "lean_int32_to_float32"] Int32.toFloat32 <- ❌ (Rust does not define this function)
  Line 102: [extern "lean_int64_to_float32"] Int64.toFloat32 <- ❌ (Rust does not define this function)
  Line 112: [extern "lean_isize_to_float32"] ISize.toFloat32 <- ❌ (Rust does not define this function)

src/Init/Data/String/Modify.lean
  Line 34: [extern "lean_string_utf8_set"] Pos.set <- src/rust/runtime/src/runtime_object_string.rs:529 (pub unsafe fn lean_string_utf8_set() ✅
  Line 160: [extern "lean_string_utf8_set"] Pos.Raw.set <- src/rust/runtime/src/runtime_object_string.rs:529 (pub unsafe fn lean_string_utf8_set() ✅
  Line 164: [extern "lean_string_utf8_set"] set <- src/rust/runtime/src/runtime_object_string.rs:529 (pub unsafe fn lean_string_utf8_set() ✅

src/Init/Data/String/Pattern/Basic.lean
  Line 299: [extern "lean_string_memcmp"] memcmpStr <- src/rust/runtime/src/runtime_object_string.rs:595 (pub unsafe fn lean_string_memcmp() ✅

src/Init/Data/String/Slice.lean
  Line 86: [extern "lean_slice_hash"] hash <- src/rust/runtime/src/runtime_object_string.rs:619 (pub unsafe fn lean_slice_hash(s: *mut LeanObject) -> u64 {) ✅
  Line 96: [extern "lean_slice_dec_lt"] instance <- src/rust/runtime/src/runtime_object_string.rs:627 (pub unsafe fn lean_slice_dec_lt(s1: *mut LeanObject, s2: *mut LeanObject) -> u8 {) ✅

src/Lean/Compiler/FFI.lean
  Line 18: [extern "lean_get_leanc_extra_flags"] getLeancExtraFlags <- src/rust/runtime/src/base.rs:1053 (pub unsafe fn lean_get_leanc_extra_flags(_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 35: [extern "lean_get_leanc_internal_flags"] getLeancInternalFlags <- src/rust/runtime/src/base.rs:1057 (pub unsafe fn lean_get_leanc_internal_flags(_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 42: [extern "lean_get_linker_flags"] getBuiltinLinkerFlags <- src/rust/runtime/src/base.rs:1061 (pub unsafe fn lean_get_linker_flags(link_static: u8) -> *mut LeanObject {) ✅
  Line 56: [extern "lean_get_internal_linker_flags"] getBuiltinInternalLinkerFlags <- src/rust/runtime/src/base.rs:1085 (pub unsafe fn lean_get_internal_linker_flags(_: *mut LeanObject) -> *mut LeanObject {) ✅

src/Init/System/IO.lean
  Line 218: [extern "lean_io_timeit"] timeit <- src/rust/runtime/src/base.rs:1183 (pub unsafe fn lean_io_timeit(msg: *mut LeanObject, fn_obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 220: [extern "lean_io_allocprof"] allocprof <- src/rust/runtime/src/base.rs:539 (pub unsafe fn lean_io_allocprof(msg: *mut LeanObject, fn_obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 229: [extern "lean_io_initializing"] IO.initializing <- src/rust/runtime/src/base.rs:1025 (pub fn lean_io_initializing() -> u8 {) ✅
  Line 244: [extern "lean_io_as_task"] asTask <- src/rust/runtime/src/runtime_io_task.rs:79 (pub unsafe fn lean_io_as_task(act: *mut LeanObject, prio: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 257: [extern "lean_io_map_task"] mapTask <- src/rust/runtime/src/runtime_io_task.rs:85 (pub unsafe fn lean_io_map_task() ✅
  Line 271: [extern "lean_io_bind_task"] bindTask <- src/rust/runtime/src/runtime_io_task.rs:96 (pub unsafe fn lean_io_bind_task() ✅
  Line 415: [extern "lean_io_mono_ms_now"] monoMsNow <- src/rust/runtime/src/base.rs:1212 (pub unsafe fn lean_io_mono_ms_now() -> *mut LeanObject {) ✅
  Line 421: [extern "lean_io_mono_nanos_now"] monoNanosNow <- src/rust/runtime/src/base.rs:1221 (pub unsafe fn lean_io_mono_nanos_now() -> *mut LeanObject {) ✅
  Line 428: [extern "lean_io_get_random_bytes"] getRandomBytes <- src/rust/runtime/src/runtime_io_fs.rs:374 (pub unsafe fn lean_io_get_random_bytes(nbytes: usize) -> *mut LeanObject {) ✅
  Line 505: [extern "lean_io_check_canceled"] checkCanceled <- src/rust/runtime/src/runtime_io_task.rs:52 (pub unsafe fn lean_io_check_canceled() -> u8 {) ✅
  Line 511: [extern "lean_io_cancel"] cancel <- src/rust/runtime/src/runtime_io_task.rs:56 (pub unsafe fn lean_io_cancel(t: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 555: [extern "lean_io_get_task_state"] getTaskState <- src/rust/runtime/src/runtime_io_task.rs:61 (pub unsafe fn lean_io_get_task_state(t: *mut LeanObject) -> u8 {) ✅
  Line 567: [extern "lean_io_wait"] wait <- src/rust/runtime/src/runtime_io_task.rs:65 (pub unsafe fn lean_io_wait(t: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 573: [extern "lean_io_wait_any"] waitAny <- src/rust/runtime/src/runtime_io_task.rs:72 (pub unsafe fn lean_io_wait_any(task_list: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 594: [extern "lean_io_get_num_heartbeats"] getNumHeartbeats <- src/rust/runtime/src/base.rs:1202 (pub unsafe fn lean_io_get_num_heartbeats() -> *mut LeanObject {) ✅
  Line 600: [extern "lean_io_set_heartbeats"] setNumHeartbeats <- src/rust/runtime/src/base.rs:1206 (pub unsafe fn lean_io_set_heartbeats(count: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 742: [extern "lean_get_stdin"] getStdin <- src/rust/runtime/src/runtime_io_stream.rs:59 (pub unsafe fn lean_get_stdin() -> *mut LeanObject {) ✅
  Line 748: [extern "lean_get_stdout"] getStdout <- src/rust/runtime/src/runtime_io_stream.rs:67 (pub unsafe fn lean_get_stdout() -> *mut LeanObject {) ✅
  Line 754: [extern "lean_get_stderr"] getStderr <- src/rust/runtime/src/runtime_io_stream.rs:75 (pub unsafe fn lean_get_stderr() -> *mut LeanObject {) ✅
  Line 761: [extern "lean_get_set_stdin"] setStdin <- src/rust/runtime/src/runtime_io_stream.rs:83 (pub unsafe fn lean_get_set_stdin(handle: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 767: [extern "lean_get_set_stdout"] setStdout <- src/rust/runtime/src/runtime_io_stream.rs:87 (pub unsafe fn lean_get_set_stdout(handle: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 773: [extern "lean_get_set_stderr"] setStderr <- src/rust/runtime/src/runtime_io_stream.rs:91 (pub unsafe fn lean_get_set_stderr(handle: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 795: [extern "lean_io_prim_handle_mk"] mk <- src/rust/runtime/src/base.rs:359 (pub unsafe fn lean_io_prim_handle_mk(filename: *mut LeanObject, mode: u8) -> *mut LeanObject {) ✅
  Line 803: [extern "lean_io_prim_handle_lock"] lock <- src/rust/runtime/src/runtime_io_handle.rs:14 (pub unsafe fn lean_io_prim_handle_lock(h: *mut LeanObject, exclusive: u8) -> *mut LeanObject {) ✅
  Line 811: [extern "lean_io_prim_handle_try_lock"] tryLock <- src/rust/runtime/src/runtime_io_handle.rs:31 (pub unsafe fn lean_io_prim_handle_try_lock() ✅
  Line 815: [extern "lean_io_prim_handle_unlock"] unlock <- src/rust/runtime/src/runtime_io_handle.rs:53 (pub unsafe fn lean_io_prim_handle_unlock(h: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 820: [extern "lean_io_prim_handle_is_tty"] isTty <- src/rust/runtime/src/base.rs:212 (pub unsafe fn lean_io_prim_handle_is_tty(h: *mut LeanObject) -> u8 {) ✅
  Line 826: [extern "lean_io_prim_handle_flush"] flush <- src/rust/runtime/src/base.rs:226 (pub unsafe fn lean_io_prim_handle_flush(h: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 830: [extern "lean_io_prim_handle_rewind"] rewind <- src/rust/runtime/src/base.rs:238 (pub unsafe fn lean_io_prim_handle_rewind(h: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 840: [extern "lean_io_prim_handle_truncate"] truncate <- src/rust/runtime/src/base.rs:250 (pub unsafe fn lean_io_prim_handle_truncate(h: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 847: [extern "lean_io_prim_handle_read"] read <- src/rust/runtime/src/base.rs:262 (pub unsafe fn lean_io_prim_handle_read(h: *mut LeanObject, nbytes: Size) -> *mut LeanObject {) ✅
  Line 854: [extern "lean_io_prim_handle_write"] write <- src/rust/runtime/src/base.rs:295 (pub unsafe fn lean_io_prim_handle_write() ✅
  Line 862: [extern "lean_io_prim_handle_get_line"] getLine <- src/rust/runtime/src/base.rs:312 (pub unsafe fn lean_io_prim_handle_get_line(h: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 869: [extern "lean_io_prim_handle_put_str"] putStr <- src/rust/runtime/src/base.rs:342 (pub unsafe fn lean_io_prim_handle_put_str() ✅
  Line 879: [extern "lean_io_realpath"] realPath <- src/rust/runtime/src/runtime_io_fs.rs:229 (pub unsafe fn lean_io_realpath(filename: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 886: [extern "lean_io_remove_file"] removeFile <- src/rust/runtime/src/runtime_io_fs.rs:215 (pub unsafe fn lean_io_remove_file(filename: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 894: [extern "lean_io_remove_dir"] removeDir <- src/rust/runtime/src/runtime_io_fs.rs:163 (pub unsafe fn lean_io_remove_dir(p: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 900: [extern "lean_io_create_dir"] createDir <- src/rust/runtime/src/runtime_io_fs.rs:150 (pub unsafe fn lean_io_create_dir(p: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 909: [extern "lean_io_rename"] rename <- src/rust/runtime/src/runtime_io_fs.rs:175 (pub unsafe fn lean_io_rename(from: *mut LeanObject, to: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 921: [extern "lean_io_hard_link"] hardLink <- src/rust/runtime/src/runtime_io_fs.rs:194 (pub unsafe fn lean_io_hard_link() ✅
  Line 933: [extern "lean_io_create_tempfile"] createTempFile <- src/rust/runtime/src/runtime_io_fs.rs:344 (pub unsafe fn lean_io_create_tempfile(_w: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 943: [extern "lean_io_create_tempdir"] createTempDir <- src/rust/runtime/src/runtime_io_fs.rs:322 (pub unsafe fn lean_io_create_tempdir(_w: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 951: [extern "lean_io_getenv"] getEnv <- src/rust/runtime/src/base.rs:1243 (pub unsafe fn lean_io_getenv(env_var: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 955: [extern "lean_io_app_path"] appPath <- src/rust/runtime/src/runtime_io_fs.rs:437 (pub unsafe fn lean_io_app_path() -> *mut LeanObject {) ✅
  Line 959: [extern "lean_io_current_dir"] currentDir <- src/rust/runtime/src/runtime_io_fs.rs:427 (pub unsafe fn lean_io_current_dir() -> *mut LeanObject {) ✅
  Line 1141: [extern "lean_io_read_dir"] readDir <- src/rust/runtime/src/runtime_io_fs.rs:252 (pub unsafe fn lean_io_read_dir(dirname: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1148: [extern "lean_io_metadata"] metadata <- src/rust/runtime/src/runtime_io_fs.rs:288 (pub unsafe fn lean_io_metadata(filename: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1155: [extern "lean_io_symlink_metadata"] symlinkMetadata <- src/rust/runtime/src/runtime_io_fs.rs:305 (pub unsafe fn lean_io_symlink_metadata(filename: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1383: [extern "lean_io_process_get_current_dir"] getCurrentDir <- src/rust/runtime/src/runtime_process.rs:161 (pub unsafe fn lean_io_process_get_current_dir() -> *mut LeanObject {) ✅
  Line 1386: [extern "lean_io_process_set_current_dir"] setCurrentDir <- src/rust/runtime/src/runtime_process.rs:176 (pub unsafe fn lean_io_process_set_current_dir(path: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1389: [extern "lean_io_process_get_pid"] getPID <- src/rust/runtime/src/runtime_process.rs:187 (pub unsafe fn lean_io_process_get_pid() -> u32 {) ✅
  Line 1489: [extern "lean_io_process_spawn"] spawn <- src/rust/runtime/src/runtime_process.rs:480 (pub unsafe fn lean_io_process_spawn(args_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1494: [extern "lean_io_process_child_wait"] Child.wait <- src/rust/runtime/src/runtime_process.rs:201 (pub unsafe fn lean_io_process_child_wait() ✅
  Line 1500: [extern "lean_io_process_child_try_wait"] Child.tryWait <- src/rust/runtime/src/runtime_process.rs:222 (pub unsafe fn lean_io_process_child_try_wait() ✅
  Line 1508: [extern "lean_io_process_child_kill"] Child.kill <- src/rust/runtime/src/runtime_process.rs:246 (pub unsafe fn lean_io_process_child_kill() ✅
  Line 1520: [extern "lean_io_process_child_take_stdin"] Child.takeStdin <- src/rust/runtime/src/runtime_process.rs:281 (pub unsafe fn lean_io_process_child_take_stdin() ✅
  Line 1524: [extern "lean_io_process_child_pid"] Child.pid <- src/rust/runtime/src/runtime_process.rs:267 (pub unsafe fn lean_io_process_child_pid() ✅
  Line 1579: [extern "lean_io_exit"] exit <- src/rust/runtime/src/runtime_io_ref.rs:147 (pub fn lean_io_exit(code: u8) -> *mut LeanObject {) ✅
  Line 1588: [extern "lean_io_force_exit"] forceExit <- src/rust/runtime/src/runtime_io_ref.rs:151 (pub fn lean_io_force_exit(code: u8) -> *mut LeanObject {) ✅
  Line 1593: [extern "lean_io_get_tid"] getTID <- src/rust/runtime/src/runtime_process.rs:194 (pub unsafe fn lean_io_get_tid() -> u64 {) ✅
  Line 1650: [extern "lean_chmod"] Prim.setAccessRights <- src/rust/runtime/src/runtime_io_fs.rs:138 (pub unsafe fn lean_chmod(filename: *mut LeanObject, mode: u32) -> *mut LeanObject {) ✅
  Line 1826: [extern "lean_runtime_mark_multi_threaded"] Runtime.markMultiThreaded <- src/rust/runtime/src/runtime_io_ref.rs:160 (pub unsafe fn lean_runtime_mark_multi_threaded(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1839: [extern "lean_runtime_mark_persistent"] Runtime.markPersistent <- src/rust/runtime/src/runtime_io_ref.rs:155 (pub unsafe fn lean_runtime_mark_persistent(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1850: [extern "lean_runtime_forget"] Runtime.forget <- src/rust/runtime/src/runtime_io_ref.rs:165 (pub unsafe fn lean_runtime_forget(o: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 1859: [extern "lean_runtime_hold"] Runtime.hold <- ❌ (Rust does not define this function)

src/Init/System/Promise.lean
  Line 40: [extern "lean_io_promise_new"] Promise.new <- src/rust/runtime/src/runtime_object_task.rs:534 (pub unsafe fn lean_io_promise_new() -> *mut LeanObject {) ✅
  Line 48: [extern "lean_io_promise_resolve"] Promise.resolve <- src/rust/runtime/src/runtime_object_task.rs:538 (pub unsafe fn lean_io_promise_resolve() ✅
  Line 54: [extern "lean_io_promise_result_opt"] Promise.result <- src/rust/runtime/src/runtime_object_task.rs:546 (pub unsafe fn lean_io_promise_result_opt(promise: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 58: [extern "lean_option_get_or_block"] Option.getOrBlock <- src/rust/runtime/src/base.rs:506 (pub unsafe fn lean_option_get_or_block(opt: *mut LeanObject) -> *mut LeanObject {) ✅

src/Std/Sync/Mutex.lean
  Line 28: [extern "lean_io_basemutex_new"] BaseMutex.new <- src/rust/runtime/src/runtime_mutex.rs:18 (pub unsafe fn lean_io_basemutex_new() -> *mut LeanObject {) ✅
  Line 38: [extern "lean_io_basemutex_lock"] BaseMutex.lock <- src/rust/runtime/src/runtime_mutex.rs:22 (pub unsafe fn lean_io_basemutex_lock(mtx: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 51: [extern "lean_io_basemutex_try_lock"] BaseMutex.tryLock <- src/rust/runtime/src/runtime_mutex.rs:27 (pub unsafe fn lean_io_basemutex_try_lock(mtx: *mut LeanObject) -> u8 {) ✅
  Line 61: [extern "lean_io_basemutex_unlock"] BaseMutex.unlock <- src/rust/runtime/src/runtime_mutex.rs:31 (pub unsafe fn lean_io_basemutex_unlock(mtx: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 92: [extern "lean_io_condvar_new"] Condvar.new <- src/rust/runtime/src/runtime_mutex.rs:36 (pub unsafe fn lean_io_condvar_new() -> *mut LeanObject {) ✅
  Line 96: [extern "lean_io_condvar_wait"] Condvar.wait <- src/rust/runtime/src/runtime_mutex.rs:40 (pub unsafe fn lean_io_condvar_wait() ✅
  Line 100: [extern "lean_io_condvar_notify_one"] Condvar.notifyOne <- src/rust/runtime/src/runtime_mutex.rs:48 (pub unsafe fn lean_io_condvar_notify_one(condvar: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 104: [extern "lean_io_condvar_notify_all"] Condvar.notifyAll <- src/rust/runtime/src/runtime_mutex.rs:55 (pub unsafe fn lean_io_condvar_notify_all(condvar: *mut LeanObject) -> *mut LeanObject {) ✅

src/Lean/Compiler/IR/LLVMBindings.lean
  Line 95: [extern "lean_llvm_get_value_name2"] Value.getName <- src/rust/runtime/src/library_llvm.rs:2011 (pub unsafe fn lean_llvm_get_value_name2() ✅
  Line 102: [extern "lean_llvm_initialize_target_info"] llvmInitializeTargetInfo <- src/rust/runtime/src/library_llvm.rs:65 (pub unsafe fn lean_llvm_initialize_target_info() -> *mut LeanObject {) ✅
  Line 105: [extern "lean_llvm_create_context"] createContext <- src/rust/runtime/src/library_llvm.rs:69 (pub unsafe fn lean_llvm_create_context() -> usize {) ✅
  Line 108: [extern "lean_llvm_create_module"] createModule <- src/rust/runtime/src/library_llvm.rs:1389 (pub unsafe fn lean_llvm_create_module(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 111: [extern "lean_llvm_module_to_string"] moduleToString <- src/rust/runtime/src/library_llvm.rs:1403 (pub unsafe fn lean_llvm_module_to_string() ✅
  Line 114: [extern "lean_llvm_write_bitcode_to_file"] writeBitcodeToFile <- src/rust/runtime/src/library_llvm.rs:1394 (pub unsafe fn lean_llvm_write_bitcode_to_file() ✅
  Line 117: [extern "lean_llvm_add_function"] addFunction <- src/rust/runtime/src/library_llvm.rs:1411 (pub unsafe fn lean_llvm_add_function() ✅
  Line 120: [extern "lean_llvm_get_first_function"] getFirstFunction <- src/rust/runtime/src/library_llvm.rs:1992 (pub unsafe fn lean_llvm_get_first_function(_p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 123: [extern "lean_llvm_get_next_function"] getNextFunction <- src/rust/runtime/src/library_llvm.rs:1997 (pub unsafe fn lean_llvm_get_next_function(_p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 126: [extern "lean_llvm_get_named_function"] getNamedFunction <- src/rust/runtime/src/library_llvm.rs:1421 (pub unsafe fn lean_llvm_get_named_function() ✅
  Line 129: [extern "lean_llvm_add_global"] addGlobal <- src/rust/runtime/src/library_llvm.rs:1430 (pub unsafe fn lean_llvm_add_global() ✅
  Line 132: [extern "lean_llvm_get_named_global"] getNamedGlobal <- src/rust/runtime/src/library_llvm.rs:1440 (pub unsafe fn lean_llvm_get_named_global() ✅
  Line 135: [extern "lean_llvm_get_first_global"] getFirstGlobal <- src/rust/runtime/src/library_llvm.rs:1982 (pub unsafe fn lean_llvm_get_first_global(_p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 138: [extern "lean_llvm_get_next_global"] getNextGlobal <- src/rust/runtime/src/library_llvm.rs:1987 (pub unsafe fn lean_llvm_get_next_global(_p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 141: [extern "lean_llvm_build_global_string"] buildGlobalString <- src/rust/runtime/src/library_llvm.rs:1449 (pub unsafe fn lean_llvm_build_global_string() ✅
  Line 144: [extern "llvm_is_declaration"] isDeclaration <- src/rust/runtime/src/library_llvm.rs:2019 (pub unsafe fn llvm_is_declaration() ✅
  Line 147: [extern "lean_llvm_set_initializer"] setInitializer <- src/rust/runtime/src/library_llvm.rs:1464 (pub unsafe fn lean_llvm_set_initializer() ✅
  Line 150: [extern "lean_llvm_function_type"] functionType <- src/rust/runtime/src/library_llvm.rs:1473 (pub unsafe fn lean_llvm_function_type() ✅
  Line 153: [extern "lean_llvm_void_type_in_context"] voidType <- src/rust/runtime/src/library_llvm.rs:1501 (pub unsafe fn lean_llvm_void_type_in_context(p0: *mut LeanObject) -> usize {) ✅
  Line 156: [extern "lean_llvm_int_type_in_context"] intTypeInContext <- src/rust/runtime/src/library_llvm.rs:1491 (pub unsafe fn lean_llvm_int_type_in_context(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 159: [extern "lean_llvm_opaque_pointer_type_in_context"] opaquePointerTypeInContext <- src/rust/runtime/src/library_llvm.rs:1483 (pub unsafe fn lean_llvm_opaque_pointer_type_in_context() ✅
  Line 162: [extern "lean_llvm_float_type_in_context"] floatTypeInContext <- src/rust/runtime/src/library_llvm.rs:1496 (pub unsafe fn lean_llvm_float_type_in_context(p0: *mut LeanObject) -> usize {) ✅
  Line 165: [extern "lean_llvm_double_type_in_context"] doubleTypeInContext <- src/rust/runtime/src/library_llvm.rs:1506 (pub unsafe fn lean_llvm_double_type_in_context(p0: *mut LeanObject) -> usize {) ✅
  Line 168: [extern "lean_llvm_pointer_type"] pointerType <- src/rust/runtime/src/library_llvm.rs:1511 (pub unsafe fn lean_llvm_pointer_type(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 171: [extern "lean_llvm_array_type"] arrayType <- src/rust/runtime/src/library_llvm.rs:1516 (pub unsafe fn lean_llvm_array_type() ✅
  Line 174: [extern "lean_llvm_const_array"] constArray <- src/rust/runtime/src/library_llvm.rs:1846 (pub unsafe fn lean_llvm_const_array() ✅
  Line 178: [extern "lean_llvm_const_string"] constString <- src/rust/runtime/src/library_llvm.rs:1856 (pub unsafe fn lean_llvm_const_string(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 181: [extern "lean_llvm_const_pointer_null"] constPointerNull <- src/rust/runtime/src/library_llvm.rs:1861 (pub unsafe fn lean_llvm_const_pointer_null(_p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 184: [extern "lean_llvm_get_undef"] getUndef <- src/rust/runtime/src/library_llvm.rs:1459 (pub unsafe fn lean_llvm_get_undef(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 187: [extern "lean_llvm_create_builder_in_context"] createBuilderInContext <- src/rust/runtime/src/library_llvm.rs:1525 (pub unsafe fn lean_llvm_create_builder_in_context(p0: *mut LeanObject) -> usize {) ✅
  Line 190: [extern "lean_llvm_append_basic_block_in_context"] appendBasicBlockInContext <- src/rust/runtime/src/library_llvm.rs:1530 (pub unsafe fn lean_llvm_append_basic_block_in_context() ✅
  Line 193: [extern "lean_llvm_count_basic_blocks"] countBasicBlocks <- src/rust/runtime/src/library_llvm.rs:2035 (pub unsafe fn lean_llvm_count_basic_blocks(_p0: *mut LeanObject, p1: *mut LeanObject) -> u64 {) ✅
  Line 196: [extern "lean_llvm_get_entry_basic_block"] getEntryBasicBlock <- src/rust/runtime/src/library_llvm.rs:2040 (pub unsafe fn lean_llvm_get_entry_basic_block() ✅
  Line 199: [extern "lean_llvm_get_first_instruction"] getFirstInstruction <- src/rust/runtime/src/library_llvm.rs:2048 (pub unsafe fn lean_llvm_get_first_instruction() ✅
  Line 202: [extern "lean_llvm_position_builder_before"] positionBuilderBefore <- src/rust/runtime/src/library_llvm.rs:2056 (pub unsafe fn lean_llvm_position_builder_before() ✅
  Line 205: [extern "lean_llvm_position_builder_at_end"] positionBuilderAtEnd <- src/rust/runtime/src/library_llvm.rs:1539 (pub unsafe fn lean_llvm_position_builder_at_end() ✅
  Line 208: [extern "lean_llvm_build_call2"] buildCall2 <- src/rust/runtime/src/library_llvm.rs:1556 (pub unsafe fn lean_llvm_build_call2() ✅
  Line 211: [extern "lean_llvm_set_tail_call"] setTailCall <- src/rust/runtime/src/library_llvm.rs:1880 (pub unsafe fn lean_llvm_set_tail_call() ✅
  Line 214: [extern "lean_llvm_build_cond_br"] buildCondBr <- src/rust/runtime/src/library_llvm.rs:1569 (pub unsafe fn lean_llvm_build_cond_br() ✅
  Line 217: [extern "lean_llvm_build_br"] buildBr <- src/rust/runtime/src/library_llvm.rs:1585 (pub unsafe fn lean_llvm_build_br() ✅
  Line 220: [extern "lean_llvm_build_alloca"] buildAlloca <- src/rust/runtime/src/library_llvm.rs:1615 (pub unsafe fn lean_llvm_build_alloca() ✅
  Line 223: [extern "lean_llvm_build_load2"] buildLoad2 <- src/rust/runtime/src/library_llvm.rs:1604 (pub unsafe fn lean_llvm_build_load2() ✅
  Line 226: [extern "lean_llvm_build_store"] buildStore <- src/rust/runtime/src/library_llvm.rs:1594 (pub unsafe fn lean_llvm_build_store() ✅
  Line 229: [extern "lean_llvm_build_ret"] buildRet <- src/rust/runtime/src/library_llvm.rs:1625 (pub unsafe fn lean_llvm_build_ret() ✅
  Line 232: [extern "lean_llvm_build_unreachable"] buildUnreachable <- src/rust/runtime/src/library_llvm.rs:1639 (pub unsafe fn lean_llvm_build_unreachable(_p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 235: [extern "lean_llvm_build_gep2"] buildGEP2 <- src/rust/runtime/src/library_llvm.rs:1657 (pub unsafe fn lean_llvm_build_gep2() ✅
  Line 238: [extern "lean_llvm_build_inbounds_gep2"] buildInBoundsGEP2 <- src/rust/runtime/src/library_llvm.rs:1644 (pub unsafe fn lean_llvm_build_inbounds_gep2() ✅
  Line 241: [extern "lean_llvm_build_sext"] buildSext <- src/rust/runtime/src/library_llvm.rs:1670 (pub unsafe fn lean_llvm_build_sext() ✅
  Line 244: [extern "lean_llvm_build_zext"] buildZext <- src/rust/runtime/src/library_llvm.rs:1681 (pub unsafe fn lean_llvm_build_zext() ✅
  Line 247: [extern "lean_llvm_build_sext_or_trunc"] buildSextOrTrunc <- src/rust/runtime/src/library_llvm.rs:1692 (pub unsafe fn lean_llvm_build_sext_or_trunc() ✅
  Line 250: [extern "lean_llvm_build_switch"] buildSwitch <- src/rust/runtime/src/library_llvm.rs:1703 (pub unsafe fn lean_llvm_build_switch() ✅
  Line 253: [extern "lean_llvm_build_ptr_to_int"] buildPtrToInt <- src/rust/runtime/src/library_llvm.rs:1719 (pub unsafe fn lean_llvm_build_ptr_to_int() ✅
  Line 256: [extern "lean_llvm_build_mul"] buildMul <- src/rust/runtime/src/library_llvm.rs:1730 (pub unsafe fn lean_llvm_build_mul() ✅
  Line 259: [extern "lean_llvm_build_add"] buildAdd <- src/rust/runtime/src/library_llvm.rs:1741 (pub unsafe fn lean_llvm_build_add() ✅
  Line 262: [extern "lean_llvm_build_sub"] buildSub <- src/rust/runtime/src/library_llvm.rs:1752 (pub unsafe fn lean_llvm_build_sub() ✅
  Line 265: [extern "lean_llvm_build_not"] buildNot <- src/rust/runtime/src/library_llvm.rs:1763 (pub unsafe fn lean_llvm_build_not() ✅
  Line 268: [extern "lean_llvm_build_icmp"] buildICmp <- src/rust/runtime/src/library_llvm.rs:1773 (pub unsafe fn lean_llvm_build_icmp() ✅
  Line 271: [extern "lean_llvm_add_case"] addCase <- src/rust/runtime/src/library_llvm.rs:1791 (pub unsafe fn lean_llvm_add_case() ✅
  Line 274: [extern "lean_llvm_get_insert_block"] getInsertBlock <- src/rust/runtime/src/library_llvm.rs:1809 (pub unsafe fn lean_llvm_get_insert_block(_p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 277: [extern "lean_llvm_clear_insertion_position"] clearInsertionPosition <- src/rust/runtime/src/library_llvm.rs:1548 (pub unsafe fn lean_llvm_clear_insertion_position() ✅
  Line 280: [extern "lean_llvm_get_basic_block_parent"] getBasicBlockParent <- src/rust/runtime/src/library_llvm.rs:1801 (pub unsafe fn lean_llvm_get_basic_block_parent() ✅
  Line 283: [extern "lean_llvm_type_of"] typeOf <- src/rust/runtime/src/library_llvm.rs:1814 (pub unsafe fn lean_llvm_type_of(_p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 286: [extern "lean_llvm_const_int"] constInt <- src/rust/runtime/src/library_llvm.rs:1836 (pub unsafe fn lean_llvm_const_int() ✅
  Line 289: [extern "lean_llvm_print_module_to_string"] printModuletoString <- src/rust/runtime/src/library_llvm.rs:1819 (pub unsafe fn lean_llvm_print_module_to_string() ✅
  Line 292: [extern "lean_llvm_print_module_to_file"] printModuletoFile <- src/rust/runtime/src/library_llvm.rs:1827 (pub unsafe fn lean_llvm_print_module_to_file() ✅
  Line 295: [extern "llvm_count_params"] countParams <- src/rust/runtime/src/library_llvm.rs:1875 (pub unsafe fn llvm_count_params(_p0: *mut LeanObject, p1: *mut LeanObject) -> u64 {) ✅
  Line 298: [extern "llvm_get_param"] getParam <- src/rust/runtime/src/library_llvm.rs:1866 (pub unsafe fn llvm_get_param() ✅
  Line 301: [extern "lean_llvm_create_memory_buffer_with_contents_of_file"] createMemoryBufferWithContentsOfFile <- src/rust/runtime/src/library_llvm.rs:2065 (pub unsafe fn lean_llvm_create_memory_buffer_with_contents_of_file() ✅
  Line 304: [extern "lean_llvm_parse_bitcode"] parseBitcode <- src/rust/runtime/src/library_llvm.rs:1889 (pub unsafe fn lean_llvm_parse_bitcode(p0: *mut LeanObject, p1: *mut LeanObject) -> usize {) ✅
  Line 307: [extern "lean_llvm_link_modules"] linkModules <- src/rust/runtime/src/library_llvm.rs:1894 (pub unsafe fn lean_llvm_link_modules() ✅
  Line 310: [extern "lean_llvm_get_default_target_triple"] getDefaultTargetTriple <- src/rust/runtime/src/library_llvm.rs:1922 (pub unsafe fn lean_llvm_get_default_target_triple() -> *mut LeanObject {) ✅
  Line 313: [extern "lean_llvm_get_target_from_triple"] getTargetFromTriple <- src/rust/runtime/src/library_llvm.rs:1914 (pub unsafe fn lean_llvm_get_target_from_triple() ✅
  Line 316: [extern "lean_llvm_create_target_machine"] createTargetMachine <- src/rust/runtime/src/library_llvm.rs:1903 (pub unsafe fn lean_llvm_create_target_machine() ✅
  Line 319: [extern "lean_llvm_target_machine_emit_to_file"] targetMachineEmitToFile <- src/rust/runtime/src/library_llvm.rs:1927 (pub unsafe fn lean_llvm_target_machine_emit_to_file() ✅
  Line 345: [extern "lean_llvm_dispose_target_machine"] disposeTargetMachine <- src/rust/runtime/src/library_llvm.rs:1938 (pub unsafe fn lean_llvm_dispose_target_machine() ✅
  Line 348: [extern "lean_llvm_dispose_module"] disposeModule <- src/rust/runtime/src/library_llvm.rs:1946 (pub unsafe fn lean_llvm_dispose_module() ✅
  Line 351: [extern "lean_llvm_verify_module"] verifyModule <- src/rust/runtime/src/library_llvm.rs:2027 (pub unsafe fn lean_llvm_verify_module() ✅
  Line 354: [extern "lean_llvm_create_string_attribute"] createStringAttribute <- src/rust/runtime/src/library_llvm.rs:2073 (pub unsafe fn lean_llvm_create_string_attribute() ✅
  Line 357: [extern "lean_llvm_add_attribute_at_index"] addAttributeAtIndex <- src/rust/runtime/src/library_llvm.rs:1972 (pub unsafe fn lean_llvm_add_attribute_at_index() ✅
  Line 369: [extern "lean_llvm_set_visibility"] setVisibility <- src/rust/runtime/src/library_llvm.rs:1954 (pub unsafe fn lean_llvm_set_visibility() ✅
  Line 380: [extern "lean_llvm_set_dll_storage_class"] setDLLStorageClass <- src/rust/runtime/src/library_llvm.rs:1963 (pub unsafe fn lean_llvm_set_dll_storage_class() ✅
  Line 421: [extern "lean_llvm_set_linkage"] setLinkage <- src/rust/runtime/src/library_llvm.rs:2002 (pub unsafe fn lean_llvm_set_linkage() ✅

src/Lean/LoadDynlib.lean
  Line 33: [extern "lean_dynlib_load"] Dynlib.load <- src/rust/runtime/src/library_dynlib.rs:66 (pub(crate) unsafe fn lean_dynlib_load(path: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 37: [extern "lean_dynlib_get"] Dynlib.get <- src/rust/runtime/src/library_dynlib.rs:76 (pub(crate) unsafe fn lean_dynlib_get() ✅
  Line 53: [extern "lean_dynlib_symbol_run_as_init"] Dynlib.Symbol.runAsInit <- src/rust/runtime/src/library_dynlib.rs:92 (pub(crate) unsafe fn lean_dynlib_symbol_run_as_init() ✅

src/Std/Internal/UV/Timer.lean
  Line 44: [extern "lean_uv_timer_mk"] mk <- src/rust/runtime/src/runtime_timer.rs:54 (pub unsafe fn lean_uv_timer_mk(timeout: u64, repeating: u8) -> *mut LeanObject {) ✅
  Line 63: [extern "lean_uv_timer_next"] next <- src/rust/runtime/src/runtime_timer.rs:126 (pub unsafe fn lean_uv_timer_next(obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 74: [extern "lean_uv_timer_reset"] reset <- src/rust/runtime/src/runtime_timer.rs:180 (pub unsafe fn lean_uv_timer_reset(obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 83: [extern "lean_uv_timer_stop"] stop <- src/rust/runtime/src/runtime_timer.rs:212 (pub unsafe fn lean_uv_timer_stop(obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 92: [extern "lean_uv_timer_cancel"] cancel <- src/rust/runtime/src/runtime_timer.rs:236 (pub unsafe fn lean_uv_timer_cancel(obj: *mut LeanObject) -> *mut LeanObject {) ✅

src/Lean/CompactedRegion.lean
  Line 21: [extern "lean_compacted_region_is_memory_mapped"] CompactedRegion.isMemoryMapped <- src/rust/runtime/src/runtime_compact.rs:69 (pub unsafe fn lean_compacted_region_is_memory_mapped(region: usize) -> u8 {) ✅
  Line 25: [extern "lean_compacted_region_size"] CompactedRegion.size <- src/rust/runtime/src/runtime_compact.rs:79 (pub unsafe fn lean_compacted_region_size(region: usize) -> usize {) ✅
  Line 32: [extern "lean_compacted_region_free"] CompactedRegion.free <- src/rust/runtime/src/runtime_compact.rs:89 (pub unsafe fn lean_compacted_region_free() ✅
  Line 69: [extern "lean_compacted_region_save"] CompactedRegion.save <- src/rust/runtime/src/runtime_compact_writer.rs:767 (pub unsafe fn lean_compacted_region_save() ✅
  Line 83: [extern "lean_compacted_region_read"] CompactedRegion.read <- src/rust/runtime/src/library_module.rs:449 (pub unsafe fn lean_compacted_region_read() ✅

src/Lean/Util/Profile.lean
  Line 37: [extern "lean_profileit"] profileit <- src/rust/runtime/src/library_time_task.rs:176 (pub unsafe fn lean_profileit() ✅
  Line 53: [extern "lean_display_cumulative_profiling_times"] displayCumulativeProfilingTimes <- src/rust/runtime/src/library_time_task.rs:160 (pub unsafe fn lean_display_cumulative_profiling_times() -> *mut LeanObject {) ✅

src/Lean/Level.lean
  Line 48: [extern "lean_level_mk_data"] Level.mkData <- src/rust/runtime/src/kernel_level.rs:52 (pub unsafe fn lean_level_mk_data() ✅
  Line 254: [extern "lean_level_eq"] beq <- src/rust/runtime/src/kernel_level.rs:75 (pub unsafe fn lean_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> u8 {) ✅

src/Lean/Expr.lean
  Line 171: [extern "lean_expr_mk_data"] Expr.mkData <- src/rust/runtime/src/kernel_expr.rs:112 (pub unsafe fn lean_expr_mk_data() ✅
  Line 176: [extern "lean_expr_mk_app_data"] Expr.mkAppData <- src/rust/runtime/src/kernel_expr.rs:142 (pub unsafe fn lean_expr_mk_app_data(f_data: u64, a_data: u64) -> u64 {) ✅
  Line 472: [extern "lean_expr_data"] data <- ❌ (Rust does not define this function)
  Line 779: [extern "lean_expr_dbg_to_string"] dbgToString <- src/rust/runtime/src/library_print.rs:593 (pub unsafe fn lean_expr_dbg_to_string(e: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 783: [extern "lean_expr_quick_lt"] quickLt <- src/rust/runtime/src/library_expr_lt.rs:493 (pub unsafe fn lean_expr_quick_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {) ✅
  Line 787: [extern "lean_expr_lt"] lt <- src/rust/runtime/src/library_expr_lt.rs:498 (pub unsafe fn lean_expr_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {) ✅
  Line 799: [extern "lean_expr_eqv"] eqv <- src/rust/runtime/src/kernel_expr_eq_fn.rs:386 (pub unsafe fn lean_expr_eqv(a: *mut LeanObject, b: *mut LeanObject) -> u8 {) ✅
  Line 809: [extern "lean_expr_equal"] equal <- src/rust/runtime/src/kernel_expr_eq_fn.rs:392 (pub unsafe fn lean_expr_equal(a: *mut LeanObject, b: *mut LeanObject) -> u8 {) ✅
  Line 1320: [extern "lean_expr_has_loose_bvar"] hasLooseBVar <- src/rust/runtime/src/kernel_expr.rs:197 (pub unsafe fn lean_expr_has_loose_bvar(e: *mut LeanObject, i: *mut LeanObject) -> u8 {) ✅
  Line 1347: [extern "lean_expr_lower_loose_bvars"] lowerLooseBVars <- src/rust/runtime/src/kernel_expr.rs:350 (pub unsafe fn lean_expr_lower_loose_bvars() ✅
  Line 1352: [extern "lean_expr_lift_loose_bvars"] liftLooseBVars <- src/rust/runtime/src/kernel_expr.rs:370 (pub unsafe fn lean_expr_lift_loose_bvars() ✅
  Line 1419: [extern "lean_expr_instantiate"] instantiate <- src/rust/runtime/src/kernel_instantiate.rs:908 (pub unsafe fn lean_expr_instantiate() ✅
  Line 1436: [extern "lean_expr_instantiate1"] instantiate1 <- src/rust/runtime/src/kernel_instantiate.rs:890 (pub unsafe fn lean_expr_instantiate1() ✅
  Line 1450: [extern "lean_expr_instantiate_rev"] instantiateRev <- src/rust/runtime/src/kernel_instantiate.rs:943 (pub unsafe fn lean_expr_instantiate_rev() ✅
  Line 1462: [extern "lean_expr_instantiate_range"] instantiateRange <- src/rust/runtime/src/kernel_instantiate.rs:920 (pub unsafe fn lean_expr_instantiate_range() ✅
  Line 1474: [extern "lean_expr_instantiate_rev_range"] instantiateRevRange <- src/rust/runtime/src/kernel_instantiate.rs:955 (pub unsafe fn lean_expr_instantiate_rev_range() ✅
  Line 1484: [extern "lean_expr_abstract"] abstract <- src/rust/runtime/src/kernel_abstract.rs:303 (pub unsafe fn lean_expr_abstract() ✅
  Line 1488: [extern "lean_expr_abstract_range"] abstractRange <- src/rust/runtime/src/kernel_abstract.rs:314 (pub unsafe fn lean_expr_abstract_range() ✅

src/Lean/MetavarContext.lean
  Line 568: [extern "lean_instantiate_level_mvars"] instantiateLevelMVarsImp <- src/rust/runtime/src/library_instantiate_mvars.rs:424 (pub unsafe fn lean_instantiate_level_mvars() ✅
  Line 576: [extern "lean_instantiate_expr_mvars"] instantiateExprMVarsImp <- src/rust/runtime/src/library_instantiate_mvars.rs:1623 (pub unsafe fn lean_instantiate_expr_mvars() ✅

src/Lean/Util/FindExpr.lean
  Line 16: [extern "lean_find_expr"] findImpl <- src/rust/runtime/src/kernel_for_each_fn.rs:326 (pub unsafe fn lean_find_expr(p: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 33: [extern "lean_find_ext_expr"] findExtImpl <- src/rust/runtime/src/kernel_for_each_fn.rs:334 (pub unsafe fn lean_find_ext_expr(p: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject {) ✅

src/Lean/Util/ReplaceExpr.lean
  Line 16: [extern "lean_replace_expr"] replaceImpl <- src/rust/runtime/src/kernel_replace_fn.rs:393 (pub unsafe fn lean_replace_expr(f: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject {) ✅

src/Lean/DocString/Links.lean
  Line 23: [extern "lean_manual_get_root"] getManualRoot <- ❌ (Rust does not define this function)

src/Lean/Setup.lean
  Line 37: [extern "lean_idbg_client_loop"] Idbg.idbgClientLoop <- ❌ (Rust does not define this function)

src/Lean/Environment.lean
  Line 296: [extern "lean_add_decl"] addDeclCore <- src/rust/runtime/src/kernel_environment.rs:30 (pub unsafe fn lean_add_decl() ✅
  Line 307: [extern "lean_add_decl_without_checking"] addDeclWithoutChecking <- src/rust/runtime/src/kernel_environment.rs:53 (pub unsafe fn lean_add_decl_without_checking() ✅
  Line 687: [extern "lean_elab_add_decl"] addDeclCheck <- src/rust/runtime/src/library_elab_environment.rs:82 (pub unsafe fn lean_elab_add_decl() ✅
  Line 691: [extern "lean_elab_add_decl_without_checking"] addDeclWithoutChecking <- src/rust/runtime/src/library_elab_environment.rs:105 (pub unsafe fn lean_elab_add_decl_without_checking() ✅
  Line 756: [extern "lean_is_reserved_name"] isReservedName <- ❌ (Rust does not define this function)
  Line 1797: [extern "lean_get_ir_extra_const_names"] getIRExtraConstNames <- ❌ (Rust does not define this function)
  Line 1855: [extern "lean_ir_export_entries"] exportIREntries <- ❌ (Rust does not define this function)
  Line 1925: [extern "lean_update_env_attributes"] updateEnvAttributes <- ❌ (Rust does not define this function)
  Line 1929: [extern "lean_get_num_attributes"] getNumBuiltinAttributes <- ❌ (Rust does not define this function)
  Line 1932: [extern "lean_run_init_attrs"] runInitAttrs <- ❌ (Rust does not define this function)
  Line 2451: [extern "lean_eval_const"] evalConstCore <- src/rust/runtime/src/library_ir_interpreter.rs:2626 (pub unsafe fn lean_eval_const() ✅
  Line 2455: [extern "lean_eval_check_meta"] evalCheckMeta <- ❌ (Rust does not define this function)
  Line 2719: [extern "lean_kernel_is_def_eq"] isDefEq <- src/rust/runtime/src/kernel_type_checker.rs:5686 (pub unsafe fn lean_kernel_is_def_eq() ✅
  Line 2731: [extern "lean_kernel_whnf"] whnf <- src/rust/runtime/src/kernel_type_checker.rs:5708 (pub unsafe fn lean_kernel_whnf() ✅
  Line 2740: [extern "lean_kernel_check"] check <- src/rust/runtime/src/kernel_type_checker.rs:5728 (pub unsafe fn lean_kernel_check() ✅

src/Lean/MonadEnv.lean
  Line 178: [extern "lean_has_compile_error"] hasCompileError <- ❌ (Rust does not define this function)

src/Lean/Meta/Basic.lean
  Line 777: [extern "lean_whnf"] whnf <- ❌ (Rust does not define this function)
  Line 832: [extern "lean_infer_type"] inferType <- ❌ (Rust does not define this function)
  Line 834: [extern "lean_is_expr_def_eq"] isExprDefEqAux <- ❌ (Rust does not define this function)
  Line 836: [extern "lean_is_level_def_eq"] isLevelDefEqAux <- ❌ (Rust does not define this function)
  Line 838: [extern "lean_synth_pending"] synthPending <- ❌ (Rust does not define this function)
  Line 2525: [extern "lean_checked_assign"] _root_.Lean.MVarId.checkedAssign <- ❌ (Rust does not define this function)

src/Lean/Meta/WHNF.lean
  Line 45: [extern "lean_get_structural_rec_arg_pos"] getStructuralRecArgPos <- ❌ (Rust does not define this function)

src/Lean/Compiler/InitAttr.lean
  Line 32: [extern "lean_run_mod_init_core"] runModInitCore <- src/rust/runtime/src/library_ir_interpreter.rs:2703 (pub unsafe fn lean_run_mod_init_core(sym: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 44: [extern "lean_run_init"] runInit <- src/rust/runtime/src/library_ir_interpreter.rs:2680 (pub unsafe fn lean_run_init() ✅

src/Lean/Meta/Sym/DSimp/DSimpM.lean
  Line 103: [extern "lean_sym_dsimp"] dsimp <- ❌ (Rust does not define this function)

src/Lean/Meta/Match/MatchEqsExt.lean
  Line 50: [extern "lean_get_match_equations_for"] getEquationsFor <- ❌ (Rust does not define this function)
  Line 57: [extern "lean_get_congr_match_equations_for"] genMatchCongrEqns <- ❌ (Rust does not define this function)

src/Lean/Meta/Tactic/Simp/Types.lean
  Line 302: [extern "lean_simp"] simp <- ❌ (Rust does not define this function)
  Line 306: [extern "lean_dsimp"] dsimp <- ❌ (Rust does not define this function)

src/Lean/Meta/Tactic/Grind/Util.lean
  Line 136: [extern "lean_grind_normalize"] normalize <- ❌ (Rust does not define this function)

src/Lean/Meta/Sym/Pattern.lean
  Line 673: [extern "lean_sym_def_eq"] isDefEqMain <- ❌ (Rust does not define this function)

src/Lean/Meta/Sym/Simp/SimpM.lean
  Line 270: [extern "lean_sym_simp"] simp <- ❌ (Rust does not define this function)

src/Lean/PrettyPrinter/Formatter.lean
  Line 238: [extern "lean_mk_antiquot_formatter"] mkAntiquot.formatter' <- ❌ (Rust does not define this function)
  Line 243: [extern "lean_pretty_printer_formatter_interpret_parser_descr"] interpretParserDescr' <- ❌ (Rust does not define this function)

src/Lean/PrettyPrinter/Parenthesizer.lean
  Line 312: [extern "lean_mk_antiquot_parenthesizer"] mkAntiquot.parenthesizer' <- ❌ (Rust does not define this function)
  Line 320: [extern "lean_pretty_printer_parenthesizer_interpret_parser_descr"] interpretParserDescr' <- ❌ (Rust does not define this function)

src/Lean/Compiler/IR/Checker.lean
  Line 15: [extern "lean_get_max_ctor_fields"] getMaxCtorFields <- ❌ (Rust does not define this function)
  Line 19: [extern "lean_get_max_ctor_scalars_size"] getMaxCtorScalarsSize <- ❌ (Rust does not define this function)
  Line 23: [extern "lean_get_max_ctor_tag"] getMaxCtorTag <- ❌ (Rust does not define this function)
  Line 27: [extern "lean_get_usize_size"] getUSizeSize <- ❌ (Rust does not define this function)

src/Lean/Meta/Tactic/Grind/Types.lean
  Line 1432: [extern "lean_grind_mk_eq_proof"] mkEqProof <- ❌ (Rust does not define this function)
  Line 1441: [extern "lean_grind_mk_heq_proof"] mkHEqProof <- ❌ (Rust does not define this function)
  Line 1446: [extern "lean_grind_process_new_facts"] processNewFacts <- ❌ (Rust does not define this function)
  Line 1451: [extern "lean_grind_internalize"] internalize <- ❌ (Rust does not define this function)
  Line 1456: [extern "lean_grind_preprocess"] preprocess <- ❌ (Rust does not define this function)

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Util.lean
  Line 46: [extern "lean_grind_cutsat_mk_var"] mkVar <- ❌ (Rust does not define this function)
  Line 67: [extern "lean_grind_cutsat_assert_eq"] EqCnstr.assert <- ❌ (Rust does not define this function)
  Line 120: [extern "lean_grind_cutsat_assert_le"] LeCnstr.assert <- ❌ (Rust does not define this function)

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Var.lean
  Line 16: [extern "lean_cutsat_propagate_nonlinear"] propagateNonlinearTerm <- ❌ (Rust does not define this function)

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean
  Line 233: [extern "lean_cutsat_eq_cnstr_to_proof"] EqCnstr.toExprProof <- ❌ (Rust does not define this function)

src/Std/Internal/UV/Loop.lean
  Line 36: [extern "lean_uv_event_loop_configure"] configure <- src/rust/runtime/src/runtime_event_loop.rs:94 (pub unsafe fn lean_uv_event_loop_configure(options: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 42: [extern "lean_uv_event_loop_alive"] alive <- src/rust/runtime/src/runtime_event_loop.rs:122 (pub unsafe fn lean_uv_event_loop_alive() -> u8 {) ✅

src/Std/Net/Addr.lean
  Line 108: [extern "lean_uv_pton_v4"] ofString <- src/rust/runtime/src/runtime_net_addr.rs:201 (pub unsafe fn lean_uv_pton_v4(str_obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 114: [extern "lean_uv_ntop_v4"] toString <- src/rust/runtime/src/runtime_net_addr.rs:215 (pub unsafe fn lean_uv_ntop_v4(ipv4_addr: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 147: [extern "lean_uv_pton_v6"] ofString <- src/rust/runtime/src/runtime_net_addr.rs:228 (pub unsafe fn lean_uv_pton_v6(str_obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 154: [extern "lean_uv_ntop_v6"] toString <- src/rust/runtime/src/runtime_net_addr.rs:242 (pub unsafe fn lean_uv_ntop_v6(ipv6_addr: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 257: [extern "lean_uv_interface_addresses"] interfaceAddresses <- src/rust/runtime/src/runtime_net_addr.rs:255 (pub unsafe fn lean_uv_interface_addresses() -> *mut LeanObject {) ✅

src/Std/Internal/UV/System.lean
  Line 98: [extern "lean_uv_get_process_title"] getProcessTitle <- src/rust/runtime/src/runtime_system.rs:70 (pub unsafe fn lean_uv_get_process_title() -> *mut LeanObject {) ✅
  Line 104: [extern "lean_uv_set_process_title"] setProcessTitle <- src/rust/runtime/src/runtime_system.rs:82 (pub unsafe fn lean_uv_set_process_title(title: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 110: [extern "lean_uv_uptime"] uptime <- src/rust/runtime/src/runtime_system.rs:97 (pub unsafe fn lean_uv_uptime() -> *mut LeanObject {) ✅
  Line 116: [extern "lean_uv_os_getpid"] osGetPid <- src/rust/runtime/src/runtime_system.rs:115 (pub unsafe fn lean_uv_os_getpid() -> *mut LeanObject {) ✅
  Line 122: [extern "lean_uv_os_getppid"] osGetPpid <- src/rust/runtime/src/runtime_system.rs:120 (pub unsafe fn lean_uv_os_getppid() -> *mut LeanObject {) ✅
  Line 128: [extern "lean_uv_cpu_info"] cpuInfo <- src/rust/runtime/src/runtime_system.rs:125 (pub unsafe fn lean_uv_cpu_info() -> *mut LeanObject {) ✅
  Line 134: [extern "lean_uv_cwd"] cwd <- src/rust/runtime/src/runtime_system.rs:164 (pub unsafe fn lean_uv_cwd() -> *mut LeanObject {) ✅
  Line 140: [extern "lean_uv_chdir"] chdir <- src/rust/runtime/src/runtime_system.rs:177 (pub unsafe fn lean_uv_chdir(path: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 146: [extern "lean_uv_os_homedir"] osHomedir <- src/rust/runtime/src/runtime_system.rs:194 (pub unsafe fn lean_uv_os_homedir() -> *mut LeanObject {) ✅
  Line 152: [extern "lean_uv_os_tmpdir"] osTmpdir <- src/rust/runtime/src/runtime_system.rs:207 (pub unsafe fn lean_uv_os_tmpdir() -> *mut LeanObject {) ✅
  Line 158: [extern "lean_uv_os_get_passwd"] osGetPasswd <- src/rust/runtime/src/runtime_system.rs:220 (pub unsafe fn lean_uv_os_get_passwd() -> *mut LeanObject {) ✅
  Line 164: [extern "lean_uv_os_get_group"] osGetGroup <- src/rust/runtime/src/runtime_system.rs:263 (pub unsafe fn lean_uv_os_get_group(gid: u64) -> *mut LeanObject {) ✅
  Line 170: [extern "lean_uv_os_environ"] osEnviron <- src/rust/runtime/src/runtime_system.rs:308 (pub unsafe fn lean_uv_os_environ() -> *mut LeanObject {) ✅
  Line 176: [extern "lean_uv_os_getenv"] osGetenv <- src/rust/runtime/src/runtime_system.rs:338 (pub unsafe fn lean_uv_os_getenv(name: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 182: [extern "lean_uv_os_setenv"] osSetenv <- src/rust/runtime/src/runtime_system.rs:381 (pub unsafe fn lean_uv_os_setenv() ✅
  Line 188: [extern "lean_uv_os_unsetenv"] osUnsetenv <- src/rust/runtime/src/runtime_system.rs:403 (pub unsafe fn lean_uv_os_unsetenv(name: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 194: [extern "lean_uv_os_gethostname"] osGetHostname <- src/rust/runtime/src/runtime_system.rs:418 (pub unsafe fn lean_uv_os_gethostname() -> *mut LeanObject {) ✅
  Line 200: [extern "lean_uv_os_getpriority"] osGetPriority <- src/rust/runtime/src/runtime_system.rs:432 (pub unsafe fn lean_uv_os_getpriority(pid: u64) -> *mut LeanObject {) ✅
  Line 206: [extern "lean_uv_os_setpriority"] osSetPriority <- src/rust/runtime/src/runtime_system.rs:443 (pub unsafe fn lean_uv_os_setpriority(pid: u64, priority: i64) -> *mut LeanObject {) ✅
  Line 212: [extern "lean_uv_os_uname"] osUname <- src/rust/runtime/src/runtime_system.rs:453 (pub unsafe fn lean_uv_os_uname() -> *mut LeanObject {) ✅
  Line 218: [extern "lean_uv_hrtime"] hrtime <- src/rust/runtime/src/runtime_system.rs:476 (pub unsafe fn lean_uv_hrtime() -> *mut LeanObject {) ✅
  Line 224: [extern "lean_uv_random"] random <- src/rust/runtime/src/runtime_system.rs:481 (pub unsafe fn lean_uv_random(size: u64) -> *mut LeanObject {) ✅
  Line 230: [extern "lean_uv_getrusage"] getrusage <- src/rust/runtime/src/runtime_system.rs:552 (pub unsafe fn lean_uv_getrusage() -> *mut LeanObject {) ✅
  Line 236: [extern "lean_uv_exepath"] exePath <- src/rust/runtime/src/runtime_system.rs:582 (pub unsafe fn lean_uv_exepath() -> *mut LeanObject {) ✅
  Line 242: [extern "lean_uv_get_free_memory"] freeMemory <- src/rust/runtime/src/runtime_system.rs:595 (pub unsafe fn lean_uv_get_free_memory() -> *mut LeanObject {) ✅
  Line 248: [extern "lean_uv_get_total_memory"] totalMemory <- src/rust/runtime/src/runtime_system.rs:600 (pub unsafe fn lean_uv_get_total_memory() -> *mut LeanObject {) ✅
  Line 254: [extern "lean_uv_get_constrained_memory"] constrainedMemory <- src/rust/runtime/src/runtime_system.rs:605 (pub unsafe fn lean_uv_get_constrained_memory() -> *mut LeanObject {) ✅
  Line 260: [extern "lean_uv_get_available_memory"] availableMemory <- src/rust/runtime/src/runtime_system.rs:610 (pub unsafe fn lean_uv_get_available_memory() -> *mut LeanObject {) ✅

src/Std/Internal/UV/Signal.lean
  Line 46: [extern "lean_uv_signal_mk"] mk <- src/rust/runtime/src/runtime_signal.rs:86 (pub unsafe fn lean_uv_signal_mk(signum_obj: u32, repeating: u8) -> *mut LeanObject {) ✅
  Line 67: [extern "lean_uv_signal_next"] next <- src/rust/runtime/src/runtime_signal.rs:189 (pub unsafe fn lean_uv_signal_next(obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 77: [extern "lean_uv_signal_stop"] stop <- src/rust/runtime/src/runtime_signal.rs:243 (pub unsafe fn lean_uv_signal_stop(obj: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 86: [extern "lean_uv_signal_cancel"] cancel <- src/rust/runtime/src/runtime_signal.rs:271 (pub unsafe fn lean_uv_signal_cancel(obj: *mut LeanObject) -> *mut LeanObject {) ✅

src/Std/Internal/UV/TCP.lean
  Line 36: [extern "lean_uv_tcp_new"] new <- src/rust/runtime/src/runtime_tcp.rs:135 (pub unsafe fn lean_uv_tcp_new() -> *mut LeanObject {) ✅
  Line 42: [extern "lean_uv_tcp_connect"] connect <- src/rust/runtime/src/runtime_tcp.rs:175 (pub unsafe fn lean_uv_tcp_connect() ✅
  Line 48: [extern "lean_uv_tcp_send"] send <- src/rust/runtime/src/runtime_tcp.rs:245 (pub unsafe fn lean_uv_tcp_send() ✅
  Line 58: [extern "lean_uv_tcp_recv"] recv <- src/rust/runtime/src/runtime_tcp.rs:348 (pub unsafe fn lean_uv_tcp_recv(socket: *mut LeanObject, buffer_size: u64) -> *mut LeanObject {) ✅
  Line 66: [extern "lean_uv_tcp_wait_readable"] waitReadable <- src/rust/runtime/src/runtime_tcp.rs:428 (pub unsafe fn lean_uv_tcp_wait_readable(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 77: [extern "lean_uv_tcp_cancel_recv"] cancelRecv <- src/rust/runtime/src/runtime_tcp.rs:496 (pub unsafe fn lean_uv_tcp_cancel_recv(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 83: [extern "lean_uv_tcp_bind"] bind <- src/rust/runtime/src/runtime_tcp.rs:524 (pub unsafe fn lean_uv_tcp_bind() ✅
  Line 89: [extern "lean_uv_tcp_listen"] listen <- src/rust/runtime/src/runtime_tcp.rs:544 (pub unsafe fn lean_uv_tcp_listen(socket: *mut LeanObject, backlog: i32) -> *mut LeanObject {) ✅
  Line 95: [extern "lean_uv_tcp_accept"] accept <- src/rust/runtime/src/runtime_tcp.rs:598 (pub unsafe fn lean_uv_tcp_accept(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 101: [extern "lean_uv_tcp_try_accept"] tryAccept <- src/rust/runtime/src/runtime_tcp.rs:639 (pub unsafe fn lean_uv_tcp_try_accept(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 107: [extern "lean_uv_tcp_cancel_accept"] cancelAccept <- src/rust/runtime/src/runtime_tcp.rs:671 (pub unsafe fn lean_uv_tcp_cancel_accept(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 113: [extern "lean_uv_tcp_shutdown"] shutdown <- src/rust/runtime/src/runtime_tcp.rs:697 (pub unsafe fn lean_uv_tcp_shutdown(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 119: [extern "lean_uv_tcp_getpeername"] getPeerName <- src/rust/runtime/src/runtime_tcp.rs:758 (pub unsafe fn lean_uv_tcp_getpeername(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 125: [extern "lean_uv_tcp_getsockname"] getSockName <- src/rust/runtime/src/runtime_tcp.rs:779 (pub unsafe fn lean_uv_tcp_getsockname(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 131: [extern "lean_uv_tcp_nodelay"] noDelay <- src/rust/runtime/src/runtime_tcp.rs:800 (pub unsafe fn lean_uv_tcp_nodelay(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 137: [extern "lean_uv_tcp_keepalive"] keepAlive <- src/rust/runtime/src/runtime_tcp.rs:814 (pub unsafe fn lean_uv_tcp_keepalive() ✅

src/Std/Internal/UV/UDP.lean
  Line 35: [extern "lean_uv_udp_new"] new <- src/rust/runtime/src/runtime_udp.rs:116 (pub unsafe fn lean_uv_udp_new() -> *mut LeanObject {) ✅
  Line 42: [extern "lean_uv_udp_bind"] bind <- src/rust/runtime/src/runtime_udp.rs:152 (pub unsafe fn lean_uv_udp_bind() ✅
  Line 49: [extern "lean_uv_udp_connect"] connect <- src/rust/runtime/src/runtime_udp.rs:176 (pub unsafe fn lean_uv_udp_connect() ✅
  Line 56: [extern "lean_uv_udp_send"] send <- src/rust/runtime/src/runtime_udp.rs:196 (pub unsafe fn lean_uv_udp_send() ✅
  Line 64: [extern "lean_uv_udp_recv"] recv <- src/rust/runtime/src/runtime_udp.rs:325 (pub unsafe fn lean_uv_udp_recv(socket: *mut LeanObject, buffer_size: u64) -> *mut LeanObject {) ✅
  Line 71: [extern "lean_uv_udp_wait_readable"] waitReadable <- src/rust/runtime/src/runtime_udp.rs:418 (pub unsafe fn lean_uv_udp_wait_readable(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 81: [extern "lean_uv_udp_cancel_recv"] cancelRecv <- src/rust/runtime/src/runtime_udp.rs:490 (pub unsafe fn lean_uv_udp_cancel_recv(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 89: [extern "lean_uv_udp_getpeername"] getPeerName <- src/rust/runtime/src/runtime_udp.rs:520 (pub unsafe fn lean_uv_udp_getpeername(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 95: [extern "lean_uv_udp_getsockname"] getSockName <- src/rust/runtime/src/runtime_udp.rs:541 (pub unsafe fn lean_uv_udp_getsockname(socket: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 101: [extern "lean_uv_udp_set_broadcast"] setBroadcast <- src/rust/runtime/src/runtime_udp.rs:562 (pub unsafe fn lean_uv_udp_set_broadcast() ✅
  Line 107: [extern "lean_uv_udp_set_multicast_loop"] setMulticastLoop <- src/rust/runtime/src/runtime_udp.rs:579 (pub unsafe fn lean_uv_udp_set_multicast_loop() ✅
  Line 113: [extern "lean_uv_udp_set_multicast_ttl"] setMulticastTTL <- src/rust/runtime/src/runtime_udp.rs:596 (pub unsafe fn lean_uv_udp_set_multicast_ttl() ✅
  Line 120: [extern "lean_uv_udp_set_membership"] setMembership <- src/rust/runtime/src/runtime_udp.rs:615 (pub unsafe fn lean_uv_udp_set_membership() ✅
  Line 126: [extern "lean_uv_udp_set_multicast_interface"] setMulticastInterface <- src/rust/runtime/src/runtime_udp.rs:662 (pub unsafe fn lean_uv_udp_set_multicast_interface() ✅
  Line 132: [extern "lean_uv_udp_set_ttl"] setTTL <- src/rust/runtime/src/runtime_udp.rs:687 (pub unsafe fn lean_uv_udp_set_ttl(socket: *mut LeanObject, ttl: u32) -> *mut LeanObject {) ✅

src/Std/Internal/UV/DNS.lean
  Line 25: [extern "lean_uv_dns_get_info"] getAddrInfo <- src/rust/runtime/src/runtime_dns.rs:60 (pub unsafe fn lean_uv_dns_get_info() ✅
  Line 32: [extern "lean_uv_dns_get_name"] getNameInfo <- src/rust/runtime/src/runtime_dns.rs:167 (pub unsafe fn lean_uv_dns_get_name(addr: *mut LeanObject) -> *mut LeanObject {) ✅

src/Std/Sync/RecursiveMutex.lean
  Line 27: [extern "lean_io_baserecmutex_new"] BaseRecursiveMutex.new <- src/rust/runtime/src/runtime_mutex.rs:62 (pub unsafe fn lean_io_baserecmutex_new() -> *mut LeanObject {) ✅
  Line 34: [extern "lean_io_baserecmutex_lock"] BaseRecursiveMutex.lock <- src/rust/runtime/src/runtime_mutex.rs:66 (pub unsafe fn lean_io_baserecmutex_lock(mtx: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 44: [extern "lean_io_baserecmutex_try_lock"] BaseRecursiveMutex.tryLock <- src/rust/runtime/src/runtime_mutex.rs:71 (pub unsafe fn lean_io_baserecmutex_try_lock(mtx: *mut LeanObject) -> u8 {) ✅
  Line 54: [extern "lean_io_baserecmutex_unlock"] BaseRecursiveMutex.unlock <- src/rust/runtime/src/runtime_mutex.rs:75 (pub unsafe fn lean_io_baserecmutex_unlock(mtx: *mut LeanObject) -> *mut LeanObject {) ✅

src/Std/Sync/SharedMutex.lean
  Line 27: [extern "lean_io_basesharedmutex_new"] BaseSharedMutex.new <- src/rust/runtime/src/runtime_mutex.rs:80 (pub unsafe fn lean_io_basesharedmutex_new() -> *mut LeanObject {) ✅
  Line 37: [extern "lean_io_basesharedmutex_write"] BaseSharedMutex.write <- src/rust/runtime/src/runtime_mutex.rs:84 (pub unsafe fn lean_io_basesharedmutex_write(mtx: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 47: [extern "lean_io_basesharedmutex_try_write"] BaseSharedMutex.tryWrite <- src/rust/runtime/src/runtime_mutex.rs:89 (pub unsafe fn lean_io_basesharedmutex_try_write(mtx: *mut LeanObject) -> u8 {) ✅
  Line 56: [extern "lean_io_basesharedmutex_unlock_write"] BaseSharedMutex.unlockWrite <- src/rust/runtime/src/runtime_mutex.rs:93 (pub unsafe fn lean_io_basesharedmutex_unlock_write(mtx: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 67: [extern "lean_io_basesharedmutex_read"] BaseSharedMutex.read <- src/rust/runtime/src/runtime_mutex.rs:98 (pub unsafe fn lean_io_basesharedmutex_read(mtx: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 77: [extern "lean_io_basesharedmutex_try_read"] BaseSharedMutex.tryRead <- src/rust/runtime/src/runtime_mutex.rs:103 (pub unsafe fn lean_io_basesharedmutex_try_read(mtx: *mut LeanObject) -> u8 {) ✅
  Line 86: [extern "lean_io_basesharedmutex_unlock_read"] BaseSharedMutex.unlockRead <- src/rust/runtime/src/runtime_mutex.rs:107 (pub unsafe fn lean_io_basesharedmutex_unlock_read(mtx: *mut LeanObject) -> *mut LeanObject {) ✅

src/Std/Time/DateTime/Timestamp.lean
  Line 70: [extern "lean_get_current_time"] now <- src/rust/runtime/src/base.rs:1230 (pub unsafe fn lean_get_current_time() -> *mut LeanObject {) ✅

src/Std/Time/Zoned/Database/Windows.lean
  Line 26: [extern "lean_windows_get_next_transition"] getNextTransition <- ❌ (Rust does not define this function)
  Line 32: [extern "lean_get_windows_local_timezone_id_at"] getLocalTimeZoneIdentifierAt <- ❌ (Rust does not define this function)

src/Lean/Elab/Tactic/Try.lean
  Line 661: [extern "lean_eval_suggest_tactic"] evalSuggest <- ❌ (Rust does not define this function)

src/Lean/Shell.lean
  Line 31: [extern "lean_decode_lossy_utf8"] decodeLossyUTF8 <- src/rust/runtime/src/runtime_object_string.rs:209 (pub unsafe fn lean_decode_lossy_utf8(a: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 35: [extern "lean_eval_main"] runMain <- src/rust/runtime/src/library_ir_interpreter.rs:2601 (pub unsafe fn lean_eval_main() ✅
  Line 42: [extern "lean_init_llvm"] initLLVM <- src/rust/runtime/src/library_llvm.rs:38 (pub unsafe fn lean_init_llvm() -> *mut LeanObject {) ✅
  Line 49: [extern "lean_emit_llvm"] emitLLVM <- src/rust/runtime/src/library_llvm.rs:42 (pub unsafe fn lean_emit_llvm() ✅
  Line 53: [extern "lean_internal_has_address_sanitizer"] Internal.hasAddressSanitizer <- src/rust/runtime/src/base.rs:1037 (pub fn lean_internal_has_address_sanitizer(_: *mut LeanObject) -> u8 {) ✅
  Line 57: [extern "lean_internal_is_multi_thread"] Internal.isMultiThread <- src/rust/runtime/src/base.rs:1041 (pub fn lean_internal_is_multi_thread(_: *mut LeanObject) -> u8 {) ✅
  Line 61: [extern "lean_internal_is_debug"] Internal.isDebug <- src/rust/runtime/src/base.rs:1045 (pub fn lean_internal_is_debug(_: *mut LeanObject) -> u8 {) ✅
  Line 65: [extern "lean_internal_get_build_type"] Internal.getBuildType <- src/rust/runtime/src/base.rs:1049 (pub unsafe fn lean_internal_get_build_type(_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 72: [extern "lean_internal_get_default_max_memory"] Internal.getDefaultMaxMemory <- src/rust/runtime/src/runtime_memory.rs:38 (pub fn lean_internal_get_default_max_memory() -> *mut LeanObject {) ✅
  Line 76: [extern "lean_internal_set_max_memory"] Internal.setMaxMemory <- src/rust/runtime/src/runtime_memory.rs:47 (pub fn lean_internal_set_max_memory(max: usize) -> *mut LeanObject {) ✅
  Line 83: [extern "lean_internal_get_default_max_heartbeat"] Internal.getDefaultMaxHeartbeat <- src/rust/runtime/src/runtime_interrupt.rs:83 (pub fn lean_internal_get_default_max_heartbeat() -> *mut LeanObject {) ✅
  Line 87: [extern "lean_internal_set_max_heartbeat"] Internal.setMaxHeartbeat <- src/rust/runtime/src/runtime_interrupt.rs:89 (pub fn lean_internal_set_max_heartbeat(max: usize) -> *mut LeanObject {) ✅
  Line 91: [extern "lean_internal_get_default_verbose"] Internal.getDefaultVerbose <- src/rust/runtime/src/base.rs:973 (pub fn lean_internal_get_default_verbose(_: *mut LeanObject) -> u8 {) ✅
  Line 95: [extern "lean_internal_set_exit_on_panic"] Internal.setExitOnPanic <- src/rust/runtime/src/runtime_object_panic.rs:37 (pub unsafe fn lean_internal_set_exit_on_panic(exit: u8) -> *mut LeanObject {) ✅
  Line 99: [extern "lean_internal_set_thread_stack_size"] Internal.setThreadStackSize <- src/rust/runtime/src/runtime_thread.rs:87 (pub unsafe fn lean_internal_set_thread_stack_size(sz: usize) -> *mut LeanObject {) ✅
  Line 103: [extern "lean_internal_enable_debug"] Internal.enableDebug <- src/rust/runtime/src/runtime_debug.rs:67 (pub unsafe fn lean_internal_enable_debug(tag: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 202: [extern "lean_internal_get_default_options"] Internal.getDefaultOptions <- src/rust/runtime/src/base.rs:977 (pub unsafe fn lean_internal_get_default_options(_: *mut LeanObject) -> *mut LeanObject {) ✅
  Line 211: [extern "lean_internal_get_believer_trust_level"] Internal.getBelieverTrustLevel <- src/rust/runtime/src/library_elab_environment.rs:116 (pub unsafe fn lean_internal_get_believer_trust_level(_io: *mut LeanObject) -> u32 {) ✅
  Line 219: [extern "lean_internal_get_hardware_concurrency"] Internal.getHardwareCurrency <- src/rust/runtime/src/base.rs:500 (pub fn lean_internal_get_hardware_concurrency(_: *mut LeanObject) -> u32 {) ✅

src/lake/Lake/Load/Lean/Elab.lean
  Line 96: [extern "lake_environment_add"] addToEnv <- src/rust/lake_ffi/src/ffi/Lake/Load/Lean/Elab.rs:4 (pub use gen_lean::r#gen::Lean::Environment::lake_environment_add;) 🔍 (Referenced in Rust)

# list of all functions that rust imports from lean

src/Init/Prelude.lean
  Line 4729: @[export lean_name_mk_string] mkStr -> src/rust/leanh/src/in_emit_rust.rs:312 -> 🛠️ (Defined in Rust: `pub unsafe fn lean_name_mk_string(`, should be `use crate::Init::Prelude::lean_name_mk_string;`)
  Line 4736: @[export lean_name_mk_numeral] mkNum -> src/rust/runtime/src/kernel_trace.rs:29 -> 🔌 (FFI Declaration: `fn lean_name_mk_numeral(prefix: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 5610: @[export lean_erase_macro_scopes] Name.eraseMacroScopes -> ❌ (Not found in Rust, should be `use crate::Init::Prelude::lean_erase_macro_scopes;`)
  Line 5621: @[export lean_simp_macro_scopes] Name.simpMacroScopes -> ❌ (Not found in Rust, should be `use crate::Init::Prelude::lean_simp_macro_scopes;`)

src/Lean/PrivateName.lean
  Line 37: @[export lean_is_private_name] isPrivateNameExport -> ❌ (Not found in Rust, should be `use crate::Lean::PrivateName::lean_is_private_name;`)
  Line 62: @[export lean_private_to_user_name] privateToUserName -> ❌ (Not found in Rust, should be `use crate::Lean::PrivateName::lean_private_to_user_name;`)
  Line 75: @[export lean_private_prefix] privatePrefix -> ❌ (Not found in Rust, should be `use crate::Lean::PrivateName::lean_private_prefix;`)

src/Init/Data/List/ToArrayImpl.lean
  Line 35: @[export lean_list_to_array] List.toArrayImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::List::ToArrayImpl::lean_list_to_array;`)

src/Init/Data/Array/Basic.lean
  Line 1436: @[export lean_array_to_list_impl] toListImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::Array::Basic::lean_array_to_list_impl;`)

src/Init/Meta/Defs.lean
  Line 152: @[export lean_is_inaccessible_user_name] isInaccessibleUserName -> ❌ (Not found in Rust, should be `use crate::Init::Meta::Defs::lean_is_inaccessible_user_name;`)
  Line 316: @[export lean_name_append_after] appendAfter -> ❌ (Not found in Rust, should be `use crate::Init::Meta::Defs::lean_name_append_after;`)
  Line 322: @[export lean_name_append_index_after] appendIndexAfter -> src/rust/runtime/src/kernel_type_checker.rs:6511 -> 🔌 (FFI Declaration: `fn lean_name_append_index_after(n: *mut LeanObject, i: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 328: @[export lean_name_append_before] appendBefore -> ❌ (Not found in Rust, should be `use crate::Init::Meta::Defs::lean_name_append_before;`)
  Line 750: @[export lean_mk_syntax_ident] mkIdent -> ❌ (Not found in Rust, should be `use crate::Init::Meta::Defs::lean_mk_syntax_ident;`)

src/Init/Data/OfScientific.lean
  Line 71: @[export lean_float_of_nat] Float.ofNat -> src/rust/runtime/src/library_ir_interpreter.rs:29 -> 🔌 (FFI Declaration: `fn lean_float_of_nat(a: *mut LeanObject) -> f64;`) ✅
  Line 116: @[export lean_float32_of_nat] Float32.ofNat -> src/rust/runtime/src/library_ir_interpreter.rs:30 -> 🔌 (FFI Declaration: `fn lean_float32_of_nat(a: *mut LeanObject) -> f32;`) ✅

src/Init/Data/String/PosRaw.lean
  Line 32: @[export lean_string_pos_sub] Pos.Internal.subImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::PosRaw::lean_string_pos_sub;`)
  Line 306: @[export lean_string_pos_min] Pos.Raw.Internal.minImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::PosRaw::lean_string_pos_min;`)

src/Init/Data/String/Defs.lean
  Line 222: @[export lean_string_pushn] Internal.pushnImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Defs::lean_string_pushn;`)
  Line 239: @[export lean_string_isempty] Internal.isEmptyImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Defs::lean_string_isempty;`)
  Line 271: @[export lean_string_intercalate] Internal.intercalateImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Defs::lean_string_intercalate;`)

src/Init/Data/String/Basic.lean
  Line 3056: @[export lean_string_offsetofpos] Internal.offsetOfPosImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Basic::lean_string_offsetofpos;`)

src/Init/Data/String/Iterate.lean
  Line 474: @[export lean_string_foldl] Internal.foldlImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Iterate::lean_string_foldl;`)

src/Init/Data/String/Modify.lean
  Line 249: @[export lean_string_capitalize] Internal.capitalizeImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Modify::lean_string_capitalize;`)

src/Init/Data/String/Search.lean
  Line 194: @[export lean_string_posof] Internal.posOfImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Search::lean_string_posof;`)
  Line 303: @[export lean_string_contains] Internal.containsImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Search::lean_string_contains;`)
  Line 310: @[export lean_string_any] Internal.anyImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Search::lean_string_any;`)
  Line 472: @[export lean_string_front] Internal.frontImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Search::lean_string_front;`)

src/Init/Data/String/Substring.lean
  Line 51: @[export lean_substring_isempty] Internal.isEmptyImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_isempty;`)
  Line 61: @[export lean_substring_tostring] Internal.toStringImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_tostring;`)
  Line 76: @[export lean_substring_get] Internal.getImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_get;`)
  Line 113: @[export lean_substring_prev] Internal.prevImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_prev;`)
  Line 150: @[export lean_substring_front] Internal.frontImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_front;`)
  Line 170: @[export lean_substring_drop] Internal.dropImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_drop;`)
  Line 222: @[export lean_substring_extract] Internal.extractImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_extract;`)
  Line 289: @[export lean_substring_all] Internal.allImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_all;`)
  Line 317: @[export lean_substring_takewhile] Internal.takeWhileImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_takewhile;`)
  Line 462: @[export lean_substring_beq] Internal.beqImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::Substring::lean_substring_beq;`)

src/Init/Data/String/TakeDrop.lean
  Line 45: @[export lean_string_drop] Internal.dropImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::TakeDrop::lean_string_drop;`)
  Line 75: @[export lean_string_dropright] Internal.dropRightImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::TakeDrop::lean_string_dropright;`)
  Line 322: @[export lean_string_isprefixof] Internal.isPrefixOfImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::TakeDrop::lean_string_isprefixof;`)
  Line 445: @[export lean_string_trim] Internal.trimImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::TakeDrop::lean_string_trim;`)
  Line 466: @[export lean_string_nextwhile] Internal.nextWhileImpl -> ❌ (Not found in Rust, should be `use crate::Init::Data::String::TakeDrop::lean_string_nextwhile;`)

src/Lean/Data/Name.lean
  Line 21: @[export lean_name_hash_exported] hashEx -> ❌ (Not found in Rust, should be `use crate::Lean::Data::Name::lean_name_hash_exported;`)

src/Lean/Data/KVMap.lean
  Line 27: @[export lean_data_value_beq] DataValue.beqExp -> src/rust/runtime/src/kernel_expr_eq_fn.rs:52 -> 🔌 (FFI Declaration: `fn lean_data_value_beq(a: *mut LeanObject, b: *mut LeanObject) -> u8;`) ✅
  Line 31: @[export lean_mk_bool_data_value] mkBoolDataValueEx -> ❌ (Not found in Rust, should be `use crate::Lean::Data::KVMap::lean_mk_bool_data_value;`)
  Line 32: @[export lean_data_value_bool] DataValue.getBoolEx -> ❌ (Not found in Rust, should be `use crate::Lean::Data::KVMap::lean_data_value_bool;`)
  Line 45: @[export lean_data_value_to_string] DataValue.str -> ❌ (Not found in Rust, should be `use crate::Lean::Data::KVMap::lean_data_value_to_string;`)

src/Init/System/IOError.lean
  Line 150: @[export lean_mk_io_user_error] IO.userError -> src/rust/runtime/src/base.rs:25 -> 🔌 (FFI Declaration: `pub fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 158: @[export lean_mk_io_error_already_exists_file] mkAlreadyExistsFile -> src/rust/runtime/src/runtime_io_error.rs:15 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_already_exists_file(`) ✅
  Line 162: @[export lean_mk_io_error_eof] mkEofError -> ❌ (Not found in Rust, should be `use crate::Init::System::IOError::lean_mk_io_error_eof;`)
  Line 166: @[export lean_mk_io_error_inappropriate_type_file] mkInappropriateTypeFile -> src/rust/runtime/src/runtime_io_error.rs:32 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_inappropriate_type_file(`) ✅
  Line 170: @[export lean_mk_io_error_interrupted] mkInterrupted -> src/rust/runtime/src/runtime_io_error.rs:37 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_interrupted(`) ✅
  Line 174: @[export lean_mk_io_error_invalid_argument_file] mkInvalidArgumentFile -> src/rust/runtime/src/base.rs:31 -> 🔌 (FFI Declaration: `pub fn lean_mk_io_error_invalid_argument_file(`) ✅
  Line 178: @[export lean_mk_io_error_no_file_or_directory] mkNoFileOrDirectory -> src/rust/runtime/src/runtime_io_error.rs:42 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_no_file_or_directory(`) ✅
  Line 182: @[export lean_mk_io_error_no_such_thing_file] mkNoSuchThingFile -> src/rust/runtime/src/runtime_io_error.rs:49 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_no_such_thing_file(`) ✅
  Line 186: @[export lean_mk_io_error_permission_denied_file] mkPermissionDeniedFile -> src/rust/runtime/src/runtime_io_error.rs:59 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_permission_denied_file(`) ✅
  Line 190: @[export lean_mk_io_error_resource_exhausted_file] mkResourceExhaustedFile -> src/rust/runtime/src/runtime_io_error.rs:74 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_resource_exhausted_file(`) ✅
  Line 194: @[export lean_mk_io_error_unsupported_operation] mkUnsupportedOperation -> src/rust/runtime/src/runtime_io_error.rs:88 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_unsupported_operation(`) ✅
  Line 198: @[export lean_mk_io_error_resource_exhausted] mkResourceExhausted -> src/rust/runtime/src/runtime_io_error.rs:70 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_resource_exhausted(`) ✅
  Line 202: @[export lean_mk_io_error_already_exists] mkAlreadyExists -> src/rust/runtime/src/runtime_io_error.rs:11 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_already_exists(`) ✅
  Line 206: @[export lean_mk_io_error_inappropriate_type] mkInappropriateType -> src/rust/runtime/src/runtime_io_error.rs:28 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_inappropriate_type(`) ✅
  Line 210: @[export lean_mk_io_error_no_such_thing] mkNoSuchThing -> src/rust/runtime/src/runtime_io_error.rs:47 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_no_such_thing(errnum: u32, details: *mut LeanObject)`) ✅
  Line 214: @[export lean_mk_io_error_resource_vanished] mkResourceVanished -> src/rust/runtime/src/runtime_io_error.rs:79 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_resource_vanished(`) ✅
  Line 218: @[export lean_mk_io_error_resource_busy] mkResourceBusy -> src/rust/runtime/src/runtime_io_error.rs:68 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_resource_busy(errnum: u32, details: *mut LeanObject)`) ✅
  Line 222: @[export lean_mk_io_error_invalid_argument] mkInvalidArgument -> src/rust/runtime/src/base.rs:26 -> 🔌 (FFI Declaration: `pub fn lean_mk_io_error_invalid_argument(`) ✅
  Line 226: @[export lean_mk_io_error_other_error] mkOtherError -> src/rust/runtime/src/runtime_io_error.rs:54 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_other_error(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 230: @[export lean_mk_io_error_permission_denied] mkPermissionDenied -> src/rust/runtime/src/runtime_io_error.rs:55 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_permission_denied(`) ✅
  Line 234: @[export lean_mk_io_error_hardware_fault] mkHardwareFault -> src/rust/runtime/src/runtime_io_error.rs:20 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_hardware_fault(`) ✅
  Line 238: @[export lean_mk_io_error_unsatisfied_constraints] mkUnsatisfiedConstraints -> src/rust/runtime/src/runtime_io_error.rs:84 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_unsatisfied_constraints(`) ✅
  Line 242: @[export lean_mk_io_error_illegal_operation] mkIllegalOperation -> src/rust/runtime/src/runtime_io_error.rs:24 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_illegal_operation(`) ✅
  Line 246: @[export lean_mk_io_error_protocol_error] mkProtocolError -> src/rust/runtime/src/runtime_io_error.rs:64 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_protocol_error(`) ✅
  Line 250: @[export lean_mk_io_error_time_expired] mkTimeExpired -> src/rust/runtime/src/runtime_io_error.rs:83 -> 🔌 (FFI Declaration: `fn lean_mk_io_error_time_expired(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 271: @[export lean_io_error_to_string] toString -> src/rust/leanh/src/in_emit_rust.rs:804 -> 🛠️ (Defined in Rust: `pub unsafe fn lean_io_error_to_string(mut _v_x_1214_: *mut LeanObject) -> *mut LeanObject {`, should be `use crate::Init::System::IOError::lean_io_error_to_string;`)

src/Init/System/IO.lean
  Line 1294: @[export lean_io_eprint] eprintAux -> ❌ (Not found in Rust, should be `use crate::Init::System::IO::lean_io_eprint;`)
  Line 1298: @[export lean_io_eprintln] eprintlnAux -> src/rust/leanh/src/runtime_object_panic.rs:8 -> 🛠️ (Defined in Rust: `pub unsafe fn lean_io_eprintln(mut v_s_9609_: *mut LeanObject) -> *mut LeanObject {`, should be `use crate::Init::System::IO::lean_io_eprintln;`)
  Line 1682: @[export lean_stream_of_handle] ofHandle -> src/rust/leanh/src/runtime_io_stream.rs:25 -> 🛠️ (Defined in Rust: `pub unsafe fn lean_stream_of_handle(mut v_h_10248_: *mut LeanObject) -> *mut LeanObject {`, should be `use crate::Init::System::IO::lean_stream_of_handle;`)

src/Lean/Util/Path.lean
  Line 112: @[export lean_init_search_path] initSearchPathInternal -> src/rust/lean_shell/src/lib.rs:26 -> ⚠️ (Wrong import: `use runtime::lean_init_search_path;`, should be `use crate::Lean::Util::Path::lean_init_search_path;`)

src/Init/System/CancelToken.lean
  Line 78: @[export lean_io_cancel_token_is_set] isSetExport -> ❌ (Not found in Rust, should be `use crate::Init::System::CancelToken::lean_io_cancel_token_is_set;`)

src/Lean/LoadDynlib.lean
  Line 66: @[export lean_load_dynlib] loadDynlib -> ❌ (Not found in Rust, should be `use crate::Lean::LoadDynlib::lean_load_dynlib;`)
  Line 94: @[export lean_load_plugin] loadPlugin -> ❌ (Not found in Rust, should be `use crate::Lean::LoadDynlib::lean_load_plugin;`)

src/Lean/ImportingFlag.lean
  Line 30: @[export lean_enable_initializer_execution] enableInitializersExecution -> src/rust/lean_shell/src/lib.rs:24 -> ⚠️ (Wrong import: `use runtime::lean_enable_initializer_execution;`, should be `use crate::Lean::ImportingFlag::lean_enable_initializer_execution;`)

src/Lean/Data/Options.lean
  Line 32: @[export lean_options_get_empty] getEmpty -> src/rust/runtime/src/base.rs:48 -> 🔌 (FFI Declaration: `pub fn lean_options_get_empty(_: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 124: @[export lean_register_option] registerOption -> src/rust/runtime/src/kernel_trace.rs:28 -> 🔌 (FFI Declaration: `fn lean_register_option(name: *mut LeanObject, decl: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 137: @[export lean_get_option_decls_array] getOptionDeclsArray -> ❌ (Not found in Rust, should be `use crate::Lean::Data::Options::lean_get_option_decls_array;`)
  Line 211: @[export lean_options_get_bool] getBool -> src/rust/runtime/src/base.rs:49 -> 🔌 (FFI Declaration: `pub fn lean_options_get_bool(`) ✅
  Line 221: @[export lean_options_update_bool] updateBool -> src/rust/runtime/src/base.rs:54 -> 🔌 (FFI Declaration: `pub fn lean_options_update_bool(`) ✅

src/Lean/Util/Profile.lean
  Line 28: @[export lean_get_profiler] get_profiler -> src/rust/runtime/src/base.rs:63 -> 🔌 (FFI Declaration: `pub fn lean_get_profiler(opts: *mut LeanObject) -> u8;`) ✅
  Line 32: @[export lean_get_profiler_threshold] profiler.threshold.getSecs -> src/rust/runtime/src/base.rs:64 -> 🔌 (FFI Declaration: `pub fn lean_get_profiler_threshold(opts: *mut LeanObject) -> f64;`) ✅

src/Lean/Level.lean
  Line 125: @[export lean_level_hash] hashEx -> src/rust/runtime/src/kernel_type_checker.rs:52 -> 🔌 (FFI Declaration: `fn lean_level_hash(l: *const LeanObject) -> u32;`) ✅
  Line 126: @[export lean_level_has_mvar] hasMVarEx -> ❌ (Not found in Rust, should be `use crate::Lean::Level::lean_level_has_mvar;`)
  Line 127: @[export lean_level_has_param] hasParamEx -> ❌ (Not found in Rust, should be `use crate::Lean::Level::lean_level_has_param;`)
  Line 128: @[export lean_level_depth] depthEx -> ❌ (Not found in Rust, should be `use crate::Lean::Level::lean_level_depth;`)
  Line 155: @[export lean_level_mk_zero] mkLevelZeroEx -> src/rust/runtime/src/kernel_type_checker.rs:43 -> 🔌 (FFI Declaration: `fn lean_level_mk_zero() -> *mut LeanObject;`) ✅
  Line 156: @[export lean_level_mk_succ] mkLevelSuccEx -> src/rust/runtime/src/library_instantiate_mvars.rs:41 -> 🔌 (FFI Declaration: `fn lean_level_mk_succ(l: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 157: @[export lean_level_mk_mvar] mkLevelMVarEx -> src/rust/runtime/src/kernel_type_checker.rs:48 -> 🔌 (FFI Declaration: `fn lean_level_mk_mvar(n: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 158: @[export lean_level_mk_param] mkLevelParamEx -> src/rust/runtime/src/kernel_type_checker.rs:47 -> 🔌 (FFI Declaration: `fn lean_level_mk_param(n: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 159: @[export lean_level_mk_max] mkLevelMaxEx -> src/rust/runtime/src/library_instantiate_mvars.rs:42 -> 🔌 (FFI Declaration: `fn lean_level_mk_max(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 160: @[export lean_level_mk_imax] mkLevelIMaxEx -> src/rust/runtime/src/library_instantiate_mvars.rs:43 -> 🔌 (FFI Declaration: `fn lean_level_mk_imax(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;`) ✅

src/Lean/Expr.lean
  Line 608: @[export lean_expr_hash] hashEx -> src/rust/runtime/src/kernel_type_checker.rs:94 -> 🔌 (FFI Declaration: `fn lean_expr_hash(e: *const LeanObject) -> u64;`) ✅
  Line 609: @[export lean_expr_has_fvar] hasFVarEx -> src/rust/runtime/src/kernel_type_checker.rs:97 -> 🔌 (FFI Declaration: `fn lean_expr_has_fvar(e: *const LeanObject) -> bool;`) ✅
  Line 610: @[export lean_expr_has_expr_mvar] hasExprMVarEx -> src/rust/runtime/src/kernel_type_checker.rs:99 -> 🔌 (FFI Declaration: `fn lean_expr_has_expr_mvar(e: *const LeanObject) -> bool;`) ✅
  Line 611: @[export lean_expr_has_level_mvar] hasLevelMVarEx -> ❌ (Not found in Rust, should be `use crate::Lean::Expr::lean_expr_has_level_mvar;`)
  Line 612: @[export lean_expr_has_mvar] hasMVarEx -> src/rust/runtime/src/kernel_type_checker.rs:98 -> 🔌 (FFI Declaration: `fn lean_expr_has_mvar(e: *const LeanObject) -> bool;`) ✅
  Line 613: @[export lean_expr_has_level_param] hasLevelParamEx -> ❌ (Not found in Rust, should be `use crate::Lean::Expr::lean_expr_has_level_param;`)
  Line 614: @[export lean_expr_loose_bvar_range] looseBVarRangeEx -> ❌ (Not found in Rust, should be `use crate::Lean::Expr::lean_expr_loose_bvar_range;`)
  Line 615: @[export lean_expr_binder_info] binderInfoEx -> src/rust/runtime/src/kernel_type_checker.rs:785 -> 🔌 (FFI Declaration: `fn lean_expr_binder_info(e: *mut LeanObject) -> u8;`) ✅
  Line 628: @[export lean_lit_type] Literal.typeEx -> src/rust/runtime/src/kernel_type_checker.rs:5041 -> 🛠️ (Defined in Rust: `unsafe fn lean_lit_type(e: *mut LeanObject) -> *mut LeanObject {`, should be `use crate::Lean::Expr::lean_lit_type;`)
  Line 747: @[export lean_expr_mk_bvar] mkBVarEx -> src/rust/runtime/src/kernel_expr.rs:42 -> 🔌 (FFI Declaration: `fn lean_expr_mk_bvar(idx: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 748: @[export lean_expr_mk_fvar] mkFVarEx -> src/rust/runtime/src/library_print.rs:27 -> 🔌 (FFI Declaration: `fn lean_expr_mk_fvar(n: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 749: @[export lean_expr_mk_mvar] mkMVarEx -> src/rust/runtime/src/kernel_type_checker.rs:60 -> 🔌 (FFI Declaration: `fn lean_expr_mk_mvar(id: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 750: @[export lean_expr_mk_sort] mkSortEx -> src/rust/runtime/src/library_instantiate_mvars.rs:50 -> 🔌 (FFI Declaration: `fn lean_expr_mk_sort(l: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 751: @[export lean_expr_mk_const] mkConstEx -> src/rust/runtime/src/library_instantiate_mvars.rs:51 -> 🔌 (FFI Declaration: `fn lean_expr_mk_const(n: *mut LeanObject, us: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 752: @[export lean_expr_mk_app] mkAppEx -> src/rust/runtime/src/kernel_expr.rs:43 -> 🔌 (FFI Declaration: `fn lean_expr_mk_app(f: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 753: @[export lean_expr_mk_lambda] mkLambdaEx -> src/rust/runtime/src/kernel_expr.rs:44 -> 🔌 (FFI Declaration: `fn lean_expr_mk_lambda(`) ✅
  Line 754: @[export lean_expr_mk_forall] mkForallEx -> src/rust/runtime/src/kernel_expr.rs:50 -> 🔌 (FFI Declaration: `fn lean_expr_mk_forall(`) ✅
  Line 755: @[export lean_expr_mk_let] mkLetEx -> src/rust/runtime/src/kernel_expr.rs:56 -> 🔌 (FFI Declaration: `fn lean_expr_mk_let(`) ✅
  Line 756: @[export lean_expr_mk_lit] mkLitEx -> src/rust/runtime/src/kernel_type_checker.rs:83 -> 🔌 (FFI Declaration: `fn lean_expr_mk_lit(l: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 757: @[export lean_expr_mk_mdata] mkMDataEx -> src/rust/runtime/src/kernel_expr.rs:63 -> 🔌 (FFI Declaration: `fn lean_expr_mk_mdata(data: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 758: @[export lean_expr_mk_proj] mkProjEx -> src/rust/runtime/src/kernel_expr.rs:64 -> 🔌 (FFI Declaration: `fn lean_expr_mk_proj(`) ✅
  Line 909: @[export lean_expr_is_have] isHaveEx -> ❌ (Not found in Rust, should be `use crate::Lean::Expr::lean_expr_is_have;`)
  Line 1700: @[export lean_is_out_param] isOutParam -> ❌ (Not found in Rust, should be `use crate::Lean::Expr::lean_is_out_param;`)
  Line 1730: @[export lean_expr_consume_type_annotations] consumeTypeAnnotations -> src/rust/runtime/src/kernel_type_checker.rs:6709 -> 🔌 (FFI Declaration: `fn lean_expr_consume_type_annotations(e: *mut LeanObject) -> *mut LeanObject;`) ✅

src/Lean/LocalContext.lean
  Line 89: @[export lean_mk_local_decl] mkLocalDeclEx -> ❌ (Not found in Rust, should be `use crate::Lean::LocalContext::lean_mk_local_decl;`)
  Line 92: @[export lean_mk_let_decl] mkLetDeclEx -> ❌ (Not found in Rust, should be `use crate::Lean::LocalContext::lean_mk_let_decl;`)
  Line 95: @[export lean_local_decl_binder_info] LocalDecl.binderInfoEx -> src/rust/runtime/src/kernel_type_checker.rs:834 -> 🔌 (FFI Declaration: `fn lean_local_decl_binder_info(d: *mut LeanObject) -> u8;`) ✅
  Line 273: @[export lean_mk_empty_local_ctx] mkEmpty -> src/rust/runtime/src/kernel_type_checker.rs:5768 -> 🔌 (FFI Declaration: `fn lean_mk_empty_local_ctx(u: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 278: @[export lean_local_ctx_is_empty] isEmpty -> ❌ (Not found in Rust, should be `use crate::Lean::LocalContext::lean_local_ctx_is_empty;`)
  Line 294: @[export lean_local_ctx_mk_local_decl] mkLocalDeclExported -> src/rust/runtime/src/kernel_type_checker.rs:1453 -> 🛠️ (Defined in Rust: `unsafe fn lean_local_ctx_mk_local_decl(`, should be `use crate::Lean::LocalContext::lean_local_ctx_mk_local_decl;`)
  Line 306: @[export lean_local_ctx_mk_let_decl] mkLetDeclExported -> ❌ (Not found in Rust, should be `use crate::Lean::LocalContext::lean_local_ctx_mk_let_decl;`)
  Line 330: @[export lean_local_ctx_find] find -> src/rust/runtime/src/kernel_type_checker.rs:213 -> 🔌 (FFI Declaration: `fn lean_local_ctx_find(lctx: *mut LeanObject, name: *mut LeanObject) -> *mut LeanObject; // Option LocalDecl`) ✅
  Line 370: @[export lean_local_ctx_erase] erase -> ❌ (Not found in Rust, should be `use crate::Lean::LocalContext::lean_local_ctx_erase;`)
  Line 482: @[export lean_local_ctx_num_indices] numIndices -> ❌ (Not found in Rust, should be `use crate::Lean::LocalContext::lean_local_ctx_num_indices;`)

src/Lean/MetavarContext.lean
  Line 398: @[export lean_get_lmvar_assignment] getLevelMVarAssignmentExp -> src/rust/runtime/src/library_instantiate_mvars.rs:17 -> 🔌 (FFI Declaration: `fn lean_get_lmvar_assignment(`) ✅
  Line 405: @[export lean_get_mvar_assignment] MetavarContext.getExprAssignmentExp -> src/rust/runtime/src/library_instantiate_mvars.rs:27 -> 🔌 (FFI Declaration: `fn lean_get_mvar_assignment(mctx: *mut LeanObject, mid: *mut LeanObject)`) ✅
  Line 415: @[export lean_get_delayed_mvar_assignment] MetavarContext.getDelayedMVarAssignmentExp -> src/rust/runtime/src/library_instantiate_mvars.rs:29 -> 🔌 (FFI Declaration: `fn lean_get_delayed_mvar_assignment(`) ✅
  Line 419: @[export lean_delayed_mvar_assignment_fvars] DelayedMetavarAssignment.fvarsExp -> src/rust/runtime/src/library_instantiate_mvars.rs:33 -> 🔌 (FFI Declaration: `fn lean_delayed_mvar_assignment_fvars(d: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 422: @[export lean_delayed_mvar_assignment_mvar_id_pending] DelayedMetavarAssignment.mvarIdPendingExp -> src/rust/runtime/src/library_instantiate_mvars.rs:34 -> 🔌 (FFI Declaration: `fn lean_delayed_mvar_assignment_mvar_id_pending(d: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 522: @[export lean_assign_lmvar] assignLevelMVarExp -> src/rust/runtime/src/library_instantiate_mvars.rs:21 -> 🔌 (FFI Declaration: `fn lean_assign_lmvar(`) ✅
  Line 535: @[export lean_assign_mvar] assignExp -> src/rust/runtime/src/library_instantiate_mvars.rs:35 -> 🔌 (FFI Declaration: `fn lean_assign_mvar(`) ✅

src/Lean/Declaration.lean
  Line 52: @[export lean_mk_reducibility_hints_regular] mkReducibilityHintsRegularEx -> ❌ (Not found in Rust, should be `use crate::Lean::Declaration::lean_mk_reducibility_hints_regular;`)
  Line 56: @[export lean_reducibility_hints_get_height] ReducibilityHints.getHeightEx -> src/rust/runtime/src/kernel_type_checker.rs:799 -> 🔌 (FFI Declaration: `fn lean_reducibility_hints_get_height(h: *mut LeanObject) -> u32;`) ✅
  Line 105: @[export lean_mk_axiom_val] mkAxiomValEx -> ❌ (Not found in Rust, should be `use crate::Lean::Declaration::lean_mk_axiom_val;`)
  Line 113: @[export lean_axiom_val_is_unsafe] AxiomVal.isUnsafeEx -> src/rust/runtime/src/kernel_type_checker.rs:794 -> 🔌 (FFI Declaration: `fn lean_axiom_val_is_unsafe(v: *mut LeanObject) -> u8;`) ✅
  Line 134: @[export lean_mk_definition_val] mkDefinitionValEx -> ❌ (Not found in Rust, should be `use crate::Lean::Declaration::lean_mk_definition_val;`)
  Line 139: @[export lean_definition_val_get_safety] DefinitionVal.getSafetyEx -> src/rust/runtime/src/kernel_type_checker.rs:792 -> 🔌 (FFI Declaration: `fn lean_definition_val_get_safety(v: *mut LeanObject) -> u8;`) ✅
  Line 150: @[export lean_mk_theorem_val] mkTheoremValEx -> ❌ (Not found in Rust, should be `use crate::Lean::Declaration::lean_mk_theorem_val;`)
  Line 165: @[export lean_mk_opaque_val] mkOpaqueValEx -> ❌ (Not found in Rust, should be `use crate::Lean::Declaration::lean_mk_opaque_val;`)
  Line 170: @[export lean_opaque_val_is_unsafe] OpaqueVal.isUnsafeEx -> src/rust/runtime/src/kernel_type_checker.rs:795 -> 🔌 (FFI Declaration: `fn lean_opaque_val_is_unsafe(v: *mut LeanObject) -> u8;`) ✅
  Line 195: @[export lean_mk_inductive_decl] mkInductiveDeclEs -> src/rust/runtime/src/kernel_type_checker.rs:6503 -> 🔌 (FFI Declaration: `fn lean_mk_inductive_decl(`) ✅
  Line 199: @[export lean_is_unsafe_inductive_decl] Declaration.isUnsafeInductiveDeclEx -> src/rust/runtime/src/kernel_type_checker.rs:6509 -> 🔌 (FFI Declaration: `fn lean_is_unsafe_inductive_decl(d: *mut LeanObject) -> u8;`) ✅
  Line 304: @[export lean_mk_inductive_val] mkInductiveValEx -> src/rust/runtime/src/kernel_type_checker.rs:6467 -> 🔌 (FFI Declaration: `fn lean_mk_inductive_val(`) ✅
  Line 320: @[export lean_inductive_val_is_rec] InductiveVal.isRecEx -> src/rust/runtime/src/kernel_type_checker.rs:1197 -> 🛠️ (Defined in Rust: `unsafe fn lean_inductive_val_is_rec(v: *const LeanObject) -> bool {`, should be `use crate::Lean::Declaration::lean_inductive_val_is_rec;`)
  Line 321: @[export lean_inductive_val_is_unsafe] InductiveVal.isUnsafeEx -> src/rust/runtime/src/kernel_type_checker.rs:1203 -> 🛠️ (Defined in Rust: `unsafe fn lean_inductive_val_is_unsafe(v: *const LeanObject) -> bool {`, should be `use crate::Lean::Declaration::lean_inductive_val_is_unsafe;`)
  Line 322: @[export lean_inductive_val_is_reflexive] InductiveVal.isReflexiveEx -> src/rust/runtime/src/kernel_type_checker.rs:1209 -> 🛠️ (Defined in Rust: `unsafe fn lean_inductive_val_is_reflexive(v: *const LeanObject) -> bool {`, should be `use crate::Lean::Declaration::lean_inductive_val_is_reflexive;`)
  Line 340: @[export lean_mk_constructor_val] mkConstructorValEx -> src/rust/runtime/src/kernel_type_checker.rs:6480 -> 🔌 (FFI Declaration: `fn lean_mk_constructor_val(`) ✅
  Line 345: @[export lean_constructor_val_is_unsafe] ConstructorVal.isUnsafeEx -> src/rust/runtime/src/kernel_type_checker.rs:1215 -> 🛠️ (Defined in Rust: `unsafe fn lean_constructor_val_is_unsafe(v: *const LeanObject) -> bool {`, should be `use crate::Lean::Declaration::lean_constructor_val_is_unsafe;`)
  Line 383: @[export lean_mk_recursor_val] mkRecursorValEx -> src/rust/runtime/src/kernel_type_checker.rs:6490 -> 🔌 (FFI Declaration: `fn lean_mk_recursor_val(`) ✅
  Line 390: @[export lean_recursor_k] RecursorVal.kEx -> src/rust/runtime/src/kernel_type_checker.rs:789 -> 🔌 (FFI Declaration: `fn lean_recursor_k(v: *mut LeanObject) -> u8;`) ✅
  Line 391: @[export lean_recursor_is_unsafe] RecursorVal.isUnsafeEx -> src/rust/runtime/src/kernel_type_checker.rs:790 -> 🔌 (FFI Declaration: `fn lean_recursor_is_unsafe(v: *mut LeanObject) -> u8;`) ✅
  Line 421: @[export lean_mk_quot_val] mkQuotValEx -> src/rust/runtime/src/kernel_type_checker.rs:279 -> 🔌 (FFI Declaration: `fn lean_mk_quot_val(`) ✅
  Line 426: @[export lean_quot_val_kind] QuotVal.kindEx -> ❌ (Not found in Rust, should be `use crate::Lean::Declaration::lean_quot_val_kind;`)

src/Lean/Environment.lean
  Line 282: @[export lean_environment_find] find -> src/rust/runtime/src/kernel_type_checker.rs:159 -> 🔌 (FFI Declaration: `fn lean_environment_find(env: *const LeanObject, name: *mut LeanObject) -> *mut LeanObject; // returns Option ConstantInfo`) ✅
  Line 287: @[export lean_environment_mark_quot_init] markQuotInit -> src/rust/runtime/src/kernel_type_checker.rs:817 -> 🔌 (FFI Declaration: `fn lean_environment_mark_quot_init(env: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 291: @[export lean_environment_quot_init] isQuotInit -> src/rust/runtime/src/kernel_type_checker.rs:787 -> 🔌 (FFI Declaration: `fn lean_environment_quot_init(env: *mut LeanObject) -> u8;`) ✅
  Line 310: @[export lean_environment_add] add -> src/rust/runtime/src/kernel_type_checker.rs:5771 -> 🔌 (FFI Declaration: `fn lean_environment_add(env: *mut LeanObject, info: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 314: @[export lean_kernel_diag_is_enabled] Diagnostics.isEnabled -> src/rust/runtime/src/kernel_type_checker.rs:5774 -> 🔌 (FFI Declaration: `fn lean_kernel_diag_is_enabled(d: *mut LeanObject) -> u8;`) ✅
  Line 328: @[export lean_kernel_record_unfold] Diagnostics.recordUnfold -> src/rust/runtime/src/kernel_type_checker.rs:5775 -> 🔌 (FFI Declaration: `fn lean_kernel_record_unfold(d: *mut LeanObject, name: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 336: @[export lean_kernel_get_diag] getDiagnostics -> src/rust/runtime/src/kernel_type_checker.rs:5776 -> 🔌 (FFI Declaration: `fn lean_kernel_get_diag(env: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 340: @[export lean_kernel_set_diag] setDiagnostics -> src/rust/runtime/src/kernel_type_checker.rs:5777 -> 🔌 (FFI Declaration: `fn lean_kernel_set_diag(env: *mut LeanObject, diag: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 644: @[export lean_elab_environment_of_kernel_env] ofKernelEnv -> src/rust/runtime/src/library_ir_interpreter.rs:52 -> 🔌 (FFI Declaration: `fn lean_elab_environment_of_kernel_env(env: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 648: @[export lean_elab_environment_to_kernel_env] toKernelEnv -> src/rust/runtime/src/library_elab_environment.rs:12 -> 🔌 (FFI Declaration: `fn lean_elab_environment_to_kernel_env(env: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 742: @[export lake_environment_add] lakeAdd -> src/rust/lake_ffi/src/ffi/Lake/Load/Lean/Elab.rs:4 -> ⚠️ (Wrong import: `pub use gen_lean::r#gen::Lean::Environment::lake_environment_add;`, should be `use crate::Lean::Environment::lake_environment_add;`)
  Line 1496: @[export lean_mk_empty_environment] mkEmptyEnvironment -> ❌ (Not found in Rust, should be `use crate::Lean::Environment::lean_mk_empty_environment;`)
  Line 1768: @[export lean_environment_free_regions] Environment.freeRegions -> ❌ (Not found in Rust, should be `use crate::Lean::Environment::lean_environment_free_regions;`)
  Line 2413: @[export lean_elab_environment_update_base_after_kernel_add] updateBaseAfterKernelAdd -> src/rust/runtime/src/library_elab_environment.rs:14 -> 🔌 (FFI Declaration: `fn lean_elab_environment_update_base_after_kernel_add(`) ✅

src/Lean/ProjFns.lean
  Line 30: @[export lean_mk_projection_info] mkProjectionInfoEx -> ❌ (Not found in Rust, should be `use crate::Lean::ProjFns::lean_mk_projection_info;`)
  Line 33: @[export lean_projection_info_from_class] ProjectionFunctionInfo.fromClassEx -> ❌ (Not found in Rust, should be `use crate::Lean::ProjFns::lean_projection_info_from_class;`)

src/Lean/Compiler/NameMangling.lean
  Line 144: @[export lean_mk_mangled_boxed_name] mkMangledBoxedName -> src/rust/runtime/src/library_ir_interpreter.rs:36 -> 🔌 (FFI Declaration: `fn lean_mk_mangled_boxed_name(s: *mut LeanObject) -> *mut LeanObject;`) ✅

src/Lean/Compiler/ModPkgExt.lean
  Line 63: @[export lean_get_symbol_stem] getSymbolStem -> src/rust/runtime/src/library_ir_interpreter.rs:35 -> 🔌 (FFI Declaration: `fn lean_get_symbol_stem(env: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;`) ✅

src/Lean/Compiler/NameDemangling.lean
  Line 335: @[export lean_demangle_bt_line_cstr] demangleBtLineCStr -> src/rust/leanh/src/runtime_object_panic.rs:86 -> 🔍 (Dynamic string lookup: `let Ok(demangle) = (unsafe { lib.get::<DemangleBacktraceLine>(c"lean_demangle_bt_line_cstr") })`) ✅

src/Lean/Util/Trace.lean
  Line 121: @[export lean_is_trace_class_enabled] isTracingEnabledForExport -> src/rust/runtime/src/kernel_trace.rs:27 -> 🔌 (FFI Declaration: `fn lean_is_trace_class_enabled(opts: *mut LeanObject, cls: *mut LeanObject) -> bool;`) ✅

src/Lean/ResolveName.lean
  Line 51: @[export lean_is_reserved_name] isReservedName -> ❌ (Not found in Rust, should be `use crate::Lean::ResolveName::lean_is_reserved_name;`)
  Line 75: @[export lean_add_alias] addAlias -> ❌ (Not found in Rust, should be `use crate::Lean::ResolveName::lean_add_alias;`)

src/Lean/Attributes.lean
  Line 461: @[export lean_is_attribute] isBuiltinAttribute -> ❌ (Not found in Rust, should be `use crate::Lean::Attributes::lean_is_attribute;`)
  Line 475: @[export lean_attribute_application_time] getBuiltinAttributeApplicationTime -> ❌ (Not found in Rust, should be `use crate::Lean::Attributes::lean_attribute_application_time;`)
  Line 510: @[export lean_update_env_attributes] updateEnvAttributesImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Attributes::lean_update_env_attributes;`)
  Line 522: @[export lean_get_num_attributes] getNumBuiltinAttributesImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Attributes::lean_get_num_attributes;`)

src/Lean/Compiler/ExportAttr.lean
  Line 55: @[export lean_get_export_name_for] getExportNameFor -> src/rust/runtime/src/library_ir_interpreter.rs:43 -> 🔌 (FFI Declaration: `fn lean_get_export_name_for(env: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;`) ✅

src/Lean/Compiler/IR/Format.lean
  Line 111: @[export lean_ir_format_fn_body_head] formatFnBodyHead' -> src/rust/runtime/src/library_ir_interpreter.rs:72 -> 🔌 (FFI Declaration: `fn lean_ir_format_fn_body_head(b: *mut LeanObject) -> *mut LeanObject;`) ✅

src/Lean/ReducibilityAttrs.lean
  Line 73: @[export lean_get_reducibility_status] getReducibilityStatusCore -> ❌ (Not found in Rust, should be `use crate::Lean::ReducibilityAttrs::lean_get_reducibility_status;`)
  Line 98: @[export lean_set_reducibility_status] setReducibilityStatusImp -> ❌ (Not found in Rust, should be `use crate::Lean::ReducibilityAttrs::lean_set_reducibility_status;`)

src/Lean/Class.lean
  Line 77: @[export lean_is_class] isClass -> ❌ (Not found in Rust, should be `use crate::Lean::Class::lean_is_class;`)
  Line 86: @[export lean_has_out_params] hasOutParams -> ❌ (Not found in Rust, should be `use crate::Lean::Class::lean_has_out_params;`)
  Line 136: @[export lean_mk_outparam_args_implicit] mkOutParamArgsImplicit -> ❌ (Not found in Rust, should be `use crate::Lean::Class::lean_mk_outparam_args_implicit;`)

src/Lean/Meta/Match/MatchPatternAttr.lean
  Line 41: @[export lean_has_match_pattern_attribute] hasMatchPatternAttribute -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Match::MatchPatternAttr::lean_has_match_pattern_attribute;`)

src/Lean/Meta/InferType.lean
  Line 235: @[export lean_infer_type] inferTypeImp -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::InferType::lean_infer_type;`)

src/Lean/Meta/Match/MatcherInfo.lean
  Line 162: @[export lean_is_matcher] isMatcherCore -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Match::MatcherInfo::lean_is_matcher;`)

src/Lean/Meta/WHNF.lean
  Line 1103: @[export lean_whnf] whnfImp -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::WHNF::lean_whnf;`)

src/Lean/Meta/LevelDefEq.lean
  Line 144: @[export lean_is_level_def_eq] isLevelDefEqAuxImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::LevelDefEq::lean_is_level_def_eq;`)

src/Lean/Meta/SynthInstance.lean
  Line 948: @[export lean_synth_pending] synthPendingImp -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::SynthInstance::lean_synth_pending;`)

src/Lean/Meta/ExprDefEq.lean
  Line 1164: @[export lean_checked_assign] checkedAssignImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::ExprDefEq::lean_checked_assign;`)
  Line 2271: @[export lean_is_expr_def_eq] isExprDefEqAuxImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::ExprDefEq::lean_is_expr_def_eq;`)

src/Lean/Compiler/InitAttr.lean
  Line 121: @[export lean_get_regular_init_fn_name_for] getRegularInitFnNameFor -> src/rust/runtime/src/library_ir_interpreter.rs:39 -> 🔌 (FFI Declaration: `fn lean_get_regular_init_fn_name_for(`) ✅
  Line 125: @[export lean_get_init_fn_name_for] getInitFnNameFor -> src/rust/runtime/src/base.rs:59 -> 🔌 (FFI Declaration: `pub fn lean_get_init_fn_name_for(`) ✅
  Line 159: @[export lean_run_init_attrs] runInitAttrs -> ❌ (Not found in Rust, should be `use crate::Lean::Compiler::InitAttr::lean_run_init_attrs;`)

src/Lean/Compiler/IR/CompilerM.lean
  Line 120: @[export lean_ir_export_entries] exportIREntries -> ❌ (Not found in Rust, should be `use crate::Lean::Compiler::IR::CompilerM::lean_ir_export_entries;`)
  Line 145: @[export lean_ir_find_env_decl] findInterpDecl -> src/rust/runtime/src/library_ir_interpreter.rs:24 -> 🔌 (FFI Declaration: `fn lean_ir_find_env_decl(env: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 157: @[export lean_ir_find_env_decl_boxed] findInterpDeclBoxed -> src/rust/runtime/src/library_ir_interpreter.rs:25 -> 🔌 (FFI Declaration: `fn lean_ir_find_env_decl_boxed(env: *mut LeanObject, n: *mut LeanObject)`) ✅
  Line 172: @[export lean_has_compile_error] hasCompileError -> ❌ (Not found in Rust, should be `use crate::Lean::Compiler::IR::CompilerM::lean_has_compile_error;`)
  Line 221: @[export lean_decl_get_sorry_dep] getSorryDep -> src/rust/runtime/src/library_ir_interpreter.rs:49 -> 🔌 (FFI Declaration: `fn lean_decl_get_sorry_dep(env: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject;`) ✅
  Line 228: @[export lean_get_ir_extra_const_names] getIRExtraConstNames -> ❌ (Not found in Rust, should be `use crate::Lean::Compiler::IR::CompilerM::lean_get_ir_extra_const_names;`)

src/Lean/Meta/Sym/Pattern.lean
  Line 883: @[export lean_sym_def_eq] isDefEqMainImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Sym::Pattern::lean_sym_def_eq;`)

src/Lean/Compiler/IR/EmitLLVM.lean
  Line 1639: @[export lean_ir_emit_llvm] emitLLVM -> src/rust/runtime/src/library_llvm.rs:12 -> 🔌 (FFI Declaration: `fn lean_ir_emit_llvm(`) ✅

src/Lean/Compiler/IR/Meta.lean
  Line 56: @[export lean_eval_check_meta] evalCheckMeta -> ❌ (Not found in Rust, should be `use crate::Lean::Compiler::IR::Meta::lean_eval_check_meta;`)

src/Lean/Meta/Sym/DSimp/Main.lean
  Line 37: @[export lean_sym_dsimp] dsimpImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Sym::DSimp::Main::lean_sym_dsimp;`)

src/Lean/Meta/Sym/Simp/Main.lean
  Line 44: @[export lean_sym_simp] simpImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Sym::Simp::Main::lean_sym_simp;`)

src/Lean/Parser.lean
  Line 70: @[export lean_mk_antiquot_parenthesizer] mkAntiquot.parenthesizer -> ❌ (Not found in Rust, should be `use crate::Lean::Parser::lean_mk_antiquot_parenthesizer;`)
  Line 85: @[export lean_pretty_printer_parenthesizer_interpret_parser_descr] interpretParserDescr -> ❌ (Not found in Rust, should be `use crate::Lean::Parser::lean_pretty_printer_parenthesizer_interpret_parser_descr;`)
  Line 107: @[export lean_mk_antiquot_formatter] mkAntiquot.formatter -> ❌ (Not found in Rust, should be `use crate::Lean::Parser::lean_mk_antiquot_formatter;`)
  Line 120: @[export lean_pretty_printer_formatter_interpret_parser_descr] interpretParserDescr -> ❌ (Not found in Rust, should be `use crate::Lean::Parser::lean_pretty_printer_formatter_interpret_parser_descr;`)

src/Lean/Meta/Tactic/Simp/Main.lean
  Line 516: @[export lean_dsimp] dsimpImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Simp::Main::lean_dsimp;`)
  Line 715: @[export lean_simp] simpImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Simp::Main::lean_simp;`)

src/Lean/Elab/PreDefinition/Structural/Eqns.lean
  Line 190: @[export lean_get_structural_rec_arg_pos] getStructuralRecArgPosImp -> ❌ (Not found in Rust, should be `use crate::Lean::Elab::PreDefinition::Structural::Eqns::lean_get_structural_rec_arg_pos;`)

src/Lean/Meta/Match/MatchEqs.lean
  Line 142: @[export lean_get_match_equations_for] getEquationsForImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Match::MatchEqs::lean_get_match_equations_for;`)
  Line 262: @[export lean_get_congr_match_equations_for] genMatchCongrEqnsImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Match::MatchEqs::lean_get_congr_match_equations_for;`)

src/Lean/Meta/Tactic/Grind/Simp.lean
  Line 50: @[export lean_grind_preprocess] preprocessImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Simp::lean_grind_preprocess;`)

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Var.lean
  Line 68: @[export lean_grind_cutsat_mk_var] mkVarImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Arith::Cutsat::Var::lean_grind_cutsat_mk_var;`)

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/Proof.lean
  Line 331: @[export lean_cutsat_eq_cnstr_to_proof] EqCnstr.toExprProofImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Arith::Cutsat::Proof::lean_cutsat_eq_cnstr_to_proof;`)

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/LeCnstr.lean
  Line 103: @[export lean_grind_cutsat_assert_le] LeCnstr.assertImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Arith::Cutsat::LeCnstr::lean_grind_cutsat_assert_le;`)

src/Lean/Meta/Tactic/Grind/Proof.lean
  Line 336: @[export lean_grind_mk_eq_proof] mkEqProofImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Proof::lean_grind_mk_eq_proof;`)
  Line 343: @[export lean_grind_mk_heq_proof] mkHEqProofImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Proof::lean_grind_mk_heq_proof;`)

src/Lean/Meta/Tactic/Grind/Arith/Cutsat/EqCnstr.lean
  Line 280: @[export lean_cutsat_propagate_nonlinear] propagateNonlinearTermImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Arith::Cutsat::EqCnstr::lean_cutsat_propagate_nonlinear;`)
  Line 343: @[export lean_grind_cutsat_assert_eq] EqCnstr.assertImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Arith::Cutsat::EqCnstr::lean_grind_cutsat_assert_eq;`)

src/Lean/Meta/Tactic/Grind/Internalize.lean
  Line 539: @[export lean_grind_internalize] internalizeImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Internalize::lean_grind_internalize;`)

src/Lean/Meta/Tactic/Grind/Core.lean
  Line 364: @[export lean_grind_process_new_facts] processNewFactsImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::Core::lean_grind_process_new_facts;`)

src/Lean/Meta/Tactic/Grind/SimpUtil.lean
  Line 206: @[export lean_grind_normalize] normalizeImp -> ❌ (Not found in Rust, should be `use crate::Lean::Meta::Tactic::Grind::SimpUtil::lean_grind_normalize;`)

src/Lean/Elab/Tactic/Try.lean
  Line 837: @[export lean_eval_suggest_tactic] evalSuggestImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Elab::Tactic::Try::lean_eval_suggest_tactic;`)

src/Lean/Elab/Idbg.lean
  Line 238: @[export lean_idbg_client_loop] idbgClientLoopImpl -> ❌ (Not found in Rust, should be `use crate::Lean::Elab::Idbg::lean_idbg_client_loop;`)

src/Lean/Shell.lean
  Line 252: @[export lean_shell_options_mk] mkShellOptions -> src/rust/lean_shell/src/lib.rs:33 -> ⚠️ (Wrong import: `use runtime::lean_shell_options_mk;`, should be `use crate::Lean::Shell::lean_shell_options_mk;`)
  Line 255: @[export lean_shell_options_get_run] ShellOptions.getRun -> src/rust/lean_shell/src/lib.rs:32 -> ⚠️ (Wrong import: `use runtime::lean_shell_options_get_run;`, should be `use crate::Lean::Shell::lean_shell_options_get_run;`)
  Line 259: @[export lean_shell_options_get_profiler] ShellOptions.getProfiler -> src/rust/lean_shell/src/lib.rs:31 -> ⚠️ (Wrong import: `use runtime::lean_shell_options_get_profiler;`, should be `use crate::Lean::Shell::lean_shell_options_get_profiler;`)
  Line 263: @[export lean_shell_options_get_num_threads] ShellOptions.getNumThreads -> src/rust/lean_shell/src/lib.rs:30 -> ⚠️ (Wrong import: `use runtime::lean_shell_options_get_num_threads;`, should be `use crate::Lean::Shell::lean_shell_options_get_num_threads;`)
  Line 292: @[export lean_shell_options_process] ShellOptions.process -> src/rust/lean_shell/src/lib.rs:34 -> ⚠️ (Wrong import: `use runtime::lean_shell_options_process;`, should be `use crate::Lean::Shell::lean_shell_options_process;`)
  Line 449: @[export lean_shell_main] shellMain -> src/rust/lean_shell/src/lib.rs:29 -> ⚠️ (Wrong import: `use runtime::lean_shell_main;`, should be `use crate::Lean::Shell::lean_shell_main;`)

========================================================================
WORKSPACE ANALYSIS SUMMARY
========================================================================
Lean imports from Rust ([extern]): (Lean <- Rust)
  Total occurrences:                                                          953
  Rust defined this function and function body is not empty (correct) (✅):   434
  Rust defined this function but function body is empty (empty) (⚠️):        0
  Rust does not define this function (missing) (❌):                          519

Rust should import from Lean ([export]): (Lean -> Rust)
  Total occurrences:                                                          245
  Function is found in rust code and import is correct (correct) (✅):        0
  Function is found in rust code, but import is wrong (wrong) (⚠️):          9
  Function is found in rust code, but is defined in rust (defined) (🛠️):     10
  Function is found inside of extern "C" block / FFI (externc) (🔌):          104
  Function is referenced via dynamic string lookup (dynamic) (🔍):            1
  Function is not found in rust code (missing) (❌):                          121
========================================================================
