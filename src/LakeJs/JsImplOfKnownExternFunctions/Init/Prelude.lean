import LakeJs.Js

open Lean.Compiler.JS

def lean_is_scalar := [JS|throw new Error("lean_is_scalar is not and should not be implemented")]
def lean_sorry := [JS|throw new Error("lean_sorry is not and should not be implemented")]
def lean_nat_add := [JS|#0 + #1]
def lean_nat_mul := [JS|#0 * #1]
def lean_nat_pow := [JS|#0 ^ #1]
def lean_nat_dec_eq := [JS|#0 == #1]
def lean_nat_pred := [JS|(#0 > 0) ? (#0 - 1) : 0]
def lean_nat_dec_le := [JS|#0 <= #1]
def lean_nat_dec_lt := [JS|#0 < #1]
def lean_nat_sub := [JS|(#0 > #1) ? (#0 - #1) : 0]
def lean_nat_div := [JS|(#1 > 0) ? (#0 / #1) : 0]
def lean_nat_mod := [JS|(#1 > 0) ? (#0 % #1) : 0]
def lean_system_platform_nbits := [JS|64]
def lean_uint8_of_nat := [JS|#0 & 0xFF]
def lean_uint8_dec_eq := [JS|#0 == #1]
def lean_uint8_dec_lt := [JS|#0 < #1]
def lean_uint8_dec_le := [JS|#0 <= #1]
def lean_uint16_of_nat := [JS|#0 & 0xFFFF]
def lean_uint16_dec_eq := [JS|#0 == #1]
def lean_uint32_of_nat := [JS|#0 >> 0]
def lean_uint32_dec_eq := [JS|#0 == #1]
def lean_uint32_dec_lt := [JS|#0 < #1]
def lean_uint32_dec_le := [JS|#0 <= #1]
def lean_uint64_dec_eq := [JS|#0 == #1]
def lean_usize_dec_eq := [JS|#0 == #1]
def lean_mk_empty_array_with_capacity := [JS|[]]
def lean_array_get_size := [JS|(#0).length]
def lean_array_push := [JS|(#0).concat(Array.of(#1))]
def lean_array_to_list := [JS|(#0).reduceRight((out, item) => mkObject(`List.cons, item, out), mkObject(`List.nil))]
def lean_array_mk := [JS_FUNC|inputs(curr)|returns=out|
  const out = [];
  while (isTag(curr, `List.cons)) {
    const head = getField(curr, 0);
    const tail = getField(curr, 1);
    out.push(head);
    curr = tail;
  }
]
def lean_array_get := [JS|(#2 < (#1).length) ? #1[#2] : #0]
def lean_array_get_borrowed := lean_array_get
def lean_array_fget := [JS|#0[#1]]
def lean_array_fget_borrowed := [JS|#0[#1]]
def lean_mk_empty_byte_array := [JS|new Uint8Array(0)]
def lean_byte_array_size := [JS|(#0).length]
def lean_byte_array_push := [JS|new Uint8Array(Array.from(#0).concat(Array.of(#1)))]
def lean_string_to_utf8 := [JS|new TextEncoder().encode(#0)]
def lean_string_from_utf8_unchecked := [JS|new TextDecoder().decode(#0)]
def lean_string_mk := [JS|throw new Error("lean_string_mk should not be implemented")]
def lean_string_dec_eq := [JS|#0 == #1]
def lean_float_of_scientific := [JS|throw new Error("lean_float_of_scientific is not and should not be implemented (we should just render floats?)")]
def lean_string_utf8_byte_size := [JS|new TextEncoder().encode(#0).length]
def lean_uint32_to_nat := [JS|#0 >>> 0]
def lean_panic_fn_borrowed := [JS|throw new Error(#1)]
