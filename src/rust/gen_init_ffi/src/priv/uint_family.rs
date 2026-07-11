use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_dec::lean_dec, lean_is_scalar::lean_is_scalar, lean_unbox::lean_unbox},
    r#priv::lean_usize_to_nat::lean_usize_to_nat,
    runtime_object_nat_int::{
        lean_uint8_of_big_nat, lean_uint16_of_big_nat, lean_uint32_of_big_nat,
        lean_uint64_of_big_nat,
    },
};

macro_rules! define_uint_family {
    ($ty:ty, $of_nat:ident, $of_nat_mk:ident, $to_nat:ident, $dec_eq:ident, $dec_lt:ident, $dec_le:ident, $of_big_nat:ident) => {
        #[inline]
        pub unsafe fn $of_nat(a: *const LeanObject) -> $ty {
            if lean_is_scalar(a) {
                lean_unbox(a) as $ty
            } else {
                $of_big_nat(a)
            }
        }

        #[inline]
        pub unsafe fn $of_nat_mk(a: *mut LeanObject) -> $ty {
            let r = $of_nat(a);
            lean_dec(a);
            r
        }

        #[inline]
        pub unsafe fn $to_nat(a: $ty) -> *mut LeanObject {
            lean_usize_to_nat(a as usize)
        }

        #[inline]
        pub unsafe fn $dec_eq(a1: $ty, a2: $ty) -> bool {
            a1 == a2
        }

        #[inline]
        pub unsafe fn $dec_lt(a1: $ty, a2: $ty) -> bool {
            a1 < a2
        }

        #[inline]
        pub unsafe fn $dec_le(a1: $ty, a2: $ty) -> bool {
            a1 <= a2
        }
    };
}

define_uint_family!(
    u8,
    lean_uint8_of_nat,
    lean_uint8_of_nat_mk,
    lean_uint8_to_nat,
    lean_uint8_dec_eq,
    lean_uint8_dec_lt,
    lean_uint8_dec_le,
    lean_uint8_of_big_nat
);

define_uint_family!(
    u16,
    lean_uint16_of_nat,
    lean_uint16_of_nat_mk,
    lean_uint16_to_nat,
    lean_uint16_dec_eq,
    lean_uint16_dec_lt,
    lean_uint16_dec_le,
    lean_uint16_of_big_nat
);

define_uint_family!(
    u32,
    lean_uint32_of_nat,
    lean_uint32_of_nat_mk,
    lean_uint32_to_nat,
    lean_uint32_dec_eq,
    lean_uint32_dec_lt,
    lean_uint32_dec_le,
    lean_uint32_of_big_nat
);

define_uint_family!(
    u64,
    lean_uint64_of_nat,
    lean_uint64_of_nat_mk,
    lean_uint64_to_nat,
    lean_uint64_dec_eq,
    lean_uint64_dec_lt,
    lean_uint64_dec_le,
    lean_uint64_of_big_nat
);
