use crate::{
    datatypes::LeanObject,
    emitted::{lean_dec::lean_dec, lean_is_scalar::lean_is_scalar_bool, lean_unbox::lean_unbox},
    r#priv::lean_usize_to_nat::lean_usize_to_nat,
};

#[inline]
pub unsafe fn lean_small_nat(obj: *mut LeanObject) -> usize {
    unsafe {
        if lean_is_scalar_bool(obj) {
            lean_unbox(obj)
        } else {
            panic!("big Nat is not supported in leanh.rs")

            // LEAN_EXPORT uint8_t lean_uint8_of_big_nat(b_lean_obj_arg a);
            // static inline uint8_t lean_uint8_of_nat(b_lean_obj_arg a) {
            //     return lean_is_scalar(a) ? (uint8_t)(lean_unbox(a)) : lean_uint8_of_big_nat(a);
            // }
            //
            // LEAN_EXPORT uint16_t lean_uint16_of_big_nat(b_lean_obj_arg a);
            // static inline uint16_t lean_uint16_of_nat(b_lean_obj_arg a) {
            //     return lean_is_scalar(a) ? (int16_t)(lean_unbox(a)) : lean_uint16_of_big_nat(a);
            // }
            //
            // LEAN_EXPORT uint32_t lean_uint32_of_big_nat(b_lean_obj_arg a);
            // static inline uint32_t lean_uint32_of_nat(b_lean_obj_arg a) {
            //     return lean_is_scalar(a) ? (uint32_t)(lean_unbox(a)) : lean_uint32_of_big_nat(a);
            // }
            //
            // LEAN_EXPORT uint64_t lean_uint64_of_big_nat(b_lean_obj_arg a);
            // static inline uint64_t lean_uint64_of_nat(b_lean_obj_arg a) {
            //     return lean_is_scalar(a) ? (uint64_t)(lean_unbox(a)) : lean_uint64_of_big_nat(a);
            // }
            //
            // LEAN_EXPORT size_t lean_usize_of_big_nat(b_lean_obj_arg a);
            // static inline size_t lean_usize_of_nat(b_lean_obj_arg a) {
            //     return lean_is_scalar(a) ? lean_unbox(a) : lean_usize_of_big_nat(a);
            // }
        }
    }
}

// unsafe fn lean_uint64_to_nat_rust(value: u64) -> *mut LeanObject {
//     if value <= usize::MAX as u64 >> 1 {
//         lean_box(value as usize)
//     } else {
//         runtime_object_nat_int_impl::lean_big_uint64_to_nat(value)
//     }
// }
//
// unsafe fn lean_int64_to_int_rust(value: i64) -> *mut LeanObject {
//     runtime_object_nat_int_impl::lean_big_int64_to_int(value)
// }
//
// unsafe fn lean_uint64_of_nat_rust(value: *mut LeanObject) -> u64 {
//     if lean_is_scalar(value) {
//         lean_unbox(value) as u64
//     } else {
//         runtime_object_nat_int_impl::lean_uint64_of_big_nat(value)
//     }
// }

// #[inline(always)]
// unsafe fn lean_uint64_of_nat(a: *mut LeanObject) -> u64 {
//     if lean_is_scalar(a) {
//         lean_unbox(a) as u64
//     } else {
//         lean_uint64_of_big_nat(a)
//     }
// }
//
// #[inline(always)]
// unsafe fn lean_usize_of_nat(a: *mut LeanObject) -> usize {
//     if lean_is_scalar(a) {
//         lean_unbox(a)
//     } else {
//         lean_usize_of_big_nat(a)
//     }
// }

macro_rules! define_uint_family {
    ($ty:ty, $of_nat:ident, $of_nat_mk:ident, $to_nat:ident, $dec_eq:ident, $dec_lt:ident, $dec_le:ident) => {
        #[inline]
        pub unsafe fn $of_nat(obj: *mut LeanObject) -> $ty {
            unsafe { lean_small_nat(obj) as $ty }
        }

        #[inline]
        pub unsafe fn $of_nat_mk(obj: *mut LeanObject) -> $ty {
            unsafe {
                let result = $of_nat(obj);
                lean_dec(obj);
                result
            }
        }

        #[inline]
        pub unsafe fn $to_nat(value: $ty) -> *mut LeanObject {
            unsafe { lean_usize_to_nat(value as usize) }
        }

        #[inline]
        pub unsafe fn $dec_eq(a: $ty, b: $ty) -> u8 {
            (a == b) as u8
        }

        #[inline]
        pub unsafe fn $dec_lt(a: $ty, b: $ty) -> u8 {
            (a < b) as u8
        }

        #[inline]
        pub unsafe fn $dec_le(a: $ty, b: $ty) -> u8 {
            (a <= b) as u8
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
    lean_uint8_dec_le
);

define_uint_family!(
    u16,
    lean_uint16_of_nat,
    lean_uint16_of_nat_mk,
    lean_uint16_to_nat,
    lean_uint16_dec_eq,
    lean_uint16_dec_lt,
    lean_uint16_dec_le
);

define_uint_family!(
    u32,
    lean_uint32_of_nat,
    lean_uint32_of_nat_mk,
    lean_uint32_to_nat,
    lean_uint32_dec_eq,
    lean_uint32_dec_lt,
    lean_uint32_dec_le
);

define_uint_family!(
    u64,
    lean_uint64_of_nat,
    lean_uint64_of_nat_mk,
    lean_uint64_to_nat,
    lean_uint64_dec_eq,
    lean_uint64_dec_lt,
    lean_uint64_dec_le
);
