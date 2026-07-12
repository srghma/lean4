use core::ptr;
use std::ffi::c_uchar;

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set,
        lean_ctor_set_uint64::lean_ctor_set_uint64, lean_obj_tag::lean_obj_tag,
    },
    r#priv::lean_string_cstr::lean_string_cstr,
    r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash,
};

pub const LEAN_NAME_ANONYMOUS_TAG: u8 = 0;
pub const LEAN_NAME_STRING_TAG: u32 = 1;
pub const LEAN_NAME_NUM_OBJECT_FIELDS: u32 = 2;
pub const LEAN_NAME_HASH_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;
pub const LEAN_NAME_HASH_OFFSET: usize = core::mem::size_of::<*mut LeanObject>() * 2;
pub const LEAN_NAME_ANONYMOUS_HASH: u64 = 1723;
pub const LEAN_STRING_HASH_SEED: u64 = 11;

pub unsafe fn lean_hash_str(len: usize, text: *const c_uchar, seed: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    const R: u32 = 47;

    let mut hash = seed ^ ((len as u64).wrapping_mul(M));
    let mut offset = 0;
    let end = (len / 8) * 8;

    while offset != end {
        let mut key = unsafe { ptr::read_unaligned(text.add(offset).cast::<u64>()) };
        offset += 8;

        key = key.wrapping_mul(M);
        key ^= key >> R;
        key = key.wrapping_mul(M);

        hash ^= key;
        hash = hash.wrapping_mul(M);
    }

    let tail = unsafe { text.add(offset) };
    match len & 7 {
        7 => {
            hash ^= (unsafe { *tail.add(6) } as u64) << 48;
            hash ^= (unsafe { *tail.add(5) } as u64) << 40;
            hash ^= (unsafe { *tail.add(4) } as u64) << 32;
            hash ^= (unsafe { *tail.add(3) } as u64) << 24;
            hash ^= (unsafe { *tail.add(2) } as u64) << 16;
            hash ^= (unsafe { *tail.add(1) } as u64) << 8;
            hash ^= unsafe { *tail } as u64;
            hash = hash.wrapping_mul(M);
        }
        6 => {
            hash ^= (unsafe { *tail.add(5) } as u64) << 40;
            hash ^= (unsafe { *tail.add(4) } as u64) << 32;
            hash ^= (unsafe { *tail.add(3) } as u64) << 24;
            hash ^= (unsafe { *tail.add(2) } as u64) << 16;
            hash ^= (unsafe { *tail.add(1) } as u64) << 8;
            hash ^= unsafe { *tail } as u64;
            hash = hash.wrapping_mul(M);
        }
        5 => {
            hash ^= (unsafe { *tail.add(4) } as u64) << 32;
            hash ^= (unsafe { *tail.add(3) } as u64) << 24;
            hash ^= (unsafe { *tail.add(2) } as u64) << 16;
            hash ^= (unsafe { *tail.add(1) } as u64) << 8;
            hash ^= unsafe { *tail } as u64;
            hash = hash.wrapping_mul(M);
        }
        4 => {
            hash ^= (unsafe { *tail.add(3) } as u64) << 24;
            hash ^= (unsafe { *tail.add(2) } as u64) << 16;
            hash ^= (unsafe { *tail.add(1) } as u64) << 8;
            hash ^= unsafe { *tail } as u64;
            hash = hash.wrapping_mul(M);
        }
        3 => {
            hash ^= (unsafe { *tail.add(2) } as u64) << 16;
            hash ^= (unsafe { *tail.add(1) } as u64) << 8;
            hash ^= unsafe { *tail } as u64;
            hash = hash.wrapping_mul(M);
        }
        2 => {
            hash ^= (unsafe { *tail.add(1) } as u64) << 8;
            hash ^= unsafe { *tail } as u64;
            hash = hash.wrapping_mul(M);
        }
        1 => {
            hash ^= unsafe { *tail } as u64;
            hash = hash.wrapping_mul(M);
        }
        _ => {}
    }

    hash ^= hash >> R;
    hash = hash.wrapping_mul(M);
    hash ^= hash >> R;
    hash
}

pub unsafe fn lean_string_hash(s: *const LeanObject) -> u64 {
    let s = leanh_l1::r#priv::lean_to_string::lean_to_string(s);
    let byte_len = (*s).m_size.saturating_sub(1);
    let text = lean_string_cstr(s as *const LeanObject).cast::<u8>();
    lean_hash_str(byte_len, text, LEAN_STRING_HASH_SEED)
}

// Mirrors emitted `l_Lean_Name_str___override` for
// `src/Init/Prelude.lean:4729-4731` (`@[export lean_name_mk_string] abbrev Name.mkStr := Name.str`).
pub unsafe fn lean_name_mk_string(
    prefix: *mut LeanObject,
    string: *mut LeanObject,
) -> *mut LeanObject {
    let prefix_hash = if lean_obj_tag(prefix) == LEAN_NAME_ANONYMOUS_TAG {
        LEAN_NAME_ANONYMOUS_HASH
    } else {
        leanh_l1::emitted::lean_ctor_get_uint64::lean_ctor_get_uint64(
            prefix,
            LEAN_NAME_HASH_OFFSET as u32,
        )
    };
    let string_hash = lean_string_hash(string);
    let hash = lean_uint64_mix_hash(prefix_hash, string_hash);

    let obj = lean_alloc_ctor(
        LEAN_NAME_STRING_TAG,
        LEAN_NAME_NUM_OBJECT_FIELDS,
        LEAN_NAME_HASH_SCALAR_SIZE,
    );
    lean_ctor_set(obj, 0, prefix);
    lean_ctor_set(obj, 1, string);
    lean_ctor_set_uint64(obj, LEAN_NAME_HASH_OFFSET, hash);
    obj
}
