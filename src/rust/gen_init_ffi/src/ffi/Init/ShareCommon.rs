use leanh_l1::emitted::lean_is_scalar::lean_is_scalar;
use leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash;
use leanh_l1::{
    datatypes::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MPZ_TAG, LEAN_PROMISE_TAG,
        LEAN_REF_TAG, LEAN_RESERVED_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG,
        LEAN_THUNK_TAG, LeanObject,
    },
    emitted::{
        lean_box::lean_box, lean_ctor_get::lean_ctor_get, lean_dec::lean_dec, lean_inc::lean_inc,
    },
    r#priv::lean_ptr_tag::lean_ptr_tag,
    runtime_object_nat_int::{lean_mpz_eq, lean_mpz_hash},
};
use leanh_l1_initializers::todo_import_from_lean::lean_name_mk_string::lean_hash_str;

use crate::r#priv::lean_object_data_byte_size::lean_object_data_byte_size;
use crate::r#priv::sharecommon_data::ShareCommonFn;
use crate::r#priv::sharecommon_fn_push_child::sharecommon_fn_push_child;
use crate::r#priv::sharecommon_fn_visit_array::sharecommon_fn_visit_array;
use crate::r#priv::sharecommon_fn_visit_ctor::sharecommon_fn_visit_ctor;
use crate::r#priv::sharecommon_fn_visit_mpz::sharecommon_fn_visit_mpz;
use crate::r#priv::sharecommon_fn_visit_sarray::sharecommon_fn_visit_sarray;
use crate::r#priv::sharecommon_fn_visit_string::sharecommon_fn_visit_string;
use crate::r#priv::sharecommon_quick_new::sharecommon_quick_new;
use crate::r#priv::sharecommon_quick_visit::sharecommon_quick_visit;
use crate::r#priv::sharecommon_state_map_find::sharecommon_state_map_find;
use crate::r#priv::sharecommon_state_new::sharecommon_state_new;
use crate::r#priv::sharecommon_state_pack::sharecommon_state_pack;
// Generated stub file for Lean FFI imports
// Source: src/Init/ShareCommon.lean

pub unsafe fn lean_sharecommon_eq(o1: *mut LeanObject, o2: *mut LeanObject) -> bool {
    if o1 == o2 {
        return true;
    }
    let sz1 = lean_object_data_byte_size(o1);
    let sz2 = lean_object_data_byte_size(o2);
    if sz1 != sz2 {
        return false;
    }
    let tag = lean_ptr_tag(o1);
    if tag != lean_ptr_tag(o2) {
        return false;
    }
    if (*o1).other != (*o2).other {
        return false;
    }
    if tag == LEAN_MPZ_TAG {
        lean_mpz_eq(o1, o2)
    } else {
        let header_sz = core::mem::size_of::<LeanObject>();
        let body1 = (o1 as *const u8).add(header_sz);
        let body2 = (o2 as *const u8).add(header_sz);
        let len = sz1.saturating_sub(header_sz);
        if len == 0 {
            return true;
        }
        let res = libc::memcmp(body1.cast(), body2.cast(), len);
        res == 0
    }
}

pub unsafe fn lean_sharecommon_hash(o: *const LeanObject) -> u64 {
    assert!(!lean_is_scalar(o));
    let sz = lean_object_data_byte_size(o);
    let header_sz = core::mem::size_of::<LeanObject>();
    let tag = lean_ptr_tag(o);
    if tag == LEAN_MPZ_TAG {
        let h_mpz = lean_mpz_hash(o) as u64;
        lean_uint64_mix_hash(tag as u64, h_mpz)
    } else {
        let init = lean_uint64_mix_hash(tag as u64, (*o).other as u64);
        let body = (o as *const u8).add(header_sz);
        let len = sz.saturating_sub(header_sz);
        lean_hash_str(len, body, init)
    }
}

pub unsafe fn lean_state_sharecommon(
    tc: *mut LeanObject,
    s: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let state = sharecommon_state_new(tc, s);
    let mut f = ShareCommonFn {
        state,
        children: Vec::new(),
        todo: Vec::new(),
    };

    if sharecommon_fn_push_child(&mut f, a) {
        let r = f.children[0];
        lean_inc(r);
        lean_dec(a);
        return sharecommon_state_pack(&mut f.state, r);
    }

    while !f.todo.is_empty() {
        let curr = *f.todo.last().unwrap();
        match lean_ptr_tag(curr) {
            LEAN_CLOSURE_TAG => panic!("unreachable"),
            LEAN_ARRAY_TAG => sharecommon_fn_visit_array(&mut f, curr),
            LEAN_SCALAR_ARRAY_TAG => sharecommon_fn_visit_sarray(&mut f, curr),
            LEAN_STRING_TAG => sharecommon_fn_visit_string(&mut f, curr),
            LEAN_MPZ_TAG => sharecommon_fn_visit_mpz(&mut f, curr),
            LEAN_THUNK_TAG => panic!("unreachable"),
            LEAN_TASK_TAG => panic!("unreachable"),
            LEAN_PROMISE_TAG => panic!("unreachable"),
            LEAN_REF_TAG => panic!("unreachable"),
            LEAN_EXTERNAL_TAG => panic!("unreachable"),
            LEAN_RESERVED_TAG => panic!("unreachable"),
            _ => sharecommon_fn_visit_ctor(&mut f, curr),
        }
    }

    let o = sharecommon_state_map_find(&f.state, a);
    assert_ne!(o, lean_box(0));
    let r = lean_ctor_get(o, 0);
    lean_inc(r);
    lean_dec(o);
    lean_dec(a);
    sharecommon_state_pack(&mut f.state, r)
}

pub unsafe fn lean_sharecommon_quick(a: *mut LeanObject) -> *mut LeanObject {
    let mut quick = sharecommon_quick_new(false);
    sharecommon_quick_visit(&mut quick, a)
}
