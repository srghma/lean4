use leanh_l1::{
    datatypes::{LEAN_MPZ_TAG, LeanObject, LeanScalarArray, LeanStringObject},
    emitted::{
        lean_box::lean_box, lean_ctor_get::lean_ctor_get, lean_dec::lean_dec, lean_inc::lean_inc,
    },
    r#priv::lean_ptr_tag::lean_ptr_tag,
    runtime_object_nat_int::{lean_mpz_eq, lean_mpz_hash},
};
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
    let sz = lean_object_data_byte_size(o);
    let header_sz = core::mem::size_of::<LeanObject>();
    let tag = lean_ptr_tag(o);
    if tag == LEAN_MPZ_TAG {
        let h_mpz = lean_mpz_hash(o) as u64;
        hash_combine(tag as u64, h_mpz)
    } else {
        let init = hash_combine(tag as u64, (*o).other as u64);
        let body = (o as *const u8).add(header_sz);
        let len = sz.saturating_sub(header_sz);
        hash_str(len, body, init)
    }
}

pub unsafe fn lean_state_sharecommon(
    tc: *mut LeanObject,
    s: *mut LeanObject,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let state = ShareCommonState::new(tc, s);
    let mut f = ShareCommonFn {
        state,
        children: Vec::new(),
        todo: Vec::new(),
    };

    if f.push_child(a) {
        let r = f.children[0];
        lean_inc(r);
        lean_dec(a);
        return f.state.pack(r);
    }

    while !f.todo.is_empty() {
        let curr = *f.todo.last().unwrap();
        match lean_ptr_tag(curr) {
            LEAN_CLOSURE_TAG => panic!("unreachable"),
            LEAN_ARRAY_TAG => f.visit_array(curr),
            LEAN_SCALAR_ARRAY_TAG => f.visit_sarray(curr),
            LEAN_STRING_TAG => f.visit_string(curr),
            LEAN_MPZ_TAG => f.visit_mpz(curr),
            LEAN_THUNK_TAG => panic!("unreachable"),
            LEAN_TASK_TAG => panic!("unreachable"),
            LEAN_PROMISE_TAG => panic!("unreachable"),
            LEAN_REF_TAG => panic!("unreachable"),
            LEAN_EXTERNAL_TAG => panic!("unreachable"),
            LEAN_RESERVED_TAG => panic!("unreachable"),
            _ => f.visit_ctor(curr),
        }
    }

    let o = f.state.map_find(a);
    assert_ne!(o, lean_box(0));
    let r = lean_ctor_get(o, 0);
    lean_inc(r);
    lean_dec(o);
    lean_dec(a);
    f.state.pack(r)
}

pub unsafe fn lean_sharecommon_quick(a: *mut LeanObject) -> *mut LeanObject {
    let mut quick = RustShareCommonQuick::new(false);
    quick.visit(a)
}
