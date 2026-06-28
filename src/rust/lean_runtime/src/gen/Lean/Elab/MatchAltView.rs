// Lean compiler output
// Module: Lean.Elab.MatchAltView
// Imports: Lean.Elab.Term
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
pub static l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Term_instInhabitedMatchAltView_default(
    mut v_k_19_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_20_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_20_ = l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1;
    return v___x_20_;
}
pub unsafe fn l_Lean_Elab_Term_instInhabitedMatchAltView_default___boxed(
    mut v_k_21_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_22_ = l_Lean_Elab_Term_instInhabitedMatchAltView_default(v_k_21_);
    crate::leanh::lean_dec(v_k_21_);
    return v_res_22_;
}
pub unsafe fn l_Lean_Elab_Term_instInhabitedMatchAltView(
    mut v_a_23_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_24_ = l_Lean_Elab_Term_instInhabitedMatchAltView_default(v_a_23_);
    return v___x_24_;
}
pub unsafe fn l_Lean_Elab_Term_instInhabitedMatchAltView___boxed(
    mut v_a_25_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_26_ = l_Lean_Elab_Term_instInhabitedMatchAltView(v_a_25_);
    crate::leanh::lean_dec(v_a_25_);
    return v_res_26_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_MatchAltView(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_MatchAltView(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_MatchAltView(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MatchAltView(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_MatchAltView(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_MatchAltView(builtin);
}
