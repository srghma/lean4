// Lean compiler output
// Module: Lean.Elab.MatchAltView
// Imports: Lean.Elab.Term
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
pub static l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Term_instInhabitedMatchAltView_default(
    mut v_k_19_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_20_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_20_ = l_Lean_Elab_Term_instInhabitedMatchAltView_default___closed__1;
    return v___x_20_;
}
pub unsafe fn l_Lean_Elab_Term_instInhabitedMatchAltView_default___boxed(
    mut v_k_21_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_22_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_22_ = l_Lean_Elab_Term_instInhabitedMatchAltView_default(v_k_21_);
    leanh::lean_dec(v_k_21_);
    return v_res_22_;
}
pub unsafe fn l_Lean_Elab_Term_instInhabitedMatchAltView(
    mut v_a_23_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_24_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_24_ = l_Lean_Elab_Term_instInhabitedMatchAltView_default(v_a_23_);
    return v___x_24_;
}
pub unsafe fn l_Lean_Elab_Term_instInhabitedMatchAltView___boxed(
    mut v_a_25_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_26_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_26_ = l_Lean_Elab_Term_instInhabitedMatchAltView(v_a_25_);
    leanh::lean_dec(v_a_25_);
    return v_res_26_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_MatchAltView(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_MatchAltView(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_MatchAltView(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MatchAltView(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_MatchAltView(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_MatchAltView(builtin);
}