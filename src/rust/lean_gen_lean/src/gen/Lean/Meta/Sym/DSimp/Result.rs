// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Result
// Imports: Lean.Meta.Sym.DSimp.DSimpM
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimpM::{
    initialize_Lean_Meta_Sym_DSimp_DSimpM, runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM,
};
pub static l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [1 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_markAsDone(
    mut v_x_22_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_27_: u8 = 0;
    let mut v___x_28_: u8 = 0;
    let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_32_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_22_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_x_22_, 0);
                    v___x_23_ = l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0;
                    return v___x_23_;
                } else {
                    v_e_x27_24_ = crate::leanh::lean_ctor_get(v_x_22_, 0);
                    v_isSharedCheck_32_ = (!crate::leanh::lean_is_exclusive(v_x_22_)) as u8;
                    if v_isSharedCheck_32_ == 0 {
                        v___x_26_ = v_x_22_;
                        v_isShared_27_ = v_isSharedCheck_32_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_e_x27_24_);
                        crate::leanh::lean_dec(v_x_22_);
                        v___x_26_ = crate::leanh::lean_box(0);
                        v_isShared_27_ = v_isSharedCheck_32_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_28_ = 1;
                if v_isShared_27_ == 0 {
                    v___x_30_ = v___x_26_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_31_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_31_, 0, v_e_x27_24_);
                    v___x_30_ = v_reuseFailAlloc_31_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_30_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_28_,
                );
                return v___x_30_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_getResultExpr(
    mut v_x_33_: *mut crate::leanh::LeanObject,
    mut v_x_34_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_34_) == 0 {
        crate::leanh::lean_inc_ref(v_x_33_);
        return v_x_33_;
    } else {
        let mut v_e_x27_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_e_x27_35_ = crate::leanh::lean_ctor_get(v_x_34_, 0);
        crate::leanh::lean_inc_ref(v_e_x27_35_);
        return v_e_x27_35_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_getResultExpr___boxed(
    mut v_x_36_: *mut crate::leanh::LeanObject,
    mut v_x_37_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_38_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_x_36_, v_x_37_);
    crate::leanh::lean_dec_ref(v_x_37_);
    crate::leanh::lean_dec_ref(v_x_36_);
    return v_res_38_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Result(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Result(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Result(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Result(builtin);
}
