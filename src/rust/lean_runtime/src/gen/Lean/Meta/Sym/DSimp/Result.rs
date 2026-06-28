// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Result
// Imports: Lean.Meta.Sym.DSimp.DSimpM
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimpM::{
    initialize_Lean_Meta_Sym_DSimp_DSimpM, runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [1 as *mut LeanObject],
    };
static mut l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_markAsDone(
    mut v_x_22_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_23_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_24_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_26_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_27_: u8 = 0;
    let mut v___x_28_: u8 = 0;
    let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_31_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_32_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_22_) == 0 {
                    lean_dec_ref_known(v_x_22_, 0);
                    v___x_23_ = l_Lean_Meta_Sym_DSimp_Result_markAsDone___closed__0;
                    return v___x_23_;
                } else {
                    v_e_x27_24_ = lean_ctor_get(v_x_22_, 0);
                    v_isSharedCheck_32_ = (!lean_is_exclusive(v_x_22_)) as u8;
                    if v_isSharedCheck_32_ == 0 {
                        v___x_26_ = v_x_22_;
                        v_isShared_27_ = v_isSharedCheck_32_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_e_x27_24_);
                        lean_dec(v_x_22_);
                        v___x_26_ = lean_box(0);
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
                    v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_31_, 0, v_e_x27_24_);
                    v___x_30_ = v_reuseFailAlloc_31_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_30_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_28_,
                );
                return v___x_30_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_getResultExpr(
    mut v_x_33_: *mut LeanObject,
    mut v_x_34_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_34_) == 0 {
        lean_inc_ref(v_x_33_);
        return v_x_33_;
    } else {
        let mut v_e_x27_35_: *mut LeanObject = core::ptr::null_mut();
        v_e_x27_35_ = lean_ctor_get(v_x_34_, 0);
        lean_inc_ref(v_e_x27_35_);
        return v_e_x27_35_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_getResultExpr___boxed(
    mut v_x_36_: *mut LeanObject,
    mut v_x_37_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_38_: *mut LeanObject = core::ptr::null_mut();
    v_res_38_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_x_36_, v_x_37_);
    lean_dec_ref(v_x_37_);
    lean_dec_ref(v_x_36_);
    return v_res_38_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Result(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Result(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Result(builtin);
}
