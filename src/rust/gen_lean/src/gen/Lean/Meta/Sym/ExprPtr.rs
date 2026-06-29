// Lean compiler output
// Module: Lean.Meta.Sym.ExprPtr
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{initialize_Lean_Expr, runtime_initialize_Lean_Expr};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_shift_right, lean_usize_to_uint64,
};
use crate::lean_imports_rs::Init::Prelude::lean_usize_dec_eq;
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
pub static l_Lean_Meta_Sym_instHashableExprPtr___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_instHashableExprPtr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instHashableExprPtr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instHashableExprPtr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instHashableExprPtr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instBEqExprPtr___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instBEqExprPtr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instBEqExprPtr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instBEqExprPtr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instBEqExprPtr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
    mut v_a_34_: *mut crate::leanh::LeanObject,
    mut v_b_35_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_36_: usize = 0;
    let mut v___x_37_: usize = 0;
    let mut v___x_38_: u8 = 0;
    v___x_36_ = lean_ptr_addr(v_a_34_);
    v___x_37_ = lean_ptr_addr(v_b_35_);
    v___x_38_ = lean_usize_dec_eq(v___x_36_, v___x_37_);
    return v___x_38_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(
    mut v_a_39_: *mut crate::leanh::LeanObject,
    mut v_b_40_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_41_: u8 = 0;
    let mut v_r_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_41_ =
        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_39_, v_b_40_);
    crate::leanh::lean_dec_ref(v_b_40_);
    crate::leanh::lean_dec_ref(v_a_39_);
    v_r_42_ = crate::leanh::lean_box((v_res_41_) as usize);
    return v_r_42_;
}
pub unsafe fn l_Lean_Meta_Sym_isSameExpr(
    mut v_a_43_: *mut crate::leanh::LeanObject,
    mut v_b_44_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_45_: u8 = 0;
    v___x_45_ =
        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_43_, v_b_44_);
    return v___x_45_;
}
pub unsafe fn l_Lean_Meta_Sym_isSameExpr___boxed(
    mut v_a_46_: *mut crate::leanh::LeanObject,
    mut v_b_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_48_: u8 = 0;
    let mut v_r_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Lean_Meta_Sym_isSameExpr(v_a_46_, v_b_47_);
    crate::leanh::lean_dec_ref(v_b_47_);
    crate::leanh::lean_dec_ref(v_a_46_);
    v_r_49_ = crate::leanh::lean_box((v_res_48_) as usize);
    return v_r_49_;
}
pub unsafe fn l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(
    mut v_e_50_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_51_: usize = 0;
    let mut v___x_52_: usize = 0;
    let mut v___x_53_: usize = 0;
    let mut v___x_54_: u64 = 0;
    v___x_51_ = lean_ptr_addr(v_e_50_);
    v___x_52_ = 3usize;
    v___x_53_ = lean_usize_shift_right(v___x_51_, v___x_52_);
    v___x_54_ = lean_usize_to_uint64(v___x_53_);
    return v___x_54_;
}
pub unsafe fn l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(
    mut v_e_55_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_56_: u64 = 0;
    let mut v_r_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_55_);
    crate::leanh::lean_dec_ref(v_e_55_);
    v_r_57_ = crate::leanh::lean_box_uint64(v_res_56_);
    return v_r_57_;
}
pub unsafe fn l_Lean_Meta_Sym_hashPtrExpr(mut v_e_58_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_59_: u64 = 0;
    v___x_59_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_58_);
    return v___x_59_;
}
pub unsafe fn l_Lean_Meta_Sym_hashPtrExpr___boxed(
    mut v_e_60_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_61_: u64 = 0;
    let mut v_r_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_61_ = l_Lean_Meta_Sym_hashPtrExpr(v_e_60_);
    crate::leanh::lean_dec_ref(v_e_60_);
    v_r_62_ = crate::leanh::lean_box_uint64(v_res_61_);
    return v_r_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_ExprPtr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_ExprPtr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_ExprPtr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_ExprPtr(builtin);
}
