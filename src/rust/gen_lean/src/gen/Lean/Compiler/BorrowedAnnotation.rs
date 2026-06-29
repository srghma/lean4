// Lean compiler output
// Module: Lean.Compiler.BorrowedAnnotation
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_annotation_x3f, l_Lean_mkAnnotation, runtime_initialize_Lean_Expr,
};
pub static l_Lean_markBorrowed___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [98, 111, 114, 114, 111, 119, 101, 100, 0],
    };
static mut l_Lean_markBorrowed___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_markBorrowed___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_markBorrowed___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_markBorrowed___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5493537939071954145 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_markBorrowed___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_markBorrowed___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_markBorrowed(
    mut v_e_18_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_19_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_20_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_19_ = l_Lean_markBorrowed___closed__1;
    v___x_20_ = l_Lean_mkAnnotation(v___x_19_, v_e_18_);
    return v___x_20_;
}
pub unsafe fn l_Lean_isMarkedBorrowed(mut v_e_21_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_22_ = l_Lean_markBorrowed___closed__1;
    v___x_23_ = l_Lean_annotation_x3f(v___x_22_, v_e_21_);
    if crate::leanh::lean_obj_tag(v___x_23_) == 0 {
        let mut v___x_24_: u8 = 0;
        v___x_24_ = 0;
        return v___x_24_;
    } else {
        let mut v___x_25_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_23_, 1);
        v___x_25_ = 1;
        return v___x_25_;
    }
}
pub unsafe fn l_Lean_isMarkedBorrowed___boxed(
    mut v_e_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_27_: u8 = 0;
    let mut v_r_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_27_ = l_Lean_isMarkedBorrowed(v_e_26_);
    crate::leanh::lean_dec_ref(v_e_26_);
    v_r_28_ = crate::leanh::lean_box((v_res_27_) as usize);
    return v_r_28_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_BorrowedAnnotation(
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
pub unsafe fn meta_initialize_Lean_Compiler_BorrowedAnnotation(
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
pub unsafe fn initialize_Lean_Compiler_BorrowedAnnotation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Compiler_BorrowedAnnotation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_BorrowedAnnotation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_BorrowedAnnotation(builtin);
}
