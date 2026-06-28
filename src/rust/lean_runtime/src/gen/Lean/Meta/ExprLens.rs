// Lean compiler output
// Module: Lean.Meta.ExprLens
// Imports: Lean.SubExpr
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::l_Array_size___boxed;
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl,
    l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl, l_Lean_Expr_app___override,
    l_Lean_Expr_forallE___override, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_instBEqBinderInfo_beq,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_inferType___boxed, l_Lean_Meta_mapLetDecl___redArg,
    l_Lean_Meta_mkForallFVars___boxed, l_Lean_Meta_mkLambdaFVars___boxed,
    l_Lean_Meta_withLetDecl___redArg, l_Lean_Meta_withLocalDecl___redArg,
};
use crate::r#gen::Lean::SubExpr::{
    initialize_Lean_SubExpr, l_Lean_SubExpr_Pos_foldlM___redArg, l_Lean_SubExpr_Pos_toArray,
    runtime_initialize_Lean_SubExpr,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::{lean_expr_instantiate_rev, lean_expr_instantiate1};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 99, 111, 111, 114, 100, 105, 110, 97, 116, 101, 32, 0,
    ],
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 102, 111, 114, 32, 0],
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4_value:
    LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        76, 101, 110, 115, 105, 110, 103, 32, 111, 110, 32, 116, 121, 112, 101, 115, 32, 105, 115,
        32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0_value:
    LeanStringObject<45> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        73, 110, 116, 101, 114, 110, 97, 108, 58, 32, 84, 121, 112, 101, 115, 32, 115, 104, 111,
        117, 108, 100, 32, 98, 101, 32, 104, 97, 110, 100, 108, 101, 100, 32, 98, 121, 32, 118,
        105, 101, 119, 65, 117, 120, 0,
    ],
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        66, 97, 100, 32, 99, 111, 111, 114, 100, 105, 110, 97, 116, 101, 32, 0,
    ],
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2_value:
    LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        67, 97, 110, 39, 116, 32, 118, 105, 101, 119, 82, 97, 119, 32, 116, 104, 101, 32, 116, 121,
        112, 101, 32, 111, 102, 32, 0,
    ],
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Core_viewBinders___redArg___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Core_viewBinders___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Core_viewBinders___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Core_numBinders___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_size___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Core_numBinders___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Core_numBinders___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(
    mut v_body_986_: *mut LeanObject,
    mut v_g_987_: *mut LeanObject,
    mut v_x_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    v___x_989_ = lean_expr_instantiate1(v_body_986_, v_x_988_);
    v___x_990_ = lean_apply_1(v_g_987_, v___x_989_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0___boxed(
    mut v_body_991_: *mut LeanObject,
    mut v_g_992_: *mut LeanObject,
    mut v_x_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_994_: *mut LeanObject = core::ptr::null_mut();
    v_res_994_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(
        v_body_991_,
        v_g_992_,
        v_x_993_,
    );
    lean_dec_ref(v_x_993_);
    lean_dec_ref(v_body_991_);
    return v_res_994_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(
    mut v_fn_995_: *mut LeanObject,
    mut v_toPure_996_: *mut LeanObject,
    mut v_e_997_: *mut LeanObject,
    mut v_arg_998_: *mut LeanObject,
    mut v_____do__lift_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1001_: u8 = 0;
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: usize = 0;
    let mut v___x_1009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1005_ = lean_ptr_addr(v_fn_995_);
                v___x_1006_ = lean_usize_dec_eq(v___x_1005_, v___x_1005_);
                if v___x_1006_ == 0 {
                    v___y_1001_ = v___x_1006_;
                    state = 1;
                    continue;
                } else {
                    v___x_1007_ = lean_ptr_addr(v_arg_998_);
                    v___x_1008_ = lean_ptr_addr(v_____do__lift_999_);
                    v___x_1009_ = lean_usize_dec_eq(v___x_1007_, v___x_1008_);
                    v___y_1001_ = v___x_1009_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1001_ == 0 {
                    lean_dec_ref(v_e_997_);
                    v___x_1002_ = l_Lean_Expr_app___override(v_fn_995_, v_____do__lift_999_);
                    v___x_1003_ = lean_apply_2(v_toPure_996_, lean_box(0), v___x_1002_);
                    return v___x_1003_;
                } else {
                    lean_dec_ref(v_____do__lift_999_);
                    lean_dec_ref(v_fn_995_);
                    v___x_1004_ = lean_apply_2(v_toPure_996_, lean_box(0), v_e_997_);
                    return v___x_1004_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed(
    mut v_fn_1010_: *mut LeanObject,
    mut v_toPure_1011_: *mut LeanObject,
    mut v_e_1012_: *mut LeanObject,
    mut v_arg_1013_: *mut LeanObject,
    mut v_____do__lift_1014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1015_: *mut LeanObject = core::ptr::null_mut();
    v_res_1015_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(
        v_fn_1010_,
        v_toPure_1011_,
        v_e_1012_,
        v_arg_1013_,
        v_____do__lift_1014_,
    );
    lean_dec_ref(v_arg_1013_);
    return v_res_1015_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(
    mut v___x_1016_: *mut LeanObject,
    mut v___x_1017_: u8,
    mut v___x_1018_: u8,
    mut v_inst_1019_: *mut LeanObject,
    mut v_____do__lift_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1021_: u8 = 0;
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    v___x_1021_ = 1;
    v___x_1022_ = lean_box((v___x_1017_) as usize);
    v___x_1023_ = lean_box((v___x_1018_) as usize);
    v___x_1024_ = lean_box((v___x_1017_) as usize);
    v___x_1025_ = lean_box((v___x_1018_) as usize);
    v___x_1026_ = lean_box((v___x_1021_) as usize);
    v___x_1027_ = lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    lean_closure_set(v___x_1027_, 0, v___x_1016_);
    lean_closure_set(v___x_1027_, 1, v_____do__lift_1020_);
    lean_closure_set(v___x_1027_, 2, v___x_1022_);
    lean_closure_set(v___x_1027_, 3, v___x_1023_);
    lean_closure_set(v___x_1027_, 4, v___x_1024_);
    lean_closure_set(v___x_1027_, 5, v___x_1025_);
    lean_closure_set(v___x_1027_, 6, v___x_1026_);
    v___x_1028_ = lean_apply_2(v_inst_1019_, lean_box(0), v___x_1027_);
    return v___x_1028_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed(
    mut v___x_1029_: *mut LeanObject,
    mut v___x_1030_: *mut LeanObject,
    mut v___x_1031_: *mut LeanObject,
    mut v_inst_1032_: *mut LeanObject,
    mut v_____do__lift_1033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1064__boxed_1034_: u8 = 0;
    let mut v___x_1065__boxed_1035_: u8 = 0;
    let mut v_res_1036_: *mut LeanObject = core::ptr::null_mut();
    v___x_1064__boxed_1034_ = (lean_unbox(v___x_1030_) as u8);
    v___x_1065__boxed_1035_ = (lean_unbox(v___x_1031_) as u8);
    v_res_1036_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(
        v___x_1029_,
        v___x_1064__boxed_1034_,
        v___x_1065__boxed_1035_,
        v_inst_1032_,
        v_____do__lift_1033_,
    );
    return v_res_1036_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(
    mut v___x_1037_: *mut LeanObject,
    mut v___x_1038_: u8,
    mut v___x_1039_: u8,
    mut v_inst_1040_: *mut LeanObject,
    mut v_body_1041_: *mut LeanObject,
    mut v_g_1042_: *mut LeanObject,
    mut v_toBind_1043_: *mut LeanObject,
    mut v_x_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1045_ = lean_mk_empty_array_with_capacity(v___x_1037_);
    v___x_1046_ = lean_array_push(v___x_1045_, v_x_1044_);
    v___x_1047_ = lean_box((v___x_1038_) as usize);
    v___x_1048_ = lean_box((v___x_1039_) as usize);
    lean_inc_ref(v___x_1046_);
    v___f_1049_ = lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1049_, 0, v___x_1046_);
    lean_closure_set(v___f_1049_, 1, v___x_1047_);
    lean_closure_set(v___f_1049_, 2, v___x_1048_);
    lean_closure_set(v___f_1049_, 3, v_inst_1040_);
    v___x_1050_ = lean_expr_instantiate_rev(v_body_1041_, v___x_1046_);
    lean_dec_ref(v___x_1046_);
    v___x_1051_ = lean_apply_1(v_g_1042_, v___x_1050_);
    v___x_1052_ = lean_apply_4(
        v_toBind_1043_,
        lean_box(0),
        lean_box(0),
        v___x_1051_,
        v___f_1049_,
    );
    return v___x_1052_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed(
    mut v___x_1053_: *mut LeanObject,
    mut v___x_1054_: *mut LeanObject,
    mut v___x_1055_: *mut LeanObject,
    mut v_inst_1056_: *mut LeanObject,
    mut v_body_1057_: *mut LeanObject,
    mut v_g_1058_: *mut LeanObject,
    mut v_toBind_1059_: *mut LeanObject,
    mut v_x_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1095__boxed_1061_: u8 = 0;
    let mut v___x_1096__boxed_1062_: u8 = 0;
    let mut v_res_1063_: *mut LeanObject = core::ptr::null_mut();
    v___x_1095__boxed_1061_ = (lean_unbox(v___x_1054_) as u8);
    v___x_1096__boxed_1062_ = (lean_unbox(v___x_1055_) as u8);
    v_res_1063_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(
        v___x_1053_,
        v___x_1095__boxed_1061_,
        v___x_1096__boxed_1062_,
        v_inst_1056_,
        v_body_1057_,
        v_g_1058_,
        v_toBind_1059_,
        v_x_1060_,
    );
    lean_dec_ref(v_body_1057_);
    lean_dec(v___x_1053_);
    return v_res_1063_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(
    mut v___x_1064_: *mut LeanObject,
    mut v___x_1065_: u8,
    mut v___x_1066_: u8,
    mut v_inst_1067_: *mut LeanObject,
    mut v_____do__lift_1068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    v___x_1069_ = 1;
    v___x_1070_ = lean_box((v___x_1065_) as usize);
    v___x_1071_ = lean_box((v___x_1066_) as usize);
    v___x_1072_ = lean_box((v___x_1066_) as usize);
    v___x_1073_ = lean_box((v___x_1069_) as usize);
    v___x_1074_ = lean_alloc_closure(
        l_Lean_Meta_mkForallFVars___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___x_1074_, 0, v___x_1064_);
    lean_closure_set(v___x_1074_, 1, v_____do__lift_1068_);
    lean_closure_set(v___x_1074_, 2, v___x_1070_);
    lean_closure_set(v___x_1074_, 3, v___x_1071_);
    lean_closure_set(v___x_1074_, 4, v___x_1072_);
    lean_closure_set(v___x_1074_, 5, v___x_1073_);
    v___x_1075_ = lean_apply_2(v_inst_1067_, lean_box(0), v___x_1074_);
    return v___x_1075_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed(
    mut v___x_1076_: *mut LeanObject,
    mut v___x_1077_: *mut LeanObject,
    mut v___x_1078_: *mut LeanObject,
    mut v_inst_1079_: *mut LeanObject,
    mut v_____do__lift_1080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1126__boxed_1081_: u8 = 0;
    let mut v___x_1127__boxed_1082_: u8 = 0;
    let mut v_res_1083_: *mut LeanObject = core::ptr::null_mut();
    v___x_1126__boxed_1081_ = (lean_unbox(v___x_1077_) as u8);
    v___x_1127__boxed_1082_ = (lean_unbox(v___x_1078_) as u8);
    v_res_1083_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(
        v___x_1076_,
        v___x_1126__boxed_1081_,
        v___x_1127__boxed_1082_,
        v_inst_1079_,
        v_____do__lift_1080_,
    );
    return v_res_1083_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(
    mut v___x_1084_: *mut LeanObject,
    mut v___x_1085_: u8,
    mut v___x_1086_: u8,
    mut v_inst_1087_: *mut LeanObject,
    mut v_body_1088_: *mut LeanObject,
    mut v_g_1089_: *mut LeanObject,
    mut v_toBind_1090_: *mut LeanObject,
    mut v_x_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    v___x_1092_ = lean_mk_empty_array_with_capacity(v___x_1084_);
    v___x_1093_ = lean_array_push(v___x_1092_, v_x_1091_);
    v___x_1094_ = lean_box((v___x_1085_) as usize);
    v___x_1095_ = lean_box((v___x_1086_) as usize);
    lean_inc_ref(v___x_1093_);
    v___f_1096_ = lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1096_, 0, v___x_1093_);
    lean_closure_set(v___f_1096_, 1, v___x_1094_);
    lean_closure_set(v___f_1096_, 2, v___x_1095_);
    lean_closure_set(v___f_1096_, 3, v_inst_1087_);
    v___x_1097_ = lean_expr_instantiate_rev(v_body_1088_, v___x_1093_);
    lean_dec_ref(v___x_1093_);
    v___x_1098_ = lean_apply_1(v_g_1089_, v___x_1097_);
    v___x_1099_ = lean_apply_4(
        v_toBind_1090_,
        lean_box(0),
        lean_box(0),
        v___x_1098_,
        v___f_1096_,
    );
    return v___x_1099_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed(
    mut v___x_1100_: *mut LeanObject,
    mut v___x_1101_: *mut LeanObject,
    mut v___x_1102_: *mut LeanObject,
    mut v_inst_1103_: *mut LeanObject,
    mut v_body_1104_: *mut LeanObject,
    mut v_g_1105_: *mut LeanObject,
    mut v_toBind_1106_: *mut LeanObject,
    mut v_x_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1155__boxed_1108_: u8 = 0;
    let mut v___x_1156__boxed_1109_: u8 = 0;
    let mut v_res_1110_: *mut LeanObject = core::ptr::null_mut();
    v___x_1155__boxed_1108_ = (lean_unbox(v___x_1101_) as u8);
    v___x_1156__boxed_1109_ = (lean_unbox(v___x_1102_) as u8);
    v_res_1110_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(
        v___x_1100_,
        v___x_1155__boxed_1108_,
        v___x_1156__boxed_1109_,
        v_inst_1103_,
        v_body_1104_,
        v_g_1105_,
        v_toBind_1106_,
        v_x_1107_,
    );
    lean_dec_ref(v_body_1104_);
    lean_dec(v___x_1100_);
    return v_res_1110_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(
    mut v_declName_1111_: *mut LeanObject,
    mut v_type_1112_: *mut LeanObject,
    mut v_body_1113_: *mut LeanObject,
    mut v_nondep_1114_: u8,
    mut v_toPure_1115_: *mut LeanObject,
    mut v_e_1116_: *mut LeanObject,
    mut v_value_1117_: *mut LeanObject,
    mut v_____do__lift_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1120_: u8 = 0;
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: usize = 0;
    let mut v___x_1124_: u8 = 0;
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: usize = 0;
    let mut v___x_1129_: u8 = 0;
    let mut v___x_1130_: usize = 0;
    let mut v___x_1131_: usize = 0;
    let mut v___x_1132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1128_ = lean_ptr_addr(v_type_1112_);
                v___x_1129_ = lean_usize_dec_eq(v___x_1128_, v___x_1128_);
                if v___x_1129_ == 0 {
                    v___y_1120_ = v___x_1129_;
                    state = 1;
                    continue;
                } else {
                    v___x_1130_ = lean_ptr_addr(v_value_1117_);
                    v___x_1131_ = lean_ptr_addr(v_____do__lift_1118_);
                    v___x_1132_ = lean_usize_dec_eq(v___x_1130_, v___x_1131_);
                    v___y_1120_ = v___x_1132_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1120_ == 0 {
                    lean_dec_ref(v_e_1116_);
                    v___x_1121_ = l_Lean_Expr_letE___override(
                        v_declName_1111_,
                        v_type_1112_,
                        v_____do__lift_1118_,
                        v_body_1113_,
                        v_nondep_1114_,
                    );
                    v___x_1122_ = lean_apply_2(v_toPure_1115_, lean_box(0), v___x_1121_);
                    return v___x_1122_;
                } else {
                    v___x_1123_ = lean_ptr_addr(v_body_1113_);
                    v___x_1124_ = lean_usize_dec_eq(v___x_1123_, v___x_1123_);
                    if v___x_1124_ == 0 {
                        lean_dec_ref(v_e_1116_);
                        v___x_1125_ = l_Lean_Expr_letE___override(
                            v_declName_1111_,
                            v_type_1112_,
                            v_____do__lift_1118_,
                            v_body_1113_,
                            v_nondep_1114_,
                        );
                        v___x_1126_ = lean_apply_2(v_toPure_1115_, lean_box(0), v___x_1125_);
                        return v___x_1126_;
                    } else {
                        lean_dec_ref(v_____do__lift_1118_);
                        lean_dec_ref(v_body_1113_);
                        lean_dec_ref(v_type_1112_);
                        lean_dec(v_declName_1111_);
                        v___x_1127_ = lean_apply_2(v_toPure_1115_, lean_box(0), v_e_1116_);
                        return v___x_1127_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed(
    mut v_declName_1133_: *mut LeanObject,
    mut v_type_1134_: *mut LeanObject,
    mut v_body_1135_: *mut LeanObject,
    mut v_nondep_1136_: *mut LeanObject,
    mut v_toPure_1137_: *mut LeanObject,
    mut v_e_1138_: *mut LeanObject,
    mut v_value_1139_: *mut LeanObject,
    mut v_____do__lift_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_1188__boxed_1141_: u8 = 0;
    let mut v_res_1142_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_1188__boxed_1141_ = (lean_unbox(v_nondep_1136_) as u8);
    v_res_1142_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(
        v_declName_1133_,
        v_type_1134_,
        v_body_1135_,
        v_nondep_1188__boxed_1141_,
        v_toPure_1137_,
        v_e_1138_,
        v_value_1139_,
        v_____do__lift_1140_,
    );
    lean_dec_ref(v_value_1139_);
    return v_res_1142_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(
    mut v_arg_1143_: *mut LeanObject,
    mut v_toPure_1144_: *mut LeanObject,
    mut v_e_1145_: *mut LeanObject,
    mut v_fn_1146_: *mut LeanObject,
    mut v_____do__lift_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1149_: u8 = 0;
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: usize = 0;
    let mut v___x_1154_: usize = 0;
    let mut v___x_1155_: u8 = 0;
    let mut v___x_1156_: usize = 0;
    let mut v___x_1157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1153_ = lean_ptr_addr(v_fn_1146_);
                v___x_1154_ = lean_ptr_addr(v_____do__lift_1147_);
                v___x_1155_ = lean_usize_dec_eq(v___x_1153_, v___x_1154_);
                if v___x_1155_ == 0 {
                    v___y_1149_ = v___x_1155_;
                    state = 1;
                    continue;
                } else {
                    v___x_1156_ = lean_ptr_addr(v_arg_1143_);
                    v___x_1157_ = lean_usize_dec_eq(v___x_1156_, v___x_1156_);
                    v___y_1149_ = v___x_1157_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1149_ == 0 {
                    lean_dec_ref(v_e_1145_);
                    v___x_1150_ = l_Lean_Expr_app___override(v_____do__lift_1147_, v_arg_1143_);
                    v___x_1151_ = lean_apply_2(v_toPure_1144_, lean_box(0), v___x_1150_);
                    return v___x_1151_;
                } else {
                    lean_dec_ref(v_____do__lift_1147_);
                    lean_dec_ref(v_arg_1143_);
                    v___x_1152_ = lean_apply_2(v_toPure_1144_, lean_box(0), v_e_1145_);
                    return v___x_1152_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed(
    mut v_arg_1158_: *mut LeanObject,
    mut v_toPure_1159_: *mut LeanObject,
    mut v_e_1160_: *mut LeanObject,
    mut v_fn_1161_: *mut LeanObject,
    mut v_____do__lift_1162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1163_: *mut LeanObject = core::ptr::null_mut();
    v_res_1163_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(
        v_arg_1158_,
        v_toPure_1159_,
        v_e_1160_,
        v_fn_1161_,
        v_____do__lift_1162_,
    );
    lean_dec_ref(v_fn_1161_);
    return v_res_1163_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(
    mut v_binderName_1164_: *mut LeanObject,
    mut v_body_1165_: *mut LeanObject,
    mut v_binderInfo_1166_: u8,
    mut v_toPure_1167_: *mut LeanObject,
    mut v_e_1168_: *mut LeanObject,
    mut v_binderType_1169_: *mut LeanObject,
    mut v_____do__lift_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1172_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: usize = 0;
    let mut v___x_1180_: usize = 0;
    let mut v___x_1181_: u8 = 0;
    let mut v___x_1182_: usize = 0;
    let mut v___x_1183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1179_ = lean_ptr_addr(v_binderType_1169_);
                v___x_1180_ = lean_ptr_addr(v_____do__lift_1170_);
                v___x_1181_ = lean_usize_dec_eq(v___x_1179_, v___x_1180_);
                if v___x_1181_ == 0 {
                    v___y_1172_ = v___x_1181_;
                    state = 1;
                    continue;
                } else {
                    v___x_1182_ = lean_ptr_addr(v_body_1165_);
                    v___x_1183_ = lean_usize_dec_eq(v___x_1182_, v___x_1182_);
                    v___y_1172_ = v___x_1183_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1172_ == 0 {
                    lean_dec_ref(v_e_1168_);
                    v___x_1173_ = l_Lean_Expr_lam___override(
                        v_binderName_1164_,
                        v_____do__lift_1170_,
                        v_body_1165_,
                        v_binderInfo_1166_,
                    );
                    v___x_1174_ = lean_apply_2(v_toPure_1167_, lean_box(0), v___x_1173_);
                    return v___x_1174_;
                } else {
                    v___x_1175_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1166_, v_binderInfo_1166_);
                    if v___x_1175_ == 0 {
                        lean_dec_ref(v_e_1168_);
                        v___x_1176_ = l_Lean_Expr_lam___override(
                            v_binderName_1164_,
                            v_____do__lift_1170_,
                            v_body_1165_,
                            v_binderInfo_1166_,
                        );
                        v___x_1177_ = lean_apply_2(v_toPure_1167_, lean_box(0), v___x_1176_);
                        return v___x_1177_;
                    } else {
                        lean_dec_ref(v_____do__lift_1170_);
                        lean_dec_ref(v_body_1165_);
                        lean_dec(v_binderName_1164_);
                        v___x_1178_ = lean_apply_2(v_toPure_1167_, lean_box(0), v_e_1168_);
                        return v___x_1178_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed(
    mut v_binderName_1184_: *mut LeanObject,
    mut v_body_1185_: *mut LeanObject,
    mut v_binderInfo_1186_: *mut LeanObject,
    mut v_toPure_1187_: *mut LeanObject,
    mut v_e_1188_: *mut LeanObject,
    mut v_binderType_1189_: *mut LeanObject,
    mut v_____do__lift_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderInfo_1262__boxed_1191_: u8 = 0;
    let mut v_res_1192_: *mut LeanObject = core::ptr::null_mut();
    v_binderInfo_1262__boxed_1191_ = (lean_unbox(v_binderInfo_1186_) as u8);
    v_res_1192_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(
        v_binderName_1184_,
        v_body_1185_,
        v_binderInfo_1262__boxed_1191_,
        v_toPure_1187_,
        v_e_1188_,
        v_binderType_1189_,
        v_____do__lift_1190_,
    );
    lean_dec_ref(v_binderType_1189_);
    return v_res_1192_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(
    mut v_binderName_1193_: *mut LeanObject,
    mut v_body_1194_: *mut LeanObject,
    mut v_binderInfo_1195_: u8,
    mut v_toPure_1196_: *mut LeanObject,
    mut v_e_1197_: *mut LeanObject,
    mut v_binderType_1198_: *mut LeanObject,
    mut v_____do__lift_1199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1201_: u8 = 0;
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: usize = 0;
    let mut v___x_1209_: usize = 0;
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: usize = 0;
    let mut v___x_1212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1208_ = lean_ptr_addr(v_binderType_1198_);
                v___x_1209_ = lean_ptr_addr(v_____do__lift_1199_);
                v___x_1210_ = lean_usize_dec_eq(v___x_1208_, v___x_1209_);
                if v___x_1210_ == 0 {
                    v___y_1201_ = v___x_1210_;
                    state = 1;
                    continue;
                } else {
                    v___x_1211_ = lean_ptr_addr(v_body_1194_);
                    v___x_1212_ = lean_usize_dec_eq(v___x_1211_, v___x_1211_);
                    v___y_1201_ = v___x_1212_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1201_ == 0 {
                    lean_dec_ref(v_e_1197_);
                    v___x_1202_ = l_Lean_Expr_forallE___override(
                        v_binderName_1193_,
                        v_____do__lift_1199_,
                        v_body_1194_,
                        v_binderInfo_1195_,
                    );
                    v___x_1203_ = lean_apply_2(v_toPure_1196_, lean_box(0), v___x_1202_);
                    return v___x_1203_;
                } else {
                    v___x_1204_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1195_, v_binderInfo_1195_);
                    if v___x_1204_ == 0 {
                        lean_dec_ref(v_e_1197_);
                        v___x_1205_ = l_Lean_Expr_forallE___override(
                            v_binderName_1193_,
                            v_____do__lift_1199_,
                            v_body_1194_,
                            v_binderInfo_1195_,
                        );
                        v___x_1206_ = lean_apply_2(v_toPure_1196_, lean_box(0), v___x_1205_);
                        return v___x_1206_;
                    } else {
                        lean_dec_ref(v_____do__lift_1199_);
                        lean_dec_ref(v_body_1194_);
                        lean_dec(v_binderName_1193_);
                        v___x_1207_ = lean_apply_2(v_toPure_1196_, lean_box(0), v_e_1197_);
                        return v___x_1207_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed(
    mut v_binderName_1213_: *mut LeanObject,
    mut v_body_1214_: *mut LeanObject,
    mut v_binderInfo_1215_: *mut LeanObject,
    mut v_toPure_1216_: *mut LeanObject,
    mut v_e_1217_: *mut LeanObject,
    mut v_binderType_1218_: *mut LeanObject,
    mut v_____do__lift_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderInfo_1303__boxed_1220_: u8 = 0;
    let mut v_res_1221_: *mut LeanObject = core::ptr::null_mut();
    v_binderInfo_1303__boxed_1220_ = (lean_unbox(v_binderInfo_1215_) as u8);
    v_res_1221_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(
        v_binderName_1213_,
        v_body_1214_,
        v_binderInfo_1303__boxed_1220_,
        v_toPure_1216_,
        v_e_1217_,
        v_binderType_1218_,
        v_____do__lift_1219_,
    );
    lean_dec_ref(v_binderType_1218_);
    return v_res_1221_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(
    mut v_declName_1222_: *mut LeanObject,
    mut v_value_1223_: *mut LeanObject,
    mut v_body_1224_: *mut LeanObject,
    mut v_nondep_1225_: u8,
    mut v_toPure_1226_: *mut LeanObject,
    mut v_e_1227_: *mut LeanObject,
    mut v_type_1228_: *mut LeanObject,
    mut v_____do__lift_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1231_: u8 = 0;
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: usize = 0;
    let mut v___x_1235_: u8 = 0;
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: usize = 0;
    let mut v___x_1240_: usize = 0;
    let mut v___x_1241_: u8 = 0;
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1239_ = lean_ptr_addr(v_type_1228_);
                v___x_1240_ = lean_ptr_addr(v_____do__lift_1229_);
                v___x_1241_ = lean_usize_dec_eq(v___x_1239_, v___x_1240_);
                if v___x_1241_ == 0 {
                    v___y_1231_ = v___x_1241_;
                    state = 1;
                    continue;
                } else {
                    v___x_1242_ = lean_ptr_addr(v_value_1223_);
                    v___x_1243_ = lean_usize_dec_eq(v___x_1242_, v___x_1242_);
                    v___y_1231_ = v___x_1243_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1231_ == 0 {
                    lean_dec_ref(v_e_1227_);
                    v___x_1232_ = l_Lean_Expr_letE___override(
                        v_declName_1222_,
                        v_____do__lift_1229_,
                        v_value_1223_,
                        v_body_1224_,
                        v_nondep_1225_,
                    );
                    v___x_1233_ = lean_apply_2(v_toPure_1226_, lean_box(0), v___x_1232_);
                    return v___x_1233_;
                } else {
                    v___x_1234_ = lean_ptr_addr(v_body_1224_);
                    v___x_1235_ = lean_usize_dec_eq(v___x_1234_, v___x_1234_);
                    if v___x_1235_ == 0 {
                        lean_dec_ref(v_e_1227_);
                        v___x_1236_ = l_Lean_Expr_letE___override(
                            v_declName_1222_,
                            v_____do__lift_1229_,
                            v_value_1223_,
                            v_body_1224_,
                            v_nondep_1225_,
                        );
                        v___x_1237_ = lean_apply_2(v_toPure_1226_, lean_box(0), v___x_1236_);
                        return v___x_1237_;
                    } else {
                        lean_dec_ref(v_____do__lift_1229_);
                        lean_dec_ref(v_body_1224_);
                        lean_dec_ref(v_value_1223_);
                        lean_dec(v_declName_1222_);
                        v___x_1238_ = lean_apply_2(v_toPure_1226_, lean_box(0), v_e_1227_);
                        return v___x_1238_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed(
    mut v_declName_1244_: *mut LeanObject,
    mut v_value_1245_: *mut LeanObject,
    mut v_body_1246_: *mut LeanObject,
    mut v_nondep_1247_: *mut LeanObject,
    mut v_toPure_1248_: *mut LeanObject,
    mut v_e_1249_: *mut LeanObject,
    mut v_type_1250_: *mut LeanObject,
    mut v_____do__lift_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_1345__boxed_1252_: u8 = 0;
    let mut v_res_1253_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_1345__boxed_1252_ = (lean_unbox(v_nondep_1247_) as u8);
    v_res_1253_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(
        v_declName_1244_,
        v_value_1245_,
        v_body_1246_,
        v_nondep_1345__boxed_1252_,
        v_toPure_1248_,
        v_e_1249_,
        v_type_1250_,
        v_____do__lift_1251_,
    );
    lean_dec_ref(v_type_1250_);
    return v_res_1253_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v___x_1255_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0;
    v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
    return v___x_1256_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    v___x_1258_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2;
    v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
    return v___x_1259_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4;
    v___x_1262_ = l_Lean_stringToMessageData(v___x_1261_);
    return v___x_1262_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(
    mut v_inst_1263_: *mut LeanObject,
    mut v_inst_1264_: *mut LeanObject,
    mut v_inst_1265_: *mut LeanObject,
    mut v_inst_1266_: *mut LeanObject,
    mut v_g_1267_: *mut LeanObject,
    mut v_n_1268_: *mut LeanObject,
    mut v_e_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: u8 = 0;
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v_expr_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1310_: u8 = 0;
    let mut v___f_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1323_: u8 = 0;
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1332_: u8 = 0;
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1342_: u8 = 0;
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1356_: u8 = 0;
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1364_: u8 = 0;
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1373_: u8 = 0;
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1283_ = lean_ctor_get(v_inst_1263_, 0);
                v_toBind_1284_ = lean_ctor_get(v_inst_1263_, 1);
                v_toFunctor_1285_ = lean_ctor_get(v_toApplicative_1283_, 0);
                v_toPure_1286_ = lean_ctor_get(v_toApplicative_1283_, 1);
                v___x_1294_ = lean_unsigned_to_nat(0);
                v___x_1295_ = lean_nat_dec_eq(v_n_1268_, v___x_1294_);
                if v___x_1295_ == 0 {
                    v___x_1296_ = lean_unsigned_to_nat(1);
                    v___x_1297_ = lean_nat_dec_eq(v_n_1268_, v___x_1296_);
                    if v___x_1297_ == 0 {
                        v___x_1298_ = lean_unsigned_to_nat(2);
                        v___x_1299_ = lean_nat_dec_eq(v_n_1268_, v___x_1298_);
                        if v___x_1299_ == 0 {
                            v___x_1300_ = lean_unsigned_to_nat(3);
                            v___x_1301_ = lean_nat_dec_eq(v_n_1268_, v___x_1300_);
                            if v___x_1301_ == 0 {
                                if lean_obj_tag(v_e_1269_) == 10 {
                                    v_expr_1302_ = lean_ctor_get(v_e_1269_, 1);
                                    lean_inc_ref(v_expr_1302_);
                                    v_n_1288_ = v_n_1268_;
                                    v_a_1289_ = v_expr_1302_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v_g_1267_);
                                    lean_dec_ref(v_inst_1265_);
                                    lean_dec(v_inst_1264_);
                                    v_c_1271_ = v_n_1268_;
                                    v_e_1272_ = v_e_1269_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_n_1268_);
                                if lean_obj_tag(v_e_1269_) == 10 {
                                    v_expr_1303_ = lean_ctor_get(v_e_1269_, 1);
                                    lean_inc_ref(v_expr_1303_);
                                    v_n_1288_ = v___x_1300_;
                                    v_a_1289_ = v_expr_1303_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec_ref(v_e_1269_);
                                    lean_dec(v_g_1267_);
                                    lean_dec_ref(v_inst_1265_);
                                    lean_dec(v_inst_1264_);
                                    v___x_1304_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5);
                                    v___x_1305_ = l_Lean_throwError___redArg(
                                        v_inst_1263_,
                                        v_inst_1266_,
                                        v___x_1304_,
                                    );
                                    return v___x_1305_;
                                }
                            }
                        } else {
                            lean_dec(v_n_1268_);
                            match lean_obj_tag(v_e_1269_) {
                                8 => {
                                    lean_dec_ref(v_inst_1266_);
                                    v_declName_1306_ = lean_ctor_get(v_e_1269_, 0);
                                    lean_inc(v_declName_1306_);
                                    v_type_1307_ = lean_ctor_get(v_e_1269_, 1);
                                    lean_inc_ref(v_type_1307_);
                                    v_value_1308_ = lean_ctor_get(v_e_1269_, 2);
                                    lean_inc_ref(v_value_1308_);
                                    v_body_1309_ = lean_ctor_get(v_e_1269_, 3);
                                    lean_inc_ref(v_body_1309_);
                                    v_nondep_1310_ = lean_ctor_get_uint8(
                                        v_e_1269_,
                                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                                    );
                                    lean_dec_ref_known(v_e_1269_, 4);
                                    v___f_1311_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                                    lean_closure_set(v___f_1311_, 0, v_body_1309_);
                                    lean_closure_set(v___f_1311_, 1, v_g_1267_);
                                    v___x_1312_ = 0;
                                    v___x_1313_ = l_Lean_Meta_mapLetDecl___redArg(
                                        v_inst_1265_,
                                        v_inst_1263_,
                                        v_inst_1264_,
                                        v_declName_1306_,
                                        v_type_1307_,
                                        v_value_1308_,
                                        v___f_1311_,
                                        v_nondep_1310_,
                                        v___x_1312_,
                                        v___x_1297_,
                                    );
                                    return v___x_1313_;
                                }
                                10 => {
                                    v_expr_1314_ = lean_ctor_get(v_e_1269_, 1);
                                    lean_inc_ref(v_expr_1314_);
                                    v_n_1288_ = v___x_1298_;
                                    v_a_1289_ = v_expr_1314_;
                                    state = 2;
                                    continue;
                                }
                                _ => {
                                    lean_dec(v_g_1267_);
                                    lean_dec_ref(v_inst_1265_);
                                    lean_dec(v_inst_1264_);
                                    v_c_1271_ = v___x_1298_;
                                    v_e_1272_ = v_e_1269_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_n_1268_);
                        match lean_obj_tag(v_e_1269_) {
                            5 => {
                                lean_inc(v_toPure_1286_);
                                lean_inc(v_toBind_1284_);
                                lean_dec_ref(v_inst_1266_);
                                lean_dec_ref(v_inst_1265_);
                                lean_dec(v_inst_1264_);
                                lean_dec_ref(v_inst_1263_);
                                v_fn_1315_ = lean_ctor_get(v_e_1269_, 0);
                                lean_inc_ref(v_fn_1315_);
                                v_arg_1316_ = lean_ctor_get(v_e_1269_, 1);
                                lean_inc_ref_n(v_arg_1316_, 2);
                                v___f_1317_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 4);
                                lean_closure_set(v___f_1317_, 0, v_fn_1315_);
                                lean_closure_set(v___f_1317_, 1, v_toPure_1286_);
                                lean_closure_set(v___f_1317_, 2, v_e_1269_);
                                lean_closure_set(v___f_1317_, 3, v_arg_1316_);
                                v___x_1318_ = lean_apply_1(v_g_1267_, v_arg_1316_);
                                v___x_1319_ = lean_apply_4(
                                    v_toBind_1284_,
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_1318_,
                                    v___f_1317_,
                                );
                                return v___x_1319_;
                            }
                            6 => {
                                lean_dec_ref(v_inst_1266_);
                                v_binderName_1320_ = lean_ctor_get(v_e_1269_, 0);
                                lean_inc(v_binderName_1320_);
                                v_binderType_1321_ = lean_ctor_get(v_e_1269_, 1);
                                lean_inc_ref(v_binderType_1321_);
                                v_body_1322_ = lean_ctor_get(v_e_1269_, 2);
                                lean_inc_ref(v_body_1322_);
                                v_binderInfo_1323_ = lean_ctor_get_uint8(
                                    v_e_1269_,
                                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                                );
                                lean_dec_ref_known(v_e_1269_, 3);
                                v___x_1324_ = lean_box((v___x_1295_) as usize);
                                v___x_1325_ = lean_box((v___x_1297_) as usize);
                                lean_inc(v_toBind_1284_);
                                v___f_1326_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed as *mut core::ffi::c_void, 8, 7);
                                lean_closure_set(v___f_1326_, 0, v___x_1296_);
                                lean_closure_set(v___f_1326_, 1, v___x_1324_);
                                lean_closure_set(v___f_1326_, 2, v___x_1325_);
                                lean_closure_set(v___f_1326_, 3, v_inst_1264_);
                                lean_closure_set(v___f_1326_, 4, v_body_1322_);
                                lean_closure_set(v___f_1326_, 5, v_g_1267_);
                                lean_closure_set(v___f_1326_, 6, v_toBind_1284_);
                                v___x_1327_ = 0;
                                v___x_1328_ = l_Lean_Meta_withLocalDecl___redArg(
                                    v_inst_1265_,
                                    v_inst_1263_,
                                    v_binderName_1320_,
                                    v_binderInfo_1323_,
                                    v_binderType_1321_,
                                    v___f_1326_,
                                    v___x_1327_,
                                );
                                return v___x_1328_;
                            }
                            7 => {
                                lean_dec_ref(v_inst_1266_);
                                v_binderName_1329_ = lean_ctor_get(v_e_1269_, 0);
                                lean_inc(v_binderName_1329_);
                                v_binderType_1330_ = lean_ctor_get(v_e_1269_, 1);
                                lean_inc_ref(v_binderType_1330_);
                                v_body_1331_ = lean_ctor_get(v_e_1269_, 2);
                                lean_inc_ref(v_body_1331_);
                                v_binderInfo_1332_ = lean_ctor_get_uint8(
                                    v_e_1269_,
                                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                                );
                                lean_dec_ref_known(v_e_1269_, 3);
                                v___x_1333_ = lean_box((v___x_1295_) as usize);
                                v___x_1334_ = lean_box((v___x_1297_) as usize);
                                lean_inc(v_toBind_1284_);
                                v___f_1335_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed as *mut core::ffi::c_void, 8, 7);
                                lean_closure_set(v___f_1335_, 0, v___x_1296_);
                                lean_closure_set(v___f_1335_, 1, v___x_1333_);
                                lean_closure_set(v___f_1335_, 2, v___x_1334_);
                                lean_closure_set(v___f_1335_, 3, v_inst_1264_);
                                lean_closure_set(v___f_1335_, 4, v_body_1331_);
                                lean_closure_set(v___f_1335_, 5, v_g_1267_);
                                lean_closure_set(v___f_1335_, 6, v_toBind_1284_);
                                v___x_1336_ = 0;
                                v___x_1337_ = l_Lean_Meta_withLocalDecl___redArg(
                                    v_inst_1265_,
                                    v_inst_1263_,
                                    v_binderName_1329_,
                                    v_binderInfo_1332_,
                                    v_binderType_1330_,
                                    v___f_1335_,
                                    v___x_1336_,
                                );
                                return v___x_1337_;
                            }
                            8 => {
                                lean_inc(v_toPure_1286_);
                                lean_inc(v_toBind_1284_);
                                lean_dec_ref(v_inst_1266_);
                                lean_dec_ref(v_inst_1265_);
                                lean_dec(v_inst_1264_);
                                lean_dec_ref(v_inst_1263_);
                                v_declName_1338_ = lean_ctor_get(v_e_1269_, 0);
                                lean_inc(v_declName_1338_);
                                v_type_1339_ = lean_ctor_get(v_e_1269_, 1);
                                lean_inc_ref(v_type_1339_);
                                v_value_1340_ = lean_ctor_get(v_e_1269_, 2);
                                lean_inc_ref_n(v_value_1340_, 2);
                                v_body_1341_ = lean_ctor_get(v_e_1269_, 3);
                                lean_inc_ref(v_body_1341_);
                                v_nondep_1342_ = lean_ctor_get_uint8(
                                    v_e_1269_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                                );
                                v___x_1343_ = lean_box((v_nondep_1342_) as usize);
                                v___f_1344_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed as *mut core::ffi::c_void, 8, 7);
                                lean_closure_set(v___f_1344_, 0, v_declName_1338_);
                                lean_closure_set(v___f_1344_, 1, v_type_1339_);
                                lean_closure_set(v___f_1344_, 2, v_body_1341_);
                                lean_closure_set(v___f_1344_, 3, v___x_1343_);
                                lean_closure_set(v___f_1344_, 4, v_toPure_1286_);
                                lean_closure_set(v___f_1344_, 5, v_e_1269_);
                                lean_closure_set(v___f_1344_, 6, v_value_1340_);
                                v___x_1345_ = lean_apply_1(v_g_1267_, v_value_1340_);
                                v___x_1346_ = lean_apply_4(
                                    v_toBind_1284_,
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_1345_,
                                    v___f_1344_,
                                );
                                return v___x_1346_;
                            }
                            10 => {
                                v_expr_1347_ = lean_ctor_get(v_e_1269_, 1);
                                lean_inc_ref(v_expr_1347_);
                                v_n_1288_ = v___x_1296_;
                                v_a_1289_ = v_expr_1347_;
                                state = 2;
                                continue;
                            }
                            _ => {
                                lean_dec(v_g_1267_);
                                lean_dec_ref(v_inst_1265_);
                                lean_dec(v_inst_1264_);
                                v_c_1271_ = v___x_1296_;
                                v_e_1272_ = v_e_1269_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_n_1268_);
                    match lean_obj_tag(v_e_1269_) {
                        5 => {
                            lean_inc(v_toPure_1286_);
                            lean_inc(v_toBind_1284_);
                            lean_dec_ref(v_inst_1266_);
                            lean_dec_ref(v_inst_1265_);
                            lean_dec(v_inst_1264_);
                            lean_dec_ref(v_inst_1263_);
                            v_fn_1348_ = lean_ctor_get(v_e_1269_, 0);
                            lean_inc_ref_n(v_fn_1348_, 2);
                            v_arg_1349_ = lean_ctor_get(v_e_1269_, 1);
                            lean_inc_ref(v_arg_1349_);
                            v___f_1350_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed as *mut core::ffi::c_void, 5, 4);
                            lean_closure_set(v___f_1350_, 0, v_arg_1349_);
                            lean_closure_set(v___f_1350_, 1, v_toPure_1286_);
                            lean_closure_set(v___f_1350_, 2, v_e_1269_);
                            lean_closure_set(v___f_1350_, 3, v_fn_1348_);
                            v___x_1351_ = lean_apply_1(v_g_1267_, v_fn_1348_);
                            v___x_1352_ = lean_apply_4(
                                v_toBind_1284_,
                                lean_box(0),
                                lean_box(0),
                                v___x_1351_,
                                v___f_1350_,
                            );
                            return v___x_1352_;
                        }
                        6 => {
                            lean_inc(v_toPure_1286_);
                            lean_inc(v_toBind_1284_);
                            lean_dec_ref(v_inst_1266_);
                            lean_dec_ref(v_inst_1265_);
                            lean_dec(v_inst_1264_);
                            lean_dec_ref(v_inst_1263_);
                            v_binderName_1353_ = lean_ctor_get(v_e_1269_, 0);
                            lean_inc(v_binderName_1353_);
                            v_binderType_1354_ = lean_ctor_get(v_e_1269_, 1);
                            lean_inc_ref_n(v_binderType_1354_, 2);
                            v_body_1355_ = lean_ctor_get(v_e_1269_, 2);
                            lean_inc_ref(v_body_1355_);
                            v_binderInfo_1356_ = lean_ctor_get_uint8(
                                v_e_1269_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            v___x_1357_ = lean_box((v_binderInfo_1356_) as usize);
                            v___f_1358_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed as *mut core::ffi::c_void, 7, 6);
                            lean_closure_set(v___f_1358_, 0, v_binderName_1353_);
                            lean_closure_set(v___f_1358_, 1, v_body_1355_);
                            lean_closure_set(v___f_1358_, 2, v___x_1357_);
                            lean_closure_set(v___f_1358_, 3, v_toPure_1286_);
                            lean_closure_set(v___f_1358_, 4, v_e_1269_);
                            lean_closure_set(v___f_1358_, 5, v_binderType_1354_);
                            v___x_1359_ = lean_apply_1(v_g_1267_, v_binderType_1354_);
                            v___x_1360_ = lean_apply_4(
                                v_toBind_1284_,
                                lean_box(0),
                                lean_box(0),
                                v___x_1359_,
                                v___f_1358_,
                            );
                            return v___x_1360_;
                        }
                        7 => {
                            lean_inc(v_toPure_1286_);
                            lean_inc(v_toBind_1284_);
                            lean_dec_ref(v_inst_1266_);
                            lean_dec_ref(v_inst_1265_);
                            lean_dec(v_inst_1264_);
                            lean_dec_ref(v_inst_1263_);
                            v_binderName_1361_ = lean_ctor_get(v_e_1269_, 0);
                            lean_inc(v_binderName_1361_);
                            v_binderType_1362_ = lean_ctor_get(v_e_1269_, 1);
                            lean_inc_ref_n(v_binderType_1362_, 2);
                            v_body_1363_ = lean_ctor_get(v_e_1269_, 2);
                            lean_inc_ref(v_body_1363_);
                            v_binderInfo_1364_ = lean_ctor_get_uint8(
                                v_e_1269_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            v___x_1365_ = lean_box((v_binderInfo_1364_) as usize);
                            v___f_1366_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed as *mut core::ffi::c_void, 7, 6);
                            lean_closure_set(v___f_1366_, 0, v_binderName_1361_);
                            lean_closure_set(v___f_1366_, 1, v_body_1363_);
                            lean_closure_set(v___f_1366_, 2, v___x_1365_);
                            lean_closure_set(v___f_1366_, 3, v_toPure_1286_);
                            lean_closure_set(v___f_1366_, 4, v_e_1269_);
                            lean_closure_set(v___f_1366_, 5, v_binderType_1362_);
                            v___x_1367_ = lean_apply_1(v_g_1267_, v_binderType_1362_);
                            v___x_1368_ = lean_apply_4(
                                v_toBind_1284_,
                                lean_box(0),
                                lean_box(0),
                                v___x_1367_,
                                v___f_1366_,
                            );
                            return v___x_1368_;
                        }
                        8 => {
                            lean_inc(v_toPure_1286_);
                            lean_inc(v_toBind_1284_);
                            lean_dec_ref(v_inst_1266_);
                            lean_dec_ref(v_inst_1265_);
                            lean_dec(v_inst_1264_);
                            lean_dec_ref(v_inst_1263_);
                            v_declName_1369_ = lean_ctor_get(v_e_1269_, 0);
                            lean_inc(v_declName_1369_);
                            v_type_1370_ = lean_ctor_get(v_e_1269_, 1);
                            lean_inc_ref_n(v_type_1370_, 2);
                            v_value_1371_ = lean_ctor_get(v_e_1269_, 2);
                            lean_inc_ref(v_value_1371_);
                            v_body_1372_ = lean_ctor_get(v_e_1269_, 3);
                            lean_inc_ref(v_body_1372_);
                            v_nondep_1373_ = lean_ctor_get_uint8(
                                v_e_1269_,
                                (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                            );
                            v___x_1374_ = lean_box((v_nondep_1373_) as usize);
                            v___f_1375_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed as *mut core::ffi::c_void, 8, 7);
                            lean_closure_set(v___f_1375_, 0, v_declName_1369_);
                            lean_closure_set(v___f_1375_, 1, v_value_1371_);
                            lean_closure_set(v___f_1375_, 2, v_body_1372_);
                            lean_closure_set(v___f_1375_, 3, v___x_1374_);
                            lean_closure_set(v___f_1375_, 4, v_toPure_1286_);
                            lean_closure_set(v___f_1375_, 5, v_e_1269_);
                            lean_closure_set(v___f_1375_, 6, v_type_1370_);
                            v___x_1376_ = lean_apply_1(v_g_1267_, v_type_1370_);
                            v___x_1377_ = lean_apply_4(
                                v_toBind_1284_,
                                lean_box(0),
                                lean_box(0),
                                v___x_1376_,
                                v___f_1375_,
                            );
                            return v___x_1377_;
                        }
                        11 => {
                            lean_inc_ref(v_toFunctor_1285_);
                            lean_dec_ref(v_inst_1266_);
                            lean_dec_ref(v_inst_1265_);
                            lean_dec(v_inst_1264_);
                            lean_dec_ref(v_inst_1263_);
                            v_struct_1378_ = lean_ctor_get(v_e_1269_, 2);
                            lean_inc_ref(v_struct_1378_);
                            v_map_1379_ = lean_ctor_get(v_toFunctor_1285_, 0);
                            lean_inc(v_map_1379_);
                            lean_dec_ref(v_toFunctor_1285_);
                            v___x_1380_ = lean_alloc_closure(
                                l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            lean_closure_set(v___x_1380_, 0, v_e_1269_);
                            v___x_1381_ = lean_apply_1(v_g_1267_, v_struct_1378_);
                            v___x_1382_ = lean_apply_4(
                                v_map_1379_,
                                lean_box(0),
                                lean_box(0),
                                v___x_1380_,
                                v___x_1381_,
                            );
                            return v___x_1382_;
                        }
                        10 => {
                            v_expr_1383_ = lean_ctor_get(v_e_1269_, 1);
                            lean_inc_ref(v_expr_1383_);
                            v_n_1288_ = v___x_1294_;
                            v_a_1289_ = v_expr_1383_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            lean_dec(v_g_1267_);
                            lean_dec_ref(v_inst_1265_);
                            lean_dec(v_inst_1264_);
                            v_c_1271_ = v___x_1294_;
                            v_e_1272_ = v_e_1269_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1273_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1);
                v___x_1274_ = l_Nat_reprFast(v_c_1271_);
                v___x_1275_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1275_, 0, v___x_1274_);
                v___x_1276_ = l_Lean_MessageData_ofFormat(v___x_1275_);
                v___x_1277_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1277_, 0, v___x_1273_);
                lean_ctor_set(v___x_1277_, 1, v___x_1276_);
                v___x_1278_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
                v___x_1279_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1279_, 0, v___x_1277_);
                lean_ctor_set(v___x_1279_, 1, v___x_1278_);
                v___x_1280_ = l_Lean_MessageData_ofExpr(v_e_1272_);
                v___x_1281_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1281_, 0, v___x_1279_);
                lean_ctor_set(v___x_1281_, 1, v___x_1280_);
                v___x_1282_ = l_Lean_throwError___redArg(v_inst_1263_, v_inst_1266_, v___x_1281_);
                return v___x_1282_;
            }
            2 => {
                v_map_1290_ = lean_ctor_get(v_toFunctor_1285_, 0);
                lean_inc(v_map_1290_);
                v___x_1291_ = lean_alloc_closure(
                    l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_1291_, 0, v_e_1269_);
                v___x_1292_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(
                    v_inst_1263_,
                    v_inst_1264_,
                    v_inst_1265_,
                    v_inst_1266_,
                    v_g_1267_,
                    v_n_1288_,
                    v_a_1289_,
                );
                v___x_1293_ = lean_apply_4(
                    v_map_1290_,
                    lean_box(0),
                    lean_box(0),
                    v___x_1291_,
                    v___x_1292_,
                );
                return v___x_1293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord(
    mut v_M_1384_: *mut LeanObject,
    mut v_inst_1385_: *mut LeanObject,
    mut v_inst_1386_: *mut LeanObject,
    mut v_inst_1387_: *mut LeanObject,
    mut v_inst_1388_: *mut LeanObject,
    mut v_g_1389_: *mut LeanObject,
    mut v_n_1390_: *mut LeanObject,
    mut v_e_1391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    v___x_1392_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(
        v_inst_1385_,
        v_inst_1386_,
        v_inst_1387_,
        v_inst_1388_,
        v_g_1389_,
        v_n_1390_,
        v_e_1391_,
    );
    return v___x_1392_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(
    mut v_inst_1393_: *mut LeanObject,
    mut v_inst_1394_: *mut LeanObject,
    mut v_inst_1395_: *mut LeanObject,
    mut v_inst_1396_: *mut LeanObject,
    mut v_g_1397_: *mut LeanObject,
    mut v_x_1398_: *mut LeanObject,
    mut v_x_1399_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1398_) == 0 {
        let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1396_);
        lean_dec_ref(v_inst_1395_);
        lean_dec(v_inst_1394_);
        lean_dec_ref(v_inst_1393_);
        v___x_1400_ = lean_apply_1(v_g_1397_, v_x_1399_);
        return v___x_1400_;
    } else {
        let mut v_head_1401_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
        v_head_1401_ = lean_ctor_get(v_x_1398_, 0);
        lean_inc(v_head_1401_);
        v_tail_1402_ = lean_ctor_get(v_x_1398_, 1);
        lean_inc(v_tail_1402_);
        lean_dec_ref_known(v_x_1398_, 2);
        lean_inc_ref(v_inst_1396_);
        lean_inc_ref(v_inst_1395_);
        lean_inc(v_inst_1394_);
        lean_inc_ref(v_inst_1393_);
        v___x_1403_ = lean_alloc_closure(
            l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg as *mut core::ffi::c_void,
            7,
            6,
        );
        lean_closure_set(v___x_1403_, 0, v_inst_1393_);
        lean_closure_set(v___x_1403_, 1, v_inst_1394_);
        lean_closure_set(v___x_1403_, 2, v_inst_1395_);
        lean_closure_set(v___x_1403_, 3, v_inst_1396_);
        lean_closure_set(v___x_1403_, 4, v_g_1397_);
        lean_closure_set(v___x_1403_, 5, v_tail_1402_);
        v___x_1404_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(
            v_inst_1393_,
            v_inst_1394_,
            v_inst_1395_,
            v_inst_1396_,
            v___x_1403_,
            v_head_1401_,
            v_x_1399_,
        );
        return v___x_1404_;
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux(
    mut v_M_1405_: *mut LeanObject,
    mut v_inst_1406_: *mut LeanObject,
    mut v_inst_1407_: *mut LeanObject,
    mut v_inst_1408_: *mut LeanObject,
    mut v_inst_1409_: *mut LeanObject,
    mut v_g_1410_: *mut LeanObject,
    mut v_x_1411_: *mut LeanObject,
    mut v_x_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    v___x_1413_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(
        v_inst_1406_,
        v_inst_1407_,
        v_inst_1408_,
        v_inst_1409_,
        v_g_1410_,
        v_x_1411_,
        v_x_1412_,
    );
    return v___x_1413_;
}
pub unsafe fn l_Lean_Meta_replaceSubexpr___redArg(
    mut v_inst_1414_: *mut LeanObject,
    mut v_inst_1415_: *mut LeanObject,
    mut v_inst_1416_: *mut LeanObject,
    mut v_inst_1417_: *mut LeanObject,
    mut v_replace_1418_: *mut LeanObject,
    mut v_p_1419_: *mut LeanObject,
    mut v_root_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    v___x_1421_ = l_Lean_SubExpr_Pos_toArray(v_p_1419_);
    v___x_1422_ = lean_array_to_list(v___x_1421_);
    v___x_1423_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(
        v_inst_1414_,
        v_inst_1415_,
        v_inst_1416_,
        v_inst_1417_,
        v_replace_1418_,
        v___x_1422_,
        v_root_1420_,
    );
    return v___x_1423_;
}
pub unsafe fn l_Lean_Meta_replaceSubexpr___redArg___boxed(
    mut v_inst_1424_: *mut LeanObject,
    mut v_inst_1425_: *mut LeanObject,
    mut v_inst_1426_: *mut LeanObject,
    mut v_inst_1427_: *mut LeanObject,
    mut v_replace_1428_: *mut LeanObject,
    mut v_p_1429_: *mut LeanObject,
    mut v_root_1430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1431_: *mut LeanObject = core::ptr::null_mut();
    v_res_1431_ = l_Lean_Meta_replaceSubexpr___redArg(
        v_inst_1424_,
        v_inst_1425_,
        v_inst_1426_,
        v_inst_1427_,
        v_replace_1428_,
        v_p_1429_,
        v_root_1430_,
    );
    lean_dec(v_p_1429_);
    return v_res_1431_;
}
pub unsafe fn l_Lean_Meta_replaceSubexpr(
    mut v_M_1432_: *mut LeanObject,
    mut v_inst_1433_: *mut LeanObject,
    mut v_inst_1434_: *mut LeanObject,
    mut v_inst_1435_: *mut LeanObject,
    mut v_inst_1436_: *mut LeanObject,
    mut v_replace_1437_: *mut LeanObject,
    mut v_p_1438_: *mut LeanObject,
    mut v_root_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1440_ = l_Lean_Meta_replaceSubexpr___redArg(
        v_inst_1433_,
        v_inst_1434_,
        v_inst_1435_,
        v_inst_1436_,
        v_replace_1437_,
        v_p_1438_,
        v_root_1439_,
    );
    return v___x_1440_;
}
pub unsafe fn l_Lean_Meta_replaceSubexpr___boxed(
    mut v_M_1441_: *mut LeanObject,
    mut v_inst_1442_: *mut LeanObject,
    mut v_inst_1443_: *mut LeanObject,
    mut v_inst_1444_: *mut LeanObject,
    mut v_inst_1445_: *mut LeanObject,
    mut v_replace_1446_: *mut LeanObject,
    mut v_p_1447_: *mut LeanObject,
    mut v_root_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1449_: *mut LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_Lean_Meta_replaceSubexpr(
        v_M_1441_,
        v_inst_1442_,
        v_inst_1443_,
        v_inst_1444_,
        v_inst_1445_,
        v_replace_1446_,
        v_p_1447_,
        v_root_1448_,
    );
    lean_dec(v_p_1447_);
    return v_res_1449_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0(
    mut v_fvars_1450_: *mut LeanObject,
    mut v_k_1451_: *mut LeanObject,
    mut v_body_1452_: *mut LeanObject,
    mut v_x_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    v___x_1454_ = lean_array_push(v_fvars_1450_, v_x_1453_);
    v___x_1455_ = lean_apply_2(v_k_1451_, v___x_1454_, v_body_1452_);
    return v___x_1455_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1(
    mut v_fvars_1456_: *mut LeanObject,
    mut v_k_1457_: *mut LeanObject,
    mut v_b_1458_: *mut LeanObject,
    mut v_x_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    v___x_1460_ = lean_array_push(v_fvars_1456_, v_x_1459_);
    v___x_1461_ = lean_apply_2(v_k_1457_, v___x_1460_, v_b_1458_);
    return v___x_1461_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0;
    v___x_1464_ = l_Lean_stringToMessageData(v___x_1463_);
    return v___x_1464_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(
    mut v_inst_1465_: *mut LeanObject,
    mut v_inst_1466_: *mut LeanObject,
    mut v_inst_1467_: *mut LeanObject,
    mut v_k_1468_: *mut LeanObject,
    mut v_fvars_1469_: *mut LeanObject,
    mut v_n_1470_: *mut LeanObject,
    mut v_e_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1489_: u8 = 0;
    let mut v___f_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: u8 = 0;
    let mut v_expr_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: u8 = 0;
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1520_: u8 = 0;
    let mut v_binderName_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1524_: u8 = 0;
    let mut v_value_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1494_ = lean_unsigned_to_nat(3);
                v___x_1495_ = lean_nat_dec_eq(v_n_1470_, v___x_1494_);
                if v___x_1495_ == 0 {
                    v___x_1496_ = lean_unsigned_to_nat(0);
                    v___x_1497_ = lean_nat_dec_eq(v_n_1470_, v___x_1496_);
                    if v___x_1497_ == 0 {
                        v___x_1498_ = lean_unsigned_to_nat(1);
                        v___x_1499_ = lean_nat_dec_eq(v_n_1470_, v___x_1498_);
                        if v___x_1499_ == 0 {
                            v___x_1500_ = lean_unsigned_to_nat(2);
                            v___x_1501_ = lean_nat_dec_eq(v_n_1470_, v___x_1500_);
                            if v___x_1501_ == 0 {
                                if lean_obj_tag(v_e_1471_) == 10 {
                                    v_expr_1502_ = lean_ctor_get(v_e_1471_, 1);
                                    lean_inc_ref(v_expr_1502_);
                                    lean_dec_ref_known(v_e_1471_, 2);
                                    v_e_1471_ = v_expr_1502_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v_fvars_1469_);
                                    lean_dec(v_k_1468_);
                                    lean_dec_ref(v_inst_1466_);
                                    v_c_1473_ = v_n_1470_;
                                    v_e_1474_ = v_e_1471_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_n_1470_);
                                match lean_obj_tag(v_e_1471_) {
                                    8 => {
                                        lean_dec_ref(v_inst_1467_);
                                        v_declName_1504_ = lean_ctor_get(v_e_1471_, 0);
                                        lean_inc(v_declName_1504_);
                                        v_type_1505_ = lean_ctor_get(v_e_1471_, 1);
                                        lean_inc_ref(v_type_1505_);
                                        v_value_1506_ = lean_ctor_get(v_e_1471_, 2);
                                        lean_inc_ref(v_value_1506_);
                                        v_body_1507_ = lean_ctor_get(v_e_1471_, 3);
                                        lean_inc_ref(v_body_1507_);
                                        lean_dec_ref_known(v_e_1471_, 4);
                                        lean_inc_ref(v_fvars_1469_);
                                        v___f_1508_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
                                        lean_closure_set(v___f_1508_, 0, v_fvars_1469_);
                                        lean_closure_set(v___f_1508_, 1, v_k_1468_);
                                        lean_closure_set(v___f_1508_, 2, v_body_1507_);
                                        v___x_1509_ =
                                            lean_expr_instantiate_rev(v_type_1505_, v_fvars_1469_);
                                        lean_dec_ref(v_type_1505_);
                                        v___x_1510_ =
                                            lean_expr_instantiate_rev(v_value_1506_, v_fvars_1469_);
                                        lean_dec_ref(v_fvars_1469_);
                                        lean_dec_ref(v_value_1506_);
                                        v___x_1511_ = 0;
                                        v___x_1512_ = l_Lean_Meta_withLetDecl___redArg(
                                            v_inst_1466_,
                                            v_inst_1465_,
                                            v_declName_1504_,
                                            v___x_1509_,
                                            v___x_1510_,
                                            v___f_1508_,
                                            v___x_1499_,
                                            v___x_1511_,
                                        );
                                        return v___x_1512_;
                                    }
                                    10 => {
                                        v_expr_1513_ = lean_ctor_get(v_e_1471_, 1);
                                        lean_inc_ref(v_expr_1513_);
                                        lean_dec_ref_known(v_e_1471_, 2);
                                        v_n_1470_ = v___x_1500_;
                                        v_e_1471_ = v_expr_1513_;
                                        state = 0;
                                        continue;
                                    }
                                    _ => {
                                        lean_dec_ref(v_fvars_1469_);
                                        lean_dec(v_k_1468_);
                                        lean_dec_ref(v_inst_1466_);
                                        v_c_1473_ = v___x_1500_;
                                        v_e_1474_ = v_e_1471_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_n_1470_);
                            match lean_obj_tag(v_e_1471_) {
                                5 => {
                                    lean_dec_ref(v_inst_1467_);
                                    lean_dec_ref(v_inst_1466_);
                                    lean_dec_ref(v_inst_1465_);
                                    v_arg_1515_ = lean_ctor_get(v_e_1471_, 1);
                                    lean_inc_ref(v_arg_1515_);
                                    lean_dec_ref_known(v_e_1471_, 2);
                                    v___x_1516_ =
                                        lean_apply_2(v_k_1468_, v_fvars_1469_, v_arg_1515_);
                                    return v___x_1516_;
                                }
                                6 => {
                                    lean_dec_ref(v_inst_1467_);
                                    v_binderName_1517_ = lean_ctor_get(v_e_1471_, 0);
                                    lean_inc(v_binderName_1517_);
                                    v_binderType_1518_ = lean_ctor_get(v_e_1471_, 1);
                                    lean_inc_ref(v_binderType_1518_);
                                    v_body_1519_ = lean_ctor_get(v_e_1471_, 2);
                                    lean_inc_ref(v_body_1519_);
                                    v_binderInfo_1520_ = lean_ctor_get_uint8(
                                        v_e_1471_,
                                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                                    );
                                    lean_dec_ref_known(v_e_1471_, 3);
                                    v_n_1486_ = v_binderName_1517_;
                                    v_y_1487_ = v_binderType_1518_;
                                    v_b_1488_ = v_body_1519_;
                                    v_c_1489_ = v_binderInfo_1520_;
                                    state = 2;
                                    continue;
                                }
                                7 => {
                                    lean_dec_ref(v_inst_1467_);
                                    v_binderName_1521_ = lean_ctor_get(v_e_1471_, 0);
                                    lean_inc(v_binderName_1521_);
                                    v_binderType_1522_ = lean_ctor_get(v_e_1471_, 1);
                                    lean_inc_ref(v_binderType_1522_);
                                    v_body_1523_ = lean_ctor_get(v_e_1471_, 2);
                                    lean_inc_ref(v_body_1523_);
                                    v_binderInfo_1524_ = lean_ctor_get_uint8(
                                        v_e_1471_,
                                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                                    );
                                    lean_dec_ref_known(v_e_1471_, 3);
                                    v_n_1486_ = v_binderName_1521_;
                                    v_y_1487_ = v_binderType_1522_;
                                    v_b_1488_ = v_body_1523_;
                                    v_c_1489_ = v_binderInfo_1524_;
                                    state = 2;
                                    continue;
                                }
                                8 => {
                                    lean_dec_ref(v_inst_1467_);
                                    lean_dec_ref(v_inst_1466_);
                                    lean_dec_ref(v_inst_1465_);
                                    v_value_1525_ = lean_ctor_get(v_e_1471_, 2);
                                    lean_inc_ref(v_value_1525_);
                                    lean_dec_ref_known(v_e_1471_, 4);
                                    v___x_1526_ =
                                        lean_apply_2(v_k_1468_, v_fvars_1469_, v_value_1525_);
                                    return v___x_1526_;
                                }
                                10 => {
                                    v_expr_1527_ = lean_ctor_get(v_e_1471_, 1);
                                    lean_inc_ref(v_expr_1527_);
                                    lean_dec_ref_known(v_e_1471_, 2);
                                    v_n_1470_ = v___x_1498_;
                                    v_e_1471_ = v_expr_1527_;
                                    state = 0;
                                    continue;
                                }
                                _ => {
                                    lean_dec_ref(v_fvars_1469_);
                                    lean_dec(v_k_1468_);
                                    lean_dec_ref(v_inst_1466_);
                                    v_c_1473_ = v___x_1498_;
                                    v_e_1474_ = v_e_1471_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_n_1470_);
                        match lean_obj_tag(v_e_1471_) {
                            5 => {
                                lean_dec_ref(v_inst_1467_);
                                lean_dec_ref(v_inst_1466_);
                                lean_dec_ref(v_inst_1465_);
                                v_fn_1529_ = lean_ctor_get(v_e_1471_, 0);
                                lean_inc_ref(v_fn_1529_);
                                lean_dec_ref_known(v_e_1471_, 2);
                                v___x_1530_ = lean_apply_2(v_k_1468_, v_fvars_1469_, v_fn_1529_);
                                return v___x_1530_;
                            }
                            6 => {
                                lean_dec_ref(v_inst_1467_);
                                lean_dec_ref(v_inst_1466_);
                                lean_dec_ref(v_inst_1465_);
                                v_binderType_1531_ = lean_ctor_get(v_e_1471_, 1);
                                lean_inc_ref(v_binderType_1531_);
                                lean_dec_ref_known(v_e_1471_, 3);
                                v___x_1532_ =
                                    lean_apply_2(v_k_1468_, v_fvars_1469_, v_binderType_1531_);
                                return v___x_1532_;
                            }
                            7 => {
                                lean_dec_ref(v_inst_1467_);
                                lean_dec_ref(v_inst_1466_);
                                lean_dec_ref(v_inst_1465_);
                                v_binderType_1533_ = lean_ctor_get(v_e_1471_, 1);
                                lean_inc_ref(v_binderType_1533_);
                                lean_dec_ref_known(v_e_1471_, 3);
                                v___x_1534_ =
                                    lean_apply_2(v_k_1468_, v_fvars_1469_, v_binderType_1533_);
                                return v___x_1534_;
                            }
                            8 => {
                                lean_dec_ref(v_inst_1467_);
                                lean_dec_ref(v_inst_1466_);
                                lean_dec_ref(v_inst_1465_);
                                v_type_1535_ = lean_ctor_get(v_e_1471_, 1);
                                lean_inc_ref(v_type_1535_);
                                lean_dec_ref_known(v_e_1471_, 4);
                                v___x_1536_ = lean_apply_2(v_k_1468_, v_fvars_1469_, v_type_1535_);
                                return v___x_1536_;
                            }
                            11 => {
                                lean_dec_ref(v_inst_1467_);
                                lean_dec_ref(v_inst_1466_);
                                lean_dec_ref(v_inst_1465_);
                                v_struct_1537_ = lean_ctor_get(v_e_1471_, 2);
                                lean_inc_ref(v_struct_1537_);
                                lean_dec_ref_known(v_e_1471_, 3);
                                v___x_1538_ =
                                    lean_apply_2(v_k_1468_, v_fvars_1469_, v_struct_1537_);
                                return v___x_1538_;
                            }
                            10 => {
                                v_expr_1539_ = lean_ctor_get(v_e_1471_, 1);
                                lean_inc_ref(v_expr_1539_);
                                lean_dec_ref_known(v_e_1471_, 2);
                                v_n_1470_ = v___x_1496_;
                                v_e_1471_ = v_expr_1539_;
                                state = 0;
                                continue;
                            }
                            _ => {
                                lean_dec_ref(v_fvars_1469_);
                                lean_dec(v_k_1468_);
                                lean_dec_ref(v_inst_1466_);
                                v_c_1473_ = v___x_1496_;
                                v_e_1474_ = v_e_1471_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1471_);
                    lean_dec(v_n_1470_);
                    lean_dec_ref(v_fvars_1469_);
                    lean_dec(v_k_1468_);
                    lean_dec_ref(v_inst_1466_);
                    v___x_1541_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1);
                    v___x_1542_ =
                        l_Lean_throwError___redArg(v_inst_1465_, v_inst_1467_, v___x_1541_);
                    return v___x_1542_;
                }
            }
            1 => {
                v___x_1475_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1);
                v___x_1476_ = l_Nat_reprFast(v_c_1473_);
                v___x_1477_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1477_, 0, v___x_1476_);
                v___x_1478_ = l_Lean_MessageData_ofFormat(v___x_1477_);
                v___x_1479_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1479_, 0, v___x_1475_);
                lean_ctor_set(v___x_1479_, 1, v___x_1478_);
                v___x_1480_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
                v___x_1481_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1481_, 0, v___x_1479_);
                lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                v___x_1482_ = l_Lean_MessageData_ofExpr(v_e_1474_);
                v___x_1483_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1483_, 0, v___x_1481_);
                lean_ctor_set(v___x_1483_, 1, v___x_1482_);
                v___x_1484_ = l_Lean_throwError___redArg(v_inst_1465_, v_inst_1467_, v___x_1483_);
                return v___x_1484_;
            }
            2 => {
                lean_inc_ref(v_fvars_1469_);
                v___f_1490_ = lean_alloc_closure(
                    l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_1490_, 0, v_fvars_1469_);
                lean_closure_set(v___f_1490_, 1, v_k_1468_);
                lean_closure_set(v___f_1490_, 2, v_b_1488_);
                v___x_1491_ = lean_expr_instantiate_rev(v_y_1487_, v_fvars_1469_);
                lean_dec_ref(v_fvars_1469_);
                lean_dec_ref(v_y_1487_);
                v___x_1492_ = 0;
                v___x_1493_ = l_Lean_Meta_withLocalDecl___redArg(
                    v_inst_1466_,
                    v_inst_1465_,
                    v_n_1486_,
                    v_c_1489_,
                    v___x_1491_,
                    v___f_1490_,
                    v___x_1492_,
                );
                return v___x_1493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux(
    mut v_M_1543_: *mut LeanObject,
    mut v_inst_1544_: *mut LeanObject,
    mut v_inst_1545_: *mut LeanObject,
    mut v_inst_1546_: *mut LeanObject,
    mut v_00_u03b1_1547_: *mut LeanObject,
    mut v_k_1548_: *mut LeanObject,
    mut v_fvars_1549_: *mut LeanObject,
    mut v_n_1550_: *mut LeanObject,
    mut v_e_1551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    v___x_1552_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(
        v_inst_1544_,
        v_inst_1545_,
        v_inst_1546_,
        v_k_1548_,
        v_fvars_1549_,
        v_n_1550_,
        v_e_1551_,
    );
    return v___x_1552_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(
    mut v_fvars_1553_: *mut LeanObject,
    mut v_k_1554_: *mut LeanObject,
    mut v_otherFvars_1555_: *mut LeanObject,
    mut v___y_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    v___x_1557_ = l_Array_append___redArg(v_fvars_1553_, v_otherFvars_1555_);
    v___x_1558_ = lean_apply_2(v_k_1554_, v___x_1557_, v___y_1556_);
    return v___x_1558_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed(
    mut v_fvars_1559_: *mut LeanObject,
    mut v_k_1560_: *mut LeanObject,
    mut v_otherFvars_1561_: *mut LeanObject,
    mut v___y_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1563_: *mut LeanObject = core::ptr::null_mut();
    v_res_1563_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(
        v_fvars_1559_,
        v_k_1560_,
        v_otherFvars_1561_,
        v___y_1562_,
    );
    lean_dec_ref(v_otherFvars_1561_);
    return v_res_1563_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2(
    mut v_inst_1566_: *mut LeanObject,
    mut v_inst_1567_: *mut LeanObject,
    mut v_inst_1568_: *mut LeanObject,
    mut v_inst_1569_: *mut LeanObject,
    mut v___f_1570_: *mut LeanObject,
    mut v_tail_1571_: *mut LeanObject,
    mut v_y_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    v___x_1573_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0;
    v___x_1574_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(
        v_inst_1566_,
        v_inst_1567_,
        v_inst_1568_,
        v_inst_1569_,
        v___f_1570_,
        v___x_1573_,
        v_tail_1571_,
        v_y_1572_,
    );
    return v___x_1574_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(
    mut v_inst_1575_: *mut LeanObject,
    mut v_inst_1576_: *mut LeanObject,
    mut v_inst_1577_: *mut LeanObject,
    mut v_inst_1578_: *mut LeanObject,
    mut v_k_1579_: *mut LeanObject,
    mut v_fvars_1580_: *mut LeanObject,
    mut v_x_1581_: *mut LeanObject,
    mut v_x_1582_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1581_) == 0 {
        let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1578_);
        lean_dec_ref(v_inst_1577_);
        lean_dec(v_inst_1576_);
        lean_dec_ref(v_inst_1575_);
        v___x_1583_ = lean_expr_instantiate_rev(v_x_1582_, v_fvars_1580_);
        lean_dec_ref(v_x_1582_);
        v___x_1584_ = lean_apply_2(v_k_1579_, v_fvars_1580_, v___x_1583_);
        return v___x_1584_;
    } else {
        let mut v_toBind_1585_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1586_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: u8 = 0;
        v_toBind_1585_ = lean_ctor_get(v_inst_1575_, 1);
        v_head_1586_ = lean_ctor_get(v_x_1581_, 0);
        lean_inc(v_head_1586_);
        v_tail_1587_ = lean_ctor_get(v_x_1581_, 1);
        lean_inc(v_tail_1587_);
        lean_dec_ref_known(v_x_1581_, 2);
        v___x_1588_ = lean_unsigned_to_nat(3);
        v___x_1589_ = lean_nat_dec_eq(v_head_1586_, v___x_1588_);
        if v___x_1589_ == 0 {
            let mut v___f_1590_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_inst_1578_);
            lean_inc_ref(v_inst_1577_);
            lean_inc_ref(v_inst_1575_);
            v___f_1590_ = lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0
                    as *mut core::ffi::c_void,
                8,
                6,
            );
            lean_closure_set(v___f_1590_, 0, v_inst_1575_);
            lean_closure_set(v___f_1590_, 1, v_inst_1576_);
            lean_closure_set(v___f_1590_, 2, v_inst_1577_);
            lean_closure_set(v___f_1590_, 3, v_inst_1578_);
            lean_closure_set(v___f_1590_, 4, v_k_1579_);
            lean_closure_set(v___f_1590_, 5, v_tail_1587_);
            v___x_1591_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(
                v_inst_1575_,
                v_inst_1577_,
                v_inst_1578_,
                v___f_1590_,
                v_fvars_1580_,
                v_head_1586_,
                v_x_1582_,
            );
            return v___x_1591_;
        } else {
            let mut v___f_1592_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1593_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_toBind_1585_);
            lean_dec(v_head_1586_);
            lean_inc_ref(v_fvars_1580_);
            v___f_1592_ = lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                4,
                2,
            );
            lean_closure_set(v___f_1592_, 0, v_fvars_1580_);
            lean_closure_set(v___f_1592_, 1, v_k_1579_);
            lean_inc(v_inst_1576_);
            v___f_1593_ = lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2
                    as *mut core::ffi::c_void,
                7,
                6,
            );
            lean_closure_set(v___f_1593_, 0, v_inst_1575_);
            lean_closure_set(v___f_1593_, 1, v_inst_1576_);
            lean_closure_set(v___f_1593_, 2, v_inst_1577_);
            lean_closure_set(v___f_1593_, 3, v_inst_1578_);
            lean_closure_set(v___f_1593_, 4, v___f_1592_);
            lean_closure_set(v___f_1593_, 5, v_tail_1587_);
            v___x_1594_ = lean_expr_instantiate_rev(v_x_1582_, v_fvars_1580_);
            lean_dec_ref(v_fvars_1580_);
            lean_dec_ref(v_x_1582_);
            v___x_1595_ = lean_alloc_closure(
                l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
                6,
                1,
            );
            lean_closure_set(v___x_1595_, 0, v___x_1594_);
            v___x_1596_ = lean_apply_2(v_inst_1576_, lean_box(0), v___x_1595_);
            v___x_1597_ = lean_apply_4(
                v_toBind_1585_,
                lean_box(0),
                lean_box(0),
                v___x_1596_,
                v___f_1593_,
            );
            return v___x_1597_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0(
    mut v_inst_1598_: *mut LeanObject,
    mut v_inst_1599_: *mut LeanObject,
    mut v_inst_1600_: *mut LeanObject,
    mut v_inst_1601_: *mut LeanObject,
    mut v_k_1602_: *mut LeanObject,
    mut v_tail_1603_: *mut LeanObject,
    mut v_fvars_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    v___x_1606_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(
        v_inst_1598_,
        v_inst_1599_,
        v_inst_1600_,
        v_inst_1601_,
        v_k_1602_,
        v_fvars_1604_,
        v_tail_1603_,
        v___y_1605_,
    );
    return v___x_1606_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux(
    mut v_M_1607_: *mut LeanObject,
    mut v_inst_1608_: *mut LeanObject,
    mut v_inst_1609_: *mut LeanObject,
    mut v_inst_1610_: *mut LeanObject,
    mut v_inst_1611_: *mut LeanObject,
    mut v_00_u03b1_1612_: *mut LeanObject,
    mut v_k_1613_: *mut LeanObject,
    mut v_fvars_1614_: *mut LeanObject,
    mut v_x_1615_: *mut LeanObject,
    mut v_x_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    v___x_1617_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(
        v_inst_1608_,
        v_inst_1609_,
        v_inst_1610_,
        v_inst_1611_,
        v_k_1613_,
        v_fvars_1614_,
        v_x_1615_,
        v_x_1616_,
    );
    return v___x_1617_;
}
pub unsafe fn l_Lean_Meta_viewSubexpr___redArg(
    mut v_inst_1618_: *mut LeanObject,
    mut v_inst_1619_: *mut LeanObject,
    mut v_inst_1620_: *mut LeanObject,
    mut v_inst_1621_: *mut LeanObject,
    mut v_visit_1622_: *mut LeanObject,
    mut v_p_1623_: *mut LeanObject,
    mut v_root_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0;
    v___x_1626_ = l_Lean_SubExpr_Pos_toArray(v_p_1623_);
    v___x_1627_ = lean_array_to_list(v___x_1626_);
    v___x_1628_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(
        v_inst_1618_,
        v_inst_1619_,
        v_inst_1620_,
        v_inst_1621_,
        v_visit_1622_,
        v___x_1625_,
        v___x_1627_,
        v_root_1624_,
    );
    return v___x_1628_;
}
pub unsafe fn l_Lean_Meta_viewSubexpr___redArg___boxed(
    mut v_inst_1629_: *mut LeanObject,
    mut v_inst_1630_: *mut LeanObject,
    mut v_inst_1631_: *mut LeanObject,
    mut v_inst_1632_: *mut LeanObject,
    mut v_visit_1633_: *mut LeanObject,
    mut v_p_1634_: *mut LeanObject,
    mut v_root_1635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1636_: *mut LeanObject = core::ptr::null_mut();
    v_res_1636_ = l_Lean_Meta_viewSubexpr___redArg(
        v_inst_1629_,
        v_inst_1630_,
        v_inst_1631_,
        v_inst_1632_,
        v_visit_1633_,
        v_p_1634_,
        v_root_1635_,
    );
    lean_dec(v_p_1634_);
    return v_res_1636_;
}
pub unsafe fn l_Lean_Meta_viewSubexpr(
    mut v_M_1637_: *mut LeanObject,
    mut v_inst_1638_: *mut LeanObject,
    mut v_inst_1639_: *mut LeanObject,
    mut v_inst_1640_: *mut LeanObject,
    mut v_inst_1641_: *mut LeanObject,
    mut v_00_u03b1_1642_: *mut LeanObject,
    mut v_visit_1643_: *mut LeanObject,
    mut v_p_1644_: *mut LeanObject,
    mut v_root_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    v___x_1646_ = l_Lean_Meta_viewSubexpr___redArg(
        v_inst_1638_,
        v_inst_1639_,
        v_inst_1640_,
        v_inst_1641_,
        v_visit_1643_,
        v_p_1644_,
        v_root_1645_,
    );
    return v___x_1646_;
}
pub unsafe fn l_Lean_Meta_viewSubexpr___boxed(
    mut v_M_1647_: *mut LeanObject,
    mut v_inst_1648_: *mut LeanObject,
    mut v_inst_1649_: *mut LeanObject,
    mut v_inst_1650_: *mut LeanObject,
    mut v_inst_1651_: *mut LeanObject,
    mut v_00_u03b1_1652_: *mut LeanObject,
    mut v_visit_1653_: *mut LeanObject,
    mut v_p_1654_: *mut LeanObject,
    mut v_root_1655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1656_: *mut LeanObject = core::ptr::null_mut();
    v_res_1656_ = l_Lean_Meta_viewSubexpr(
        v_M_1647_,
        v_inst_1648_,
        v_inst_1649_,
        v_inst_1650_,
        v_inst_1651_,
        v_00_u03b1_1652_,
        v_visit_1653_,
        v_p_1654_,
        v_root_1655_,
    );
    lean_dec(v_p_1654_);
    return v_res_1656_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(
    mut v_fvars_1657_: *mut LeanObject,
    mut v_k_1658_: *mut LeanObject,
    mut v_otherFvars_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Array_append___redArg(v_fvars_1657_, v_otherFvars_1659_);
    v___x_1664_ = lean_apply_4(
        v_k_1658_,
        v___x_1663_,
        v___y_1660_,
        v___y_1661_,
        v___y_1662_,
    );
    return v___x_1664_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed(
    mut v_fvars_1665_: *mut LeanObject,
    mut v_k_1666_: *mut LeanObject,
    mut v_otherFvars_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1671_: *mut LeanObject = core::ptr::null_mut();
    v_res_1671_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(
        v_fvars_1665_,
        v_k_1666_,
        v_otherFvars_1667_,
        v___y_1668_,
        v___y_1669_,
        v___y_1670_,
    );
    lean_dec_ref(v_otherFvars_1667_);
    return v_res_1671_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2(
    mut v_inst_1672_: *mut LeanObject,
    mut v_inst_1673_: *mut LeanObject,
    mut v_inst_1674_: *mut LeanObject,
    mut v_inst_1675_: *mut LeanObject,
    mut v___f_1676_: *mut LeanObject,
    mut v_tail_1677_: *mut LeanObject,
    mut v_y_1678_: *mut LeanObject,
    mut v_acc_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    v___x_1680_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0;
    v___x_1681_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(
        v_inst_1672_,
        v_inst_1673_,
        v_inst_1674_,
        v_inst_1675_,
        v___f_1676_,
        v_acc_1679_,
        v_tail_1677_,
        v___x_1680_,
        v_y_1678_,
    );
    return v___x_1681_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3(
    mut v_inst_1682_: *mut LeanObject,
    mut v_inst_1683_: *mut LeanObject,
    mut v_inst_1684_: *mut LeanObject,
    mut v_inst_1685_: *mut LeanObject,
    mut v___f_1686_: *mut LeanObject,
    mut v_tail_1687_: *mut LeanObject,
    mut v_k_1688_: *mut LeanObject,
    mut v_fvars_1689_: *mut LeanObject,
    mut v_current_1690_: *mut LeanObject,
    mut v___x_1691_: *mut LeanObject,
    mut v_acc_1692_: *mut LeanObject,
    mut v_toBind_1693_: *mut LeanObject,
    mut v_y_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    v___f_1695_ = lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2
            as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1695_, 0, v_inst_1682_);
    lean_closure_set(v___f_1695_, 1, v_inst_1683_);
    lean_closure_set(v___f_1695_, 2, v_inst_1684_);
    lean_closure_set(v___f_1695_, 3, v_inst_1685_);
    lean_closure_set(v___f_1695_, 4, v___f_1686_);
    lean_closure_set(v___f_1695_, 5, v_tail_1687_);
    lean_closure_set(v___f_1695_, 6, v_y_1694_);
    v___x_1696_ = lean_apply_4(
        v_k_1688_,
        v_fvars_1689_,
        v_current_1690_,
        v___x_1691_,
        v_acc_1692_,
    );
    v___x_1697_ = lean_apply_4(
        v_toBind_1693_,
        lean_box(0),
        lean_box(0),
        v___x_1696_,
        v___f_1695_,
    );
    return v___x_1697_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(
    mut v_inst_1698_: *mut LeanObject,
    mut v_inst_1699_: *mut LeanObject,
    mut v_inst_1700_: *mut LeanObject,
    mut v_inst_1701_: *mut LeanObject,
    mut v_k_1702_: *mut LeanObject,
    mut v_acc_1703_: *mut LeanObject,
    mut v_address_1704_: *mut LeanObject,
    mut v_fvars_1705_: *mut LeanObject,
    mut v_current_1706_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_address_1704_) == 0 {
        let mut v_toApplicative_1707_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1707_ = lean_ctor_get(v_inst_1698_, 0);
        lean_inc_ref(v_toApplicative_1707_);
        lean_dec_ref(v_current_1706_);
        lean_dec_ref(v_fvars_1705_);
        lean_dec(v_k_1702_);
        lean_dec_ref(v_inst_1701_);
        lean_dec_ref(v_inst_1700_);
        lean_dec(v_inst_1699_);
        lean_dec_ref(v_inst_1698_);
        v_toPure_1708_ = lean_ctor_get(v_toApplicative_1707_, 1);
        lean_inc(v_toPure_1708_);
        lean_dec_ref(v_toApplicative_1707_);
        v___x_1709_ = lean_apply_2(v_toPure_1708_, lean_box(0), v_acc_1703_);
        return v___x_1709_;
    } else {
        let mut v_toBind_1710_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_1711_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1714_: u8 = 0;
        v_toBind_1710_ = lean_ctor_get(v_inst_1698_, 1);
        lean_inc(v_toBind_1710_);
        v_head_1711_ = lean_ctor_get(v_address_1704_, 0);
        lean_inc(v_head_1711_);
        v_tail_1712_ = lean_ctor_get(v_address_1704_, 1);
        lean_inc(v_tail_1712_);
        lean_dec_ref_known(v_address_1704_, 2);
        v___x_1713_ = lean_unsigned_to_nat(3);
        v___x_1714_ = lean_nat_dec_eq(v_head_1711_, v___x_1713_);
        if v___x_1714_ == 0 {
            let mut v___f_1715_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_current_1706_);
            lean_inc(v_head_1711_);
            lean_inc_ref(v_fvars_1705_);
            lean_inc(v_k_1702_);
            v___f_1715_ = lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_1715_, 0, v_inst_1698_);
            lean_closure_set(v___f_1715_, 1, v_inst_1699_);
            lean_closure_set(v___f_1715_, 2, v_inst_1700_);
            lean_closure_set(v___f_1715_, 3, v_inst_1701_);
            lean_closure_set(v___f_1715_, 4, v_k_1702_);
            lean_closure_set(v___f_1715_, 5, v_tail_1712_);
            lean_closure_set(v___f_1715_, 6, v_fvars_1705_);
            lean_closure_set(v___f_1715_, 7, v_head_1711_);
            lean_closure_set(v___f_1715_, 8, v_current_1706_);
            v___x_1716_ = lean_expr_instantiate_rev(v_current_1706_, v_fvars_1705_);
            lean_dec_ref(v_current_1706_);
            v___x_1717_ = lean_apply_4(
                v_k_1702_,
                v_fvars_1705_,
                v___x_1716_,
                v_head_1711_,
                v_acc_1703_,
            );
            v___x_1718_ = lean_apply_4(
                v_toBind_1710_,
                lean_box(0),
                lean_box(0),
                v___x_1717_,
                v___f_1715_,
            );
            return v___x_1718_;
        } else {
            let mut v___f_1719_: *mut LeanObject = core::ptr::null_mut();
            let mut v_current_1720_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1721_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_head_1711_);
            lean_inc(v_k_1702_);
            lean_inc_ref(v_fvars_1705_);
            v___f_1719_ = lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 2);
            lean_closure_set(v___f_1719_, 0, v_fvars_1705_);
            lean_closure_set(v___f_1719_, 1, v_k_1702_);
            v_current_1720_ = lean_expr_instantiate_rev(v_current_1706_, v_fvars_1705_);
            lean_dec_ref(v_current_1706_);
            lean_inc(v_toBind_1710_);
            lean_inc_ref(v_current_1720_);
            lean_inc(v_inst_1699_);
            v___f_1721_ = lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3
                    as *mut core::ffi::c_void,
                13,
                12,
            );
            lean_closure_set(v___f_1721_, 0, v_inst_1698_);
            lean_closure_set(v___f_1721_, 1, v_inst_1699_);
            lean_closure_set(v___f_1721_, 2, v_inst_1700_);
            lean_closure_set(v___f_1721_, 3, v_inst_1701_);
            lean_closure_set(v___f_1721_, 4, v___f_1719_);
            lean_closure_set(v___f_1721_, 5, v_tail_1712_);
            lean_closure_set(v___f_1721_, 6, v_k_1702_);
            lean_closure_set(v___f_1721_, 7, v_fvars_1705_);
            lean_closure_set(v___f_1721_, 8, v_current_1720_);
            lean_closure_set(v___f_1721_, 9, v___x_1713_);
            lean_closure_set(v___f_1721_, 10, v_acc_1703_);
            lean_closure_set(v___f_1721_, 11, v_toBind_1710_);
            v___x_1722_ = lean_alloc_closure(
                l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
                6,
                1,
            );
            lean_closure_set(v___x_1722_, 0, v_current_1720_);
            v___x_1723_ = lean_apply_2(v_inst_1699_, lean_box(0), v___x_1722_);
            v___x_1724_ = lean_apply_4(
                v_toBind_1710_,
                lean_box(0),
                lean_box(0),
                v___x_1723_,
                v___f_1721_,
            );
            return v___x_1724_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0(
    mut v_inst_1725_: *mut LeanObject,
    mut v_inst_1726_: *mut LeanObject,
    mut v_inst_1727_: *mut LeanObject,
    mut v_inst_1728_: *mut LeanObject,
    mut v_k_1729_: *mut LeanObject,
    mut v_tail_1730_: *mut LeanObject,
    mut v_fvars_1731_: *mut LeanObject,
    mut v_head_1732_: *mut LeanObject,
    mut v_current_1733_: *mut LeanObject,
    mut v_acc_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1728_);
    lean_inc_ref(v_inst_1727_);
    lean_inc_ref(v_inst_1725_);
    v___x_1735_ = lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg
            as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___x_1735_, 0, v_inst_1725_);
    lean_closure_set(v___x_1735_, 1, v_inst_1726_);
    lean_closure_set(v___x_1735_, 2, v_inst_1727_);
    lean_closure_set(v___x_1735_, 3, v_inst_1728_);
    lean_closure_set(v___x_1735_, 4, v_k_1729_);
    lean_closure_set(v___x_1735_, 5, v_acc_1734_);
    lean_closure_set(v___x_1735_, 6, v_tail_1730_);
    v___x_1736_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(
        v_inst_1725_,
        v_inst_1727_,
        v_inst_1728_,
        v___x_1735_,
        v_fvars_1731_,
        v_head_1732_,
        v_current_1733_,
    );
    return v___x_1736_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux(
    mut v_M_1737_: *mut LeanObject,
    mut v_inst_1738_: *mut LeanObject,
    mut v_inst_1739_: *mut LeanObject,
    mut v_inst_1740_: *mut LeanObject,
    mut v_inst_1741_: *mut LeanObject,
    mut v_00_u03b1_1742_: *mut LeanObject,
    mut v_k_1743_: *mut LeanObject,
    mut v_acc_1744_: *mut LeanObject,
    mut v_address_1745_: *mut LeanObject,
    mut v_fvars_1746_: *mut LeanObject,
    mut v_current_1747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(
        v_inst_1738_,
        v_inst_1739_,
        v_inst_1740_,
        v_inst_1741_,
        v_k_1743_,
        v_acc_1744_,
        v_address_1745_,
        v_fvars_1746_,
        v_current_1747_,
    );
    return v___x_1748_;
}
pub unsafe fn l_Lean_Meta_foldAncestors___redArg(
    mut v_inst_1749_: *mut LeanObject,
    mut v_inst_1750_: *mut LeanObject,
    mut v_inst_1751_: *mut LeanObject,
    mut v_inst_1752_: *mut LeanObject,
    mut v_k_1753_: *mut LeanObject,
    mut v_init_1754_: *mut LeanObject,
    mut v_p_1755_: *mut LeanObject,
    mut v_e_1756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = l_Lean_SubExpr_Pos_toArray(v_p_1755_);
    v___x_1758_ = lean_array_to_list(v___x_1757_);
    v___x_1759_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0;
    v___x_1760_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(
        v_inst_1749_,
        v_inst_1750_,
        v_inst_1751_,
        v_inst_1752_,
        v_k_1753_,
        v_init_1754_,
        v___x_1758_,
        v___x_1759_,
        v_e_1756_,
    );
    return v___x_1760_;
}
pub unsafe fn l_Lean_Meta_foldAncestors___redArg___boxed(
    mut v_inst_1761_: *mut LeanObject,
    mut v_inst_1762_: *mut LeanObject,
    mut v_inst_1763_: *mut LeanObject,
    mut v_inst_1764_: *mut LeanObject,
    mut v_k_1765_: *mut LeanObject,
    mut v_init_1766_: *mut LeanObject,
    mut v_p_1767_: *mut LeanObject,
    mut v_e_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1769_: *mut LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Lean_Meta_foldAncestors___redArg(
        v_inst_1761_,
        v_inst_1762_,
        v_inst_1763_,
        v_inst_1764_,
        v_k_1765_,
        v_init_1766_,
        v_p_1767_,
        v_e_1768_,
    );
    lean_dec(v_p_1767_);
    return v_res_1769_;
}
pub unsafe fn l_Lean_Meta_foldAncestors(
    mut v_M_1770_: *mut LeanObject,
    mut v_inst_1771_: *mut LeanObject,
    mut v_inst_1772_: *mut LeanObject,
    mut v_inst_1773_: *mut LeanObject,
    mut v_inst_1774_: *mut LeanObject,
    mut v_00_u03b1_1775_: *mut LeanObject,
    mut v_k_1776_: *mut LeanObject,
    mut v_init_1777_: *mut LeanObject,
    mut v_p_1778_: *mut LeanObject,
    mut v_e_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    v___x_1780_ = l_Lean_Meta_foldAncestors___redArg(
        v_inst_1771_,
        v_inst_1772_,
        v_inst_1773_,
        v_inst_1774_,
        v_k_1776_,
        v_init_1777_,
        v_p_1778_,
        v_e_1779_,
    );
    return v___x_1780_;
}
pub unsafe fn l_Lean_Meta_foldAncestors___boxed(
    mut v_M_1781_: *mut LeanObject,
    mut v_inst_1782_: *mut LeanObject,
    mut v_inst_1783_: *mut LeanObject,
    mut v_inst_1784_: *mut LeanObject,
    mut v_inst_1785_: *mut LeanObject,
    mut v_00_u03b1_1786_: *mut LeanObject,
    mut v_k_1787_: *mut LeanObject,
    mut v_init_1788_: *mut LeanObject,
    mut v_p_1789_: *mut LeanObject,
    mut v_e_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1791_: *mut LeanObject = core::ptr::null_mut();
    v_res_1791_ = l_Lean_Meta_foldAncestors(
        v_M_1781_,
        v_inst_1782_,
        v_inst_1783_,
        v_inst_1784_,
        v_inst_1785_,
        v_00_u03b1_1786_,
        v_k_1787_,
        v_init_1788_,
        v_p_1789_,
        v_e_1790_,
    );
    lean_dec(v_p_1789_);
    return v_res_1791_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    v___x_1793_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0;
    v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
    return v___x_1794_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2;
    v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
    return v___x_1797_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(
    mut v_inst_1798_: *mut LeanObject,
    mut v_inst_1799_: *mut LeanObject,
    mut v_e_1800_: *mut LeanObject,
    mut v_n_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v_expr_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1815_ = lean_ctor_get(v_inst_1798_, 0);
                v_toPure_1816_ = lean_ctor_get(v_toApplicative_1815_, 1);
                v___x_1817_ = lean_unsigned_to_nat(3);
                v___x_1818_ = lean_nat_dec_eq(v_n_1801_, v___x_1817_);
                if v___x_1818_ == 0 {
                    v___x_1819_ = lean_unsigned_to_nat(0);
                    v___x_1820_ = lean_nat_dec_eq(v_n_1801_, v___x_1819_);
                    if v___x_1820_ == 0 {
                        v___x_1821_ = lean_unsigned_to_nat(1);
                        v___x_1822_ = lean_nat_dec_eq(v_n_1801_, v___x_1821_);
                        if v___x_1822_ == 0 {
                            v___x_1823_ = lean_unsigned_to_nat(2);
                            v___x_1824_ = lean_nat_dec_eq(v_n_1801_, v___x_1823_);
                            if v___x_1824_ == 0 {
                                if lean_obj_tag(v_e_1800_) == 10 {
                                    v_expr_1825_ = lean_ctor_get(v_e_1800_, 1);
                                    lean_inc_ref(v_expr_1825_);
                                    lean_dec_ref_known(v_e_1800_, 2);
                                    v_e_1800_ = v_expr_1825_;
                                    state = 0;
                                    continue;
                                } else {
                                    v_e_1803_ = v_e_1800_;
                                    v_c_1804_ = v_n_1801_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_n_1801_);
                                match lean_obj_tag(v_e_1800_) {
                                    8 => {
                                        lean_inc(v_toPure_1816_);
                                        lean_dec_ref(v_inst_1799_);
                                        lean_dec_ref(v_inst_1798_);
                                        v_body_1827_ = lean_ctor_get(v_e_1800_, 3);
                                        lean_inc_ref(v_body_1827_);
                                        lean_dec_ref_known(v_e_1800_, 4);
                                        v___x_1828_ =
                                            lean_apply_2(v_toPure_1816_, lean_box(0), v_body_1827_);
                                        return v___x_1828_;
                                    }
                                    10 => {
                                        v_expr_1829_ = lean_ctor_get(v_e_1800_, 1);
                                        lean_inc_ref(v_expr_1829_);
                                        lean_dec_ref_known(v_e_1800_, 2);
                                        v_e_1800_ = v_expr_1829_;
                                        v_n_1801_ = v___x_1823_;
                                        state = 0;
                                        continue;
                                    }
                                    _ => {
                                        v_e_1803_ = v_e_1800_;
                                        v_c_1804_ = v___x_1823_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_n_1801_);
                            match lean_obj_tag(v_e_1800_) {
                                5 => {
                                    lean_inc(v_toPure_1816_);
                                    lean_dec_ref(v_inst_1799_);
                                    lean_dec_ref(v_inst_1798_);
                                    v_arg_1831_ = lean_ctor_get(v_e_1800_, 1);
                                    lean_inc_ref(v_arg_1831_);
                                    lean_dec_ref_known(v_e_1800_, 2);
                                    v___x_1832_ =
                                        lean_apply_2(v_toPure_1816_, lean_box(0), v_arg_1831_);
                                    return v___x_1832_;
                                }
                                6 => {
                                    lean_inc(v_toPure_1816_);
                                    lean_dec_ref(v_inst_1799_);
                                    lean_dec_ref(v_inst_1798_);
                                    v_body_1833_ = lean_ctor_get(v_e_1800_, 2);
                                    lean_inc_ref(v_body_1833_);
                                    lean_dec_ref_known(v_e_1800_, 3);
                                    v___x_1834_ =
                                        lean_apply_2(v_toPure_1816_, lean_box(0), v_body_1833_);
                                    return v___x_1834_;
                                }
                                7 => {
                                    lean_inc(v_toPure_1816_);
                                    lean_dec_ref(v_inst_1799_);
                                    lean_dec_ref(v_inst_1798_);
                                    v_body_1835_ = lean_ctor_get(v_e_1800_, 2);
                                    lean_inc_ref(v_body_1835_);
                                    lean_dec_ref_known(v_e_1800_, 3);
                                    v___x_1836_ =
                                        lean_apply_2(v_toPure_1816_, lean_box(0), v_body_1835_);
                                    return v___x_1836_;
                                }
                                8 => {
                                    lean_inc(v_toPure_1816_);
                                    lean_dec_ref(v_inst_1799_);
                                    lean_dec_ref(v_inst_1798_);
                                    v_value_1837_ = lean_ctor_get(v_e_1800_, 2);
                                    lean_inc_ref(v_value_1837_);
                                    lean_dec_ref_known(v_e_1800_, 4);
                                    v___x_1838_ =
                                        lean_apply_2(v_toPure_1816_, lean_box(0), v_value_1837_);
                                    return v___x_1838_;
                                }
                                10 => {
                                    v_expr_1839_ = lean_ctor_get(v_e_1800_, 1);
                                    lean_inc_ref(v_expr_1839_);
                                    lean_dec_ref_known(v_e_1800_, 2);
                                    v_e_1800_ = v_expr_1839_;
                                    v_n_1801_ = v___x_1821_;
                                    state = 0;
                                    continue;
                                }
                                _ => {
                                    v_e_1803_ = v_e_1800_;
                                    v_c_1804_ = v___x_1821_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_n_1801_);
                        match lean_obj_tag(v_e_1800_) {
                            5 => {
                                lean_inc(v_toPure_1816_);
                                lean_dec_ref(v_inst_1799_);
                                lean_dec_ref(v_inst_1798_);
                                v_fn_1841_ = lean_ctor_get(v_e_1800_, 0);
                                lean_inc_ref(v_fn_1841_);
                                lean_dec_ref_known(v_e_1800_, 2);
                                v___x_1842_ = lean_apply_2(v_toPure_1816_, lean_box(0), v_fn_1841_);
                                return v___x_1842_;
                            }
                            6 => {
                                lean_inc(v_toPure_1816_);
                                lean_dec_ref(v_inst_1799_);
                                lean_dec_ref(v_inst_1798_);
                                v_binderType_1843_ = lean_ctor_get(v_e_1800_, 1);
                                lean_inc_ref(v_binderType_1843_);
                                lean_dec_ref_known(v_e_1800_, 3);
                                v___x_1844_ =
                                    lean_apply_2(v_toPure_1816_, lean_box(0), v_binderType_1843_);
                                return v___x_1844_;
                            }
                            7 => {
                                lean_inc(v_toPure_1816_);
                                lean_dec_ref(v_inst_1799_);
                                lean_dec_ref(v_inst_1798_);
                                v_binderType_1845_ = lean_ctor_get(v_e_1800_, 1);
                                lean_inc_ref(v_binderType_1845_);
                                lean_dec_ref_known(v_e_1800_, 3);
                                v___x_1846_ =
                                    lean_apply_2(v_toPure_1816_, lean_box(0), v_binderType_1845_);
                                return v___x_1846_;
                            }
                            8 => {
                                lean_inc(v_toPure_1816_);
                                lean_dec_ref(v_inst_1799_);
                                lean_dec_ref(v_inst_1798_);
                                v_type_1847_ = lean_ctor_get(v_e_1800_, 1);
                                lean_inc_ref(v_type_1847_);
                                lean_dec_ref_known(v_e_1800_, 4);
                                v___x_1848_ =
                                    lean_apply_2(v_toPure_1816_, lean_box(0), v_type_1847_);
                                return v___x_1848_;
                            }
                            11 => {
                                lean_inc(v_toPure_1816_);
                                lean_dec_ref(v_inst_1799_);
                                lean_dec_ref(v_inst_1798_);
                                v_struct_1849_ = lean_ctor_get(v_e_1800_, 2);
                                lean_inc_ref(v_struct_1849_);
                                lean_dec_ref_known(v_e_1800_, 3);
                                v___x_1850_ =
                                    lean_apply_2(v_toPure_1816_, lean_box(0), v_struct_1849_);
                                return v___x_1850_;
                            }
                            10 => {
                                v_expr_1851_ = lean_ctor_get(v_e_1800_, 1);
                                lean_inc_ref(v_expr_1851_);
                                lean_dec_ref_known(v_e_1800_, 2);
                                v_e_1800_ = v_expr_1851_;
                                v_n_1801_ = v___x_1819_;
                                state = 0;
                                continue;
                            }
                            _ => {
                                v_e_1803_ = v_e_1800_;
                                v_c_1804_ = v___x_1819_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_n_1801_);
                    v___x_1853_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3);
                    v___x_1854_ = l_Lean_MessageData_ofExpr(v_e_1800_);
                    v___x_1855_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1855_, 0, v___x_1853_);
                    lean_ctor_set(v___x_1855_, 1, v___x_1854_);
                    v___x_1856_ =
                        l_Lean_throwError___redArg(v_inst_1798_, v_inst_1799_, v___x_1855_);
                    return v___x_1856_;
                }
            }
            1 => {
                v___x_1805_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1);
                v___x_1806_ = l_Nat_reprFast(v_c_1804_);
                v___x_1807_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1807_, 0, v___x_1806_);
                v___x_1808_ = l_Lean_MessageData_ofFormat(v___x_1807_);
                v___x_1809_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1809_, 0, v___x_1805_);
                lean_ctor_set(v___x_1809_, 1, v___x_1808_);
                v___x_1810_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
                v___x_1811_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1811_, 0, v___x_1809_);
                lean_ctor_set(v___x_1811_, 1, v___x_1810_);
                v___x_1812_ = l_Lean_MessageData_ofExpr(v_e_1803_);
                v___x_1813_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1813_, 0, v___x_1811_);
                lean_ctor_set(v___x_1813_, 1, v___x_1812_);
                v___x_1814_ = l_Lean_throwError___redArg(v_inst_1798_, v_inst_1799_, v___x_1813_);
                return v___x_1814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw(
    mut v_M_1857_: *mut LeanObject,
    mut v_inst_1858_: *mut LeanObject,
    mut v_inst_1859_: *mut LeanObject,
    mut v_e_1860_: *mut LeanObject,
    mut v_n_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    v___x_1862_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(
        v_inst_1858_,
        v_inst_1859_,
        v_e_1860_,
        v_n_1861_,
    );
    return v___x_1862_;
}
pub unsafe fn l_Lean_Core_viewSubexpr___redArg(
    mut v_inst_1863_: *mut LeanObject,
    mut v_inst_1864_: *mut LeanObject,
    mut v_p_1865_: *mut LeanObject,
    mut v_root_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1863_);
    v___x_1867_ = lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_1867_, 0, lean_box(0));
    lean_closure_set(v___x_1867_, 1, v_inst_1863_);
    lean_closure_set(v___x_1867_, 2, v_inst_1864_);
    v___x_1868_ =
        l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_1863_, v___x_1867_, v_root_1866_, v_p_1865_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_Core_viewSubexpr(
    mut v_M_1869_: *mut LeanObject,
    mut v_inst_1870_: *mut LeanObject,
    mut v_inst_1871_: *mut LeanObject,
    mut v_p_1872_: *mut LeanObject,
    mut v_root_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1874_ =
        l_Lean_Core_viewSubexpr___redArg(v_inst_1870_, v_inst_1871_, v_p_1872_, v_root_1873_);
    return v___x_1874_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(
    mut v_x_1875_: *mut LeanObject,
    mut v_x_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1882_ = lean_unsigned_to_nat(1);
                v___x_1883_ = lean_nat_dec_eq(v_x_1875_, v___x_1882_);
                if v___x_1883_ == 0 {
                    v___x_1884_ = lean_unsigned_to_nat(2);
                    v___x_1885_ = lean_nat_dec_eq(v_x_1875_, v___x_1884_);
                    if v___x_1885_ == 0 {
                        lean_dec_ref(v_x_1876_);
                        v___x_1886_ = lean_box(0);
                        return v___x_1886_;
                    } else {
                        if lean_obj_tag(v_x_1876_) == 8 {
                            v_declName_1887_ = lean_ctor_get(v_x_1876_, 0);
                            lean_inc(v_declName_1887_);
                            v_type_1888_ = lean_ctor_get(v_x_1876_, 1);
                            lean_inc_ref(v_type_1888_);
                            lean_dec_ref_known(v_x_1876_, 4);
                            v___x_1889_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1889_, 0, v_declName_1887_);
                            lean_ctor_set(v___x_1889_, 1, v_type_1888_);
                            v___x_1890_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1890_, 0, v___x_1889_);
                            return v___x_1890_;
                        } else {
                            lean_dec_ref(v_x_1876_);
                            v___x_1891_ = lean_box(0);
                            return v___x_1891_;
                        }
                    }
                } else {
                    match lean_obj_tag(v_x_1876_) {
                        6 => {
                            v_binderName_1892_ = lean_ctor_get(v_x_1876_, 0);
                            lean_inc(v_binderName_1892_);
                            v_binderType_1893_ = lean_ctor_get(v_x_1876_, 1);
                            lean_inc_ref(v_binderType_1893_);
                            lean_dec_ref_known(v_x_1876_, 3);
                            v_n_1878_ = v_binderName_1892_;
                            v_y_1879_ = v_binderType_1893_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_binderName_1894_ = lean_ctor_get(v_x_1876_, 0);
                            lean_inc(v_binderName_1894_);
                            v_binderType_1895_ = lean_ctor_get(v_x_1876_, 1);
                            lean_inc_ref(v_binderType_1895_);
                            lean_dec_ref_known(v_x_1876_, 3);
                            v_n_1878_ = v_binderName_1894_;
                            v_y_1879_ = v_binderType_1895_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_x_1876_);
                            v___x_1896_ = lean_box(0);
                            return v___x_1896_;
                        }
                    }
                }
            }
            1 => {
                v___x_1880_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1880_, 0, v_n_1878_);
                lean_ctor_set(v___x_1880_, 1, v_y_1879_);
                v___x_1881_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1881_, 0, v___x_1880_);
                return v___x_1881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___boxed(
    mut v_x_1897_: *mut LeanObject,
    mut v_x_1898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1899_: *mut LeanObject = core::ptr::null_mut();
    v_res_1899_ =
        l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(v_x_1897_, v_x_1898_);
    lean_dec(v_x_1897_);
    return v_res_1899_;
}
pub unsafe fn l_Lean_Core_viewBinders___redArg___lam__0(
    mut v_toPure_1900_: *mut LeanObject,
    mut v_c_1901_: *mut LeanObject,
    mut v_snd_1902_: *mut LeanObject,
    mut v_fst_1903_: *mut LeanObject,
    mut v_e_u2082_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1909_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(
                    v_c_1901_,
                    v_snd_1902_,
                );
                if lean_obj_tag(v___x_1909_) == 0 {
                    v___y_1906_ = v_fst_1903_;
                    state = 1;
                    continue;
                } else {
                    v_val_1910_ = lean_ctor_get(v___x_1909_, 0);
                    lean_inc(v_val_1910_);
                    lean_dec_ref_known(v___x_1909_, 1);
                    v___x_1911_ = lean_array_push(v_fst_1903_, v_val_1910_);
                    v___y_1906_ = v___x_1911_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1907_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1907_, 0, v___y_1906_);
                lean_ctor_set(v___x_1907_, 1, v_e_u2082_1904_);
                v___x_1908_ = lean_apply_2(v_toPure_1900_, lean_box(0), v___x_1907_);
                return v___x_1908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_viewBinders___redArg___lam__0___boxed(
    mut v_toPure_1912_: *mut LeanObject,
    mut v_c_1913_: *mut LeanObject,
    mut v_snd_1914_: *mut LeanObject,
    mut v_fst_1915_: *mut LeanObject,
    mut v_e_u2082_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1917_: *mut LeanObject = core::ptr::null_mut();
    v_res_1917_ = l_Lean_Core_viewBinders___redArg___lam__0(
        v_toPure_1912_,
        v_c_1913_,
        v_snd_1914_,
        v_fst_1915_,
        v_e_u2082_1916_,
    );
    lean_dec(v_c_1913_);
    return v_res_1917_;
}
pub unsafe fn l_Lean_Core_viewBinders___redArg___lam__1(
    mut v_toPure_1918_: *mut LeanObject,
    mut v_inst_1919_: *mut LeanObject,
    mut v_inst_1920_: *mut LeanObject,
    mut v_toBind_1921_: *mut LeanObject,
    mut v_x_1922_: *mut LeanObject,
    mut v_c_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1924_ = lean_ctor_get(v_x_1922_, 0);
    lean_inc(v_fst_1924_);
    v_snd_1925_ = lean_ctor_get(v_x_1922_, 1);
    lean_inc_n(v_snd_1925_, 2);
    lean_dec_ref(v_x_1922_);
    lean_inc(v_c_1923_);
    v___f_1926_ = lean_alloc_closure(
        l_Lean_Core_viewBinders___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1926_, 0, v_toPure_1918_);
    lean_closure_set(v___f_1926_, 1, v_c_1923_);
    lean_closure_set(v___f_1926_, 2, v_snd_1925_);
    lean_closure_set(v___f_1926_, 3, v_fst_1924_);
    v___x_1927_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(
        v_inst_1919_,
        v_inst_1920_,
        v_snd_1925_,
        v_c_1923_,
    );
    v___x_1928_ = lean_apply_4(
        v_toBind_1921_,
        lean_box(0),
        lean_box(0),
        v___x_1927_,
        v___f_1926_,
    );
    return v___x_1928_;
}
pub unsafe fn l_Lean_Core_viewBinders___redArg___lam__2(
    mut v_toPure_1929_: *mut LeanObject,
    mut v_____x_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1931_ = lean_ctor_get(v_____x_1930_, 0);
    lean_inc(v_fst_1931_);
    lean_dec_ref(v_____x_1930_);
    v___x_1932_ = lean_apply_2(v_toPure_1929_, lean_box(0), v_fst_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Lean_Core_viewBinders___redArg(
    mut v_inst_1935_: *mut LeanObject,
    mut v_inst_1936_: *mut LeanObject,
    mut v_p_1937_: *mut LeanObject,
    mut v_root_1938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1939_ = lean_ctor_get(v_inst_1935_, 0);
    v_toBind_1940_ = lean_ctor_get(v_inst_1935_, 1);
    lean_inc_n(v_toBind_1940_, 2);
    v_toPure_1941_ = lean_ctor_get(v_toApplicative_1939_, 1);
    lean_inc_ref(v_inst_1935_);
    lean_inc_n(v_toPure_1941_, 2);
    v___f_1942_ = lean_alloc_closure(
        l_Lean_Core_viewBinders___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_1942_, 0, v_toPure_1941_);
    lean_closure_set(v___f_1942_, 1, v_inst_1935_);
    lean_closure_set(v___f_1942_, 2, v_inst_1936_);
    lean_closure_set(v___f_1942_, 3, v_toBind_1940_);
    v___f_1943_ = lean_alloc_closure(
        l_Lean_Core_viewBinders___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1943_, 0, v_toPure_1941_);
    v___x_1944_ = l_Lean_Core_viewBinders___redArg___closed__0;
    v___x_1945_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1945_, 0, v___x_1944_);
    lean_ctor_set(v___x_1945_, 1, v_root_1938_);
    v___x_1946_ =
        l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_1935_, v___f_1942_, v___x_1945_, v_p_1937_);
    v___x_1947_ = lean_apply_4(
        v_toBind_1940_,
        lean_box(0),
        lean_box(0),
        v___x_1946_,
        v___f_1943_,
    );
    return v___x_1947_;
}
pub unsafe fn l_Lean_Core_viewBinders(
    mut v_M_1948_: *mut LeanObject,
    mut v_inst_1949_: *mut LeanObject,
    mut v_inst_1950_: *mut LeanObject,
    mut v_p_1951_: *mut LeanObject,
    mut v_root_1952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    v___x_1953_ =
        l_Lean_Core_viewBinders___redArg(v_inst_1949_, v_inst_1950_, v_p_1951_, v_root_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_Core_numBinders___redArg(
    mut v_inst_1955_: *mut LeanObject,
    mut v_inst_1956_: *mut LeanObject,
    mut v_p_1957_: *mut LeanObject,
    mut v_e_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1959_ = lean_ctor_get(v_inst_1955_, 0);
    v_toFunctor_1960_ = lean_ctor_get(v_toApplicative_1959_, 0);
    v_map_1961_ = lean_ctor_get(v_toFunctor_1960_, 0);
    lean_inc(v_map_1961_);
    v___x_1962_ = l_Lean_Core_numBinders___redArg___closed__0;
    v___x_1963_ =
        l_Lean_Core_viewBinders___redArg(v_inst_1955_, v_inst_1956_, v_p_1957_, v_e_1958_);
    v___x_1964_ = lean_apply_4(
        v_map_1961_,
        lean_box(0),
        lean_box(0),
        v___x_1962_,
        v___x_1963_,
    );
    return v___x_1964_;
}
pub unsafe fn l_Lean_Core_numBinders(
    mut v_M_1965_: *mut LeanObject,
    mut v_inst_1966_: *mut LeanObject,
    mut v_inst_1967_: *mut LeanObject,
    mut v_p_1968_: *mut LeanObject,
    mut v_e_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_Lean_Core_numBinders___redArg(v_inst_1966_, v_inst_1967_, v_p_1968_, v_e_1969_);
    return v___x_1970_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ExprLens(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ExprLens(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ExprLens(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ExprLens(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ExprLens(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_ExprLens(builtin);
}
