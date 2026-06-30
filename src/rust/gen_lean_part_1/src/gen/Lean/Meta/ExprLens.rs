// Lean compiler output
// Module: Lean.Meta.ExprLens
// Imports: Lean.SubExpr
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_expr_instantiate_rev, lean_expr_instantiate1,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_ptr_addr, lean_usize_dec_eq,
};
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
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Core_viewBinders___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Core_viewBinders___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Core_viewBinders___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Core_numBinders___redArg___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_size___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Core_numBinders___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Core_numBinders___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(
    mut v_body_986_: *mut leanh::LeanObject,
    mut v_g_987_: *mut leanh::LeanObject,
    mut v_x_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = lean_expr_instantiate1(v_body_986_, v_x_988_);
    v___x_990_ = leanh::lean_apply_1(v_g_987_, v___x_989_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0___boxed(
    mut v_body_991_: *mut leanh::LeanObject,
    mut v_g_992_: *mut leanh::LeanObject,
    mut v_x_993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(
        v_body_991_,
        v_g_992_,
        v_x_993_,
    );
    leanh::lean_dec_ref(v_x_993_);
    leanh::lean_dec_ref(v_body_991_);
    return v_res_994_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(
    mut v_fn_995_: *mut leanh::LeanObject,
    mut v_toPure_996_: *mut leanh::LeanObject,
    mut v_e_997_: *mut leanh::LeanObject,
    mut v_arg_998_: *mut leanh::LeanObject,
    mut v_____do__lift_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1001_: u8 = 0;
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec_ref(v_e_997_);
                    v___x_1002_ = l_Lean_Expr_app___override(v_fn_995_, v_____do__lift_999_);
                    v___x_1003_ = leanh::lean_apply_2(
                        v_toPure_996_,
                        leanh::lean_box(0),
                        v___x_1002_,
                    );
                    return v___x_1003_;
                } else {
                    leanh::lean_dec_ref(v_____do__lift_999_);
                    leanh::lean_dec_ref(v_fn_995_);
                    v___x_1004_ = leanh::lean_apply_2(
                        v_toPure_996_,
                        leanh::lean_box(0),
                        v_e_997_,
                    );
                    return v___x_1004_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed(
    mut v_fn_1010_: *mut leanh::LeanObject,
    mut v_toPure_1011_: *mut leanh::LeanObject,
    mut v_e_1012_: *mut leanh::LeanObject,
    mut v_arg_1013_: *mut leanh::LeanObject,
    mut v_____do__lift_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1015_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(
        v_fn_1010_,
        v_toPure_1011_,
        v_e_1012_,
        v_arg_1013_,
        v_____do__lift_1014_,
    );
    leanh::lean_dec_ref(v_arg_1013_);
    return v_res_1015_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(
    mut v___x_1016_: *mut leanh::LeanObject,
    mut v___x_1017_: u8,
    mut v___x_1018_: u8,
    mut v_inst_1019_: *mut leanh::LeanObject,
    mut v_____do__lift_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1021_: u8 = 0;
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = 1;
    v___x_1022_ = leanh::lean_box((v___x_1017_) as usize);
    v___x_1023_ = leanh::lean_box((v___x_1018_) as usize);
    v___x_1024_ = leanh::lean_box((v___x_1017_) as usize);
    v___x_1025_ = leanh::lean_box((v___x_1018_) as usize);
    v___x_1026_ = leanh::lean_box((v___x_1021_) as usize);
    v___x_1027_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_1027_, 0, v___x_1016_);
    leanh::lean_closure_set(v___x_1027_, 1, v_____do__lift_1020_);
    leanh::lean_closure_set(v___x_1027_, 2, v___x_1022_);
    leanh::lean_closure_set(v___x_1027_, 3, v___x_1023_);
    leanh::lean_closure_set(v___x_1027_, 4, v___x_1024_);
    leanh::lean_closure_set(v___x_1027_, 5, v___x_1025_);
    leanh::lean_closure_set(v___x_1027_, 6, v___x_1026_);
    v___x_1028_ = leanh::lean_apply_2(v_inst_1019_, leanh::lean_box(0), v___x_1027_);
    return v___x_1028_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed(
    mut v___x_1029_: *mut leanh::LeanObject,
    mut v___x_1030_: *mut leanh::LeanObject,
    mut v___x_1031_: *mut leanh::LeanObject,
    mut v_inst_1032_: *mut leanh::LeanObject,
    mut v_____do__lift_1033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1064__boxed_1034_: u8 = 0;
    let mut v___x_1065__boxed_1035_: u8 = 0;
    let mut v_res_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064__boxed_1034_ = (leanh::lean_unbox(v___x_1030_) as u8);
    v___x_1065__boxed_1035_ = (leanh::lean_unbox(v___x_1031_) as u8);
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
    mut v___x_1037_: *mut leanh::LeanObject,
    mut v___x_1038_: u8,
    mut v___x_1039_: u8,
    mut v_inst_1040_: *mut leanh::LeanObject,
    mut v_body_1041_: *mut leanh::LeanObject,
    mut v_g_1042_: *mut leanh::LeanObject,
    mut v_toBind_1043_: *mut leanh::LeanObject,
    mut v_x_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = lean_mk_empty_array_with_capacity(v___x_1037_);
    v___x_1046_ = lean_array_push(v___x_1045_, v_x_1044_);
    v___x_1047_ = leanh::lean_box((v___x_1038_) as usize);
    v___x_1048_ = leanh::lean_box((v___x_1039_) as usize);
    leanh::lean_inc_ref(v___x_1046_);
    v___f_1049_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1049_, 0, v___x_1046_);
    leanh::lean_closure_set(v___f_1049_, 1, v___x_1047_);
    leanh::lean_closure_set(v___f_1049_, 2, v___x_1048_);
    leanh::lean_closure_set(v___f_1049_, 3, v_inst_1040_);
    v___x_1050_ = lean_expr_instantiate_rev(v_body_1041_, v___x_1046_);
    leanh::lean_dec_ref(v___x_1046_);
    v___x_1051_ = leanh::lean_apply_1(v_g_1042_, v___x_1050_);
    v___x_1052_ = leanh::lean_apply_4(
        v_toBind_1043_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1051_,
        v___f_1049_,
    );
    return v___x_1052_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed(
    mut v___x_1053_: *mut leanh::LeanObject,
    mut v___x_1054_: *mut leanh::LeanObject,
    mut v___x_1055_: *mut leanh::LeanObject,
    mut v_inst_1056_: *mut leanh::LeanObject,
    mut v_body_1057_: *mut leanh::LeanObject,
    mut v_g_1058_: *mut leanh::LeanObject,
    mut v_toBind_1059_: *mut leanh::LeanObject,
    mut v_x_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1095__boxed_1061_: u8 = 0;
    let mut v___x_1096__boxed_1062_: u8 = 0;
    let mut v_res_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1095__boxed_1061_ = (leanh::lean_unbox(v___x_1054_) as u8);
    v___x_1096__boxed_1062_ = (leanh::lean_unbox(v___x_1055_) as u8);
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
    leanh::lean_dec_ref(v_body_1057_);
    leanh::lean_dec(v___x_1053_);
    return v_res_1063_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(
    mut v___x_1064_: *mut leanh::LeanObject,
    mut v___x_1065_: u8,
    mut v___x_1066_: u8,
    mut v_inst_1067_: *mut leanh::LeanObject,
    mut v_____do__lift_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ = 1;
    v___x_1070_ = leanh::lean_box((v___x_1065_) as usize);
    v___x_1071_ = leanh::lean_box((v___x_1066_) as usize);
    v___x_1072_ = leanh::lean_box((v___x_1066_) as usize);
    v___x_1073_ = leanh::lean_box((v___x_1069_) as usize);
    v___x_1074_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkForallFVars___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___x_1074_, 0, v___x_1064_);
    leanh::lean_closure_set(v___x_1074_, 1, v_____do__lift_1068_);
    leanh::lean_closure_set(v___x_1074_, 2, v___x_1070_);
    leanh::lean_closure_set(v___x_1074_, 3, v___x_1071_);
    leanh::lean_closure_set(v___x_1074_, 4, v___x_1072_);
    leanh::lean_closure_set(v___x_1074_, 5, v___x_1073_);
    v___x_1075_ = leanh::lean_apply_2(v_inst_1067_, leanh::lean_box(0), v___x_1074_);
    return v___x_1075_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed(
    mut v___x_1076_: *mut leanh::LeanObject,
    mut v___x_1077_: *mut leanh::LeanObject,
    mut v___x_1078_: *mut leanh::LeanObject,
    mut v_inst_1079_: *mut leanh::LeanObject,
    mut v_____do__lift_1080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1126__boxed_1081_: u8 = 0;
    let mut v___x_1127__boxed_1082_: u8 = 0;
    let mut v_res_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1126__boxed_1081_ = (leanh::lean_unbox(v___x_1077_) as u8);
    v___x_1127__boxed_1082_ = (leanh::lean_unbox(v___x_1078_) as u8);
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
    mut v___x_1084_: *mut leanh::LeanObject,
    mut v___x_1085_: u8,
    mut v___x_1086_: u8,
    mut v_inst_1087_: *mut leanh::LeanObject,
    mut v_body_1088_: *mut leanh::LeanObject,
    mut v_g_1089_: *mut leanh::LeanObject,
    mut v_toBind_1090_: *mut leanh::LeanObject,
    mut v_x_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = lean_mk_empty_array_with_capacity(v___x_1084_);
    v___x_1093_ = lean_array_push(v___x_1092_, v_x_1091_);
    v___x_1094_ = leanh::lean_box((v___x_1085_) as usize);
    v___x_1095_ = leanh::lean_box((v___x_1086_) as usize);
    leanh::lean_inc_ref(v___x_1093_);
    v___f_1096_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1096_, 0, v___x_1093_);
    leanh::lean_closure_set(v___f_1096_, 1, v___x_1094_);
    leanh::lean_closure_set(v___f_1096_, 2, v___x_1095_);
    leanh::lean_closure_set(v___f_1096_, 3, v_inst_1087_);
    v___x_1097_ = lean_expr_instantiate_rev(v_body_1088_, v___x_1093_);
    leanh::lean_dec_ref(v___x_1093_);
    v___x_1098_ = leanh::lean_apply_1(v_g_1089_, v___x_1097_);
    v___x_1099_ = leanh::lean_apply_4(
        v_toBind_1090_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1098_,
        v___f_1096_,
    );
    return v___x_1099_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed(
    mut v___x_1100_: *mut leanh::LeanObject,
    mut v___x_1101_: *mut leanh::LeanObject,
    mut v___x_1102_: *mut leanh::LeanObject,
    mut v_inst_1103_: *mut leanh::LeanObject,
    mut v_body_1104_: *mut leanh::LeanObject,
    mut v_g_1105_: *mut leanh::LeanObject,
    mut v_toBind_1106_: *mut leanh::LeanObject,
    mut v_x_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1155__boxed_1108_: u8 = 0;
    let mut v___x_1156__boxed_1109_: u8 = 0;
    let mut v_res_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1155__boxed_1108_ = (leanh::lean_unbox(v___x_1101_) as u8);
    v___x_1156__boxed_1109_ = (leanh::lean_unbox(v___x_1102_) as u8);
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
    leanh::lean_dec_ref(v_body_1104_);
    leanh::lean_dec(v___x_1100_);
    return v_res_1110_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(
    mut v_declName_1111_: *mut leanh::LeanObject,
    mut v_type_1112_: *mut leanh::LeanObject,
    mut v_body_1113_: *mut leanh::LeanObject,
    mut v_nondep_1114_: u8,
    mut v_toPure_1115_: *mut leanh::LeanObject,
    mut v_e_1116_: *mut leanh::LeanObject,
    mut v_value_1117_: *mut leanh::LeanObject,
    mut v_____do__lift_1118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1120_: u8 = 0;
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: usize = 0;
    let mut v___x_1124_: u8 = 0;
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec_ref(v_e_1116_);
                    v___x_1121_ = l_Lean_Expr_letE___override(
                        v_declName_1111_,
                        v_type_1112_,
                        v_____do__lift_1118_,
                        v_body_1113_,
                        v_nondep_1114_,
                    );
                    v___x_1122_ = leanh::lean_apply_2(
                        v_toPure_1115_,
                        leanh::lean_box(0),
                        v___x_1121_,
                    );
                    return v___x_1122_;
                } else {
                    v___x_1123_ = lean_ptr_addr(v_body_1113_);
                    v___x_1124_ = lean_usize_dec_eq(v___x_1123_, v___x_1123_);
                    if v___x_1124_ == 0 {
                        leanh::lean_dec_ref(v_e_1116_);
                        v___x_1125_ = l_Lean_Expr_letE___override(
                            v_declName_1111_,
                            v_type_1112_,
                            v_____do__lift_1118_,
                            v_body_1113_,
                            v_nondep_1114_,
                        );
                        v___x_1126_ = leanh::lean_apply_2(
                            v_toPure_1115_,
                            leanh::lean_box(0),
                            v___x_1125_,
                        );
                        return v___x_1126_;
                    } else {
                        leanh::lean_dec_ref(v_____do__lift_1118_);
                        leanh::lean_dec_ref(v_body_1113_);
                        leanh::lean_dec_ref(v_type_1112_);
                        leanh::lean_dec(v_declName_1111_);
                        v___x_1127_ = leanh::lean_apply_2(
                            v_toPure_1115_,
                            leanh::lean_box(0),
                            v_e_1116_,
                        );
                        return v___x_1127_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed(
    mut v_declName_1133_: *mut leanh::LeanObject,
    mut v_type_1134_: *mut leanh::LeanObject,
    mut v_body_1135_: *mut leanh::LeanObject,
    mut v_nondep_1136_: *mut leanh::LeanObject,
    mut v_toPure_1137_: *mut leanh::LeanObject,
    mut v_e_1138_: *mut leanh::LeanObject,
    mut v_value_1139_: *mut leanh::LeanObject,
    mut v_____do__lift_1140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_1188__boxed_1141_: u8 = 0;
    let mut v_res_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_1188__boxed_1141_ = (leanh::lean_unbox(v_nondep_1136_) as u8);
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
    leanh::lean_dec_ref(v_value_1139_);
    return v_res_1142_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(
    mut v_arg_1143_: *mut leanh::LeanObject,
    mut v_toPure_1144_: *mut leanh::LeanObject,
    mut v_e_1145_: *mut leanh::LeanObject,
    mut v_fn_1146_: *mut leanh::LeanObject,
    mut v_____do__lift_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1149_: u8 = 0;
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec_ref(v_e_1145_);
                    v___x_1150_ = l_Lean_Expr_app___override(v_____do__lift_1147_, v_arg_1143_);
                    v___x_1151_ = leanh::lean_apply_2(
                        v_toPure_1144_,
                        leanh::lean_box(0),
                        v___x_1150_,
                    );
                    return v___x_1151_;
                } else {
                    leanh::lean_dec_ref(v_____do__lift_1147_);
                    leanh::lean_dec_ref(v_arg_1143_);
                    v___x_1152_ = leanh::lean_apply_2(
                        v_toPure_1144_,
                        leanh::lean_box(0),
                        v_e_1145_,
                    );
                    return v___x_1152_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed(
    mut v_arg_1158_: *mut leanh::LeanObject,
    mut v_toPure_1159_: *mut leanh::LeanObject,
    mut v_e_1160_: *mut leanh::LeanObject,
    mut v_fn_1161_: *mut leanh::LeanObject,
    mut v_____do__lift_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(
        v_arg_1158_,
        v_toPure_1159_,
        v_e_1160_,
        v_fn_1161_,
        v_____do__lift_1162_,
    );
    leanh::lean_dec_ref(v_fn_1161_);
    return v_res_1163_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(
    mut v_binderName_1164_: *mut leanh::LeanObject,
    mut v_body_1165_: *mut leanh::LeanObject,
    mut v_binderInfo_1166_: u8,
    mut v_toPure_1167_: *mut leanh::LeanObject,
    mut v_e_1168_: *mut leanh::LeanObject,
    mut v_binderType_1169_: *mut leanh::LeanObject,
    mut v_____do__lift_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1172_: u8 = 0;
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec_ref(v_e_1168_);
                    v___x_1173_ = l_Lean_Expr_lam___override(
                        v_binderName_1164_,
                        v_____do__lift_1170_,
                        v_body_1165_,
                        v_binderInfo_1166_,
                    );
                    v___x_1174_ = leanh::lean_apply_2(
                        v_toPure_1167_,
                        leanh::lean_box(0),
                        v___x_1173_,
                    );
                    return v___x_1174_;
                } else {
                    v___x_1175_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1166_, v_binderInfo_1166_);
                    if v___x_1175_ == 0 {
                        leanh::lean_dec_ref(v_e_1168_);
                        v___x_1176_ = l_Lean_Expr_lam___override(
                            v_binderName_1164_,
                            v_____do__lift_1170_,
                            v_body_1165_,
                            v_binderInfo_1166_,
                        );
                        v___x_1177_ = leanh::lean_apply_2(
                            v_toPure_1167_,
                            leanh::lean_box(0),
                            v___x_1176_,
                        );
                        return v___x_1177_;
                    } else {
                        leanh::lean_dec_ref(v_____do__lift_1170_);
                        leanh::lean_dec_ref(v_body_1165_);
                        leanh::lean_dec(v_binderName_1164_);
                        v___x_1178_ = leanh::lean_apply_2(
                            v_toPure_1167_,
                            leanh::lean_box(0),
                            v_e_1168_,
                        );
                        return v___x_1178_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed(
    mut v_binderName_1184_: *mut leanh::LeanObject,
    mut v_body_1185_: *mut leanh::LeanObject,
    mut v_binderInfo_1186_: *mut leanh::LeanObject,
    mut v_toPure_1187_: *mut leanh::LeanObject,
    mut v_e_1188_: *mut leanh::LeanObject,
    mut v_binderType_1189_: *mut leanh::LeanObject,
    mut v_____do__lift_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_1262__boxed_1191_: u8 = 0;
    let mut v_res_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_1262__boxed_1191_ = (leanh::lean_unbox(v_binderInfo_1186_) as u8);
    v_res_1192_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(
        v_binderName_1184_,
        v_body_1185_,
        v_binderInfo_1262__boxed_1191_,
        v_toPure_1187_,
        v_e_1188_,
        v_binderType_1189_,
        v_____do__lift_1190_,
    );
    leanh::lean_dec_ref(v_binderType_1189_);
    return v_res_1192_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(
    mut v_binderName_1193_: *mut leanh::LeanObject,
    mut v_body_1194_: *mut leanh::LeanObject,
    mut v_binderInfo_1195_: u8,
    mut v_toPure_1196_: *mut leanh::LeanObject,
    mut v_e_1197_: *mut leanh::LeanObject,
    mut v_binderType_1198_: *mut leanh::LeanObject,
    mut v_____do__lift_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1201_: u8 = 0;
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec_ref(v_e_1197_);
                    v___x_1202_ = l_Lean_Expr_forallE___override(
                        v_binderName_1193_,
                        v_____do__lift_1199_,
                        v_body_1194_,
                        v_binderInfo_1195_,
                    );
                    v___x_1203_ = leanh::lean_apply_2(
                        v_toPure_1196_,
                        leanh::lean_box(0),
                        v___x_1202_,
                    );
                    return v___x_1203_;
                } else {
                    v___x_1204_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1195_, v_binderInfo_1195_);
                    if v___x_1204_ == 0 {
                        leanh::lean_dec_ref(v_e_1197_);
                        v___x_1205_ = l_Lean_Expr_forallE___override(
                            v_binderName_1193_,
                            v_____do__lift_1199_,
                            v_body_1194_,
                            v_binderInfo_1195_,
                        );
                        v___x_1206_ = leanh::lean_apply_2(
                            v_toPure_1196_,
                            leanh::lean_box(0),
                            v___x_1205_,
                        );
                        return v___x_1206_;
                    } else {
                        leanh::lean_dec_ref(v_____do__lift_1199_);
                        leanh::lean_dec_ref(v_body_1194_);
                        leanh::lean_dec(v_binderName_1193_);
                        v___x_1207_ = leanh::lean_apply_2(
                            v_toPure_1196_,
                            leanh::lean_box(0),
                            v_e_1197_,
                        );
                        return v___x_1207_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed(
    mut v_binderName_1213_: *mut leanh::LeanObject,
    mut v_body_1214_: *mut leanh::LeanObject,
    mut v_binderInfo_1215_: *mut leanh::LeanObject,
    mut v_toPure_1216_: *mut leanh::LeanObject,
    mut v_e_1217_: *mut leanh::LeanObject,
    mut v_binderType_1218_: *mut leanh::LeanObject,
    mut v_____do__lift_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_1303__boxed_1220_: u8 = 0;
    let mut v_res_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_1303__boxed_1220_ = (leanh::lean_unbox(v_binderInfo_1215_) as u8);
    v_res_1221_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(
        v_binderName_1213_,
        v_body_1214_,
        v_binderInfo_1303__boxed_1220_,
        v_toPure_1216_,
        v_e_1217_,
        v_binderType_1218_,
        v_____do__lift_1219_,
    );
    leanh::lean_dec_ref(v_binderType_1218_);
    return v_res_1221_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(
    mut v_declName_1222_: *mut leanh::LeanObject,
    mut v_value_1223_: *mut leanh::LeanObject,
    mut v_body_1224_: *mut leanh::LeanObject,
    mut v_nondep_1225_: u8,
    mut v_toPure_1226_: *mut leanh::LeanObject,
    mut v_e_1227_: *mut leanh::LeanObject,
    mut v_type_1228_: *mut leanh::LeanObject,
    mut v_____do__lift_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1231_: u8 = 0;
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: usize = 0;
    let mut v___x_1235_: u8 = 0;
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_dec_ref(v_e_1227_);
                    v___x_1232_ = l_Lean_Expr_letE___override(
                        v_declName_1222_,
                        v_____do__lift_1229_,
                        v_value_1223_,
                        v_body_1224_,
                        v_nondep_1225_,
                    );
                    v___x_1233_ = leanh::lean_apply_2(
                        v_toPure_1226_,
                        leanh::lean_box(0),
                        v___x_1232_,
                    );
                    return v___x_1233_;
                } else {
                    v___x_1234_ = lean_ptr_addr(v_body_1224_);
                    v___x_1235_ = lean_usize_dec_eq(v___x_1234_, v___x_1234_);
                    if v___x_1235_ == 0 {
                        leanh::lean_dec_ref(v_e_1227_);
                        v___x_1236_ = l_Lean_Expr_letE___override(
                            v_declName_1222_,
                            v_____do__lift_1229_,
                            v_value_1223_,
                            v_body_1224_,
                            v_nondep_1225_,
                        );
                        v___x_1237_ = leanh::lean_apply_2(
                            v_toPure_1226_,
                            leanh::lean_box(0),
                            v___x_1236_,
                        );
                        return v___x_1237_;
                    } else {
                        leanh::lean_dec_ref(v_____do__lift_1229_);
                        leanh::lean_dec_ref(v_body_1224_);
                        leanh::lean_dec_ref(v_value_1223_);
                        leanh::lean_dec(v_declName_1222_);
                        v___x_1238_ = leanh::lean_apply_2(
                            v_toPure_1226_,
                            leanh::lean_box(0),
                            v_e_1227_,
                        );
                        return v___x_1238_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed(
    mut v_declName_1244_: *mut leanh::LeanObject,
    mut v_value_1245_: *mut leanh::LeanObject,
    mut v_body_1246_: *mut leanh::LeanObject,
    mut v_nondep_1247_: *mut leanh::LeanObject,
    mut v_toPure_1248_: *mut leanh::LeanObject,
    mut v_e_1249_: *mut leanh::LeanObject,
    mut v_type_1250_: *mut leanh::LeanObject,
    mut v_____do__lift_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_1345__boxed_1252_: u8 = 0;
    let mut v_res_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_1345__boxed_1252_ = (leanh::lean_unbox(v_nondep_1247_) as u8);
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
    leanh::lean_dec_ref(v_type_1250_);
    return v_res_1253_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__0;
    v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
    return v___x_1256_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__2;
    v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
    return v___x_1259_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__4;
    v___x_1262_ = l_Lean_stringToMessageData(v___x_1261_);
    return v___x_1262_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(
    mut v_inst_1263_: *mut leanh::LeanObject,
    mut v_inst_1264_: *mut leanh::LeanObject,
    mut v_inst_1265_: *mut leanh::LeanObject,
    mut v_inst_1266_: *mut leanh::LeanObject,
    mut v_g_1267_: *mut leanh::LeanObject,
    mut v_n_1268_: *mut leanh::LeanObject,
    mut v_e_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: u8 = 0;
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v_expr_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1310_: u8 = 0;
    let mut v___f_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1323_: u8 = 0;
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1342_: u8 = 0;
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1356_: u8 = 0;
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1364_: u8 = 0;
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1373_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1283_ = leanh::lean_ctor_get(v_inst_1263_, 0);
                v_toBind_1284_ = leanh::lean_ctor_get(v_inst_1263_, 1);
                v_toFunctor_1285_ = leanh::lean_ctor_get(v_toApplicative_1283_, 0);
                v_toPure_1286_ = leanh::lean_ctor_get(v_toApplicative_1283_, 1);
                v___x_1294_ = leanh::lean_unsigned_to_nat(0);
                v___x_1295_ = lean_nat_dec_eq(v_n_1268_, v___x_1294_);
                if v___x_1295_ == 0 {
                    v___x_1296_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1297_ = lean_nat_dec_eq(v_n_1268_, v___x_1296_);
                    if v___x_1297_ == 0 {
                        v___x_1298_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1299_ = lean_nat_dec_eq(v_n_1268_, v___x_1298_);
                        if v___x_1299_ == 0 {
                            v___x_1300_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1301_ = lean_nat_dec_eq(v_n_1268_, v___x_1300_);
                            if v___x_1301_ == 0 {
                                if leanh::lean_obj_tag(v_e_1269_) == 10 {
                                    v_expr_1302_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                    leanh::lean_inc_ref(v_expr_1302_);
                                    v_n_1288_ = v_n_1268_;
                                    v_a_1289_ = v_expr_1302_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_g_1267_);
                                    leanh::lean_dec_ref(v_inst_1265_);
                                    leanh::lean_dec(v_inst_1264_);
                                    v_c_1271_ = v_n_1268_;
                                    v_e_1272_ = v_e_1269_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_n_1268_);
                                if leanh::lean_obj_tag(v_e_1269_) == 10 {
                                    v_expr_1303_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                    leanh::lean_inc_ref(v_expr_1303_);
                                    v_n_1288_ = v___x_1300_;
                                    v_a_1289_ = v_expr_1303_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_e_1269_);
                                    leanh::lean_dec(v_g_1267_);
                                    leanh::lean_dec_ref(v_inst_1265_);
                                    leanh::lean_dec(v_inst_1264_);
                                    v___x_1304_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__5);
                                    v___x_1305_ = l_Lean_throwError___redArg(
                                        v_inst_1263_,
                                        v_inst_1266_,
                                        v___x_1304_,
                                    );
                                    return v___x_1305_;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_n_1268_);
                            match leanh::lean_obj_tag(v_e_1269_) {
                                8 => {
                                    leanh::lean_dec_ref(v_inst_1266_);
                                    v_declName_1306_ = leanh::lean_ctor_get(v_e_1269_, 0);
                                    leanh::lean_inc(v_declName_1306_);
                                    v_type_1307_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                    leanh::lean_inc_ref(v_type_1307_);
                                    v_value_1308_ = leanh::lean_ctor_get(v_e_1269_, 2);
                                    leanh::lean_inc_ref(v_value_1308_);
                                    v_body_1309_ = leanh::lean_ctor_get(v_e_1269_, 3);
                                    leanh::lean_inc_ref(v_body_1309_);
                                    v_nondep_1310_ = leanh::lean_ctor_get_uint8(
                                        v_e_1269_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4
                                            + 8) as u32,
                                    );
                                    leanh::lean_dec_ref_known(v_e_1269_, 4);
                                    v___f_1311_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                                    leanh::lean_closure_set(v___f_1311_, 0, v_body_1309_);
                                    leanh::lean_closure_set(v___f_1311_, 1, v_g_1267_);
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
                                    v_expr_1314_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                    leanh::lean_inc_ref(v_expr_1314_);
                                    v_n_1288_ = v___x_1298_;
                                    v_a_1289_ = v_expr_1314_;
                                    state = 2;
                                    continue;
                                }
                                _ => {
                                    leanh::lean_dec(v_g_1267_);
                                    leanh::lean_dec_ref(v_inst_1265_);
                                    leanh::lean_dec(v_inst_1264_);
                                    v_c_1271_ = v___x_1298_;
                                    v_e_1272_ = v_e_1269_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_n_1268_);
                        match leanh::lean_obj_tag(v_e_1269_) {
                            5 => {
                                leanh::lean_inc(v_toPure_1286_);
                                leanh::lean_inc(v_toBind_1284_);
                                leanh::lean_dec_ref(v_inst_1266_);
                                leanh::lean_dec_ref(v_inst_1265_);
                                leanh::lean_dec(v_inst_1264_);
                                leanh::lean_dec_ref(v_inst_1263_);
                                v_fn_1315_ = leanh::lean_ctor_get(v_e_1269_, 0);
                                leanh::lean_inc_ref(v_fn_1315_);
                                v_arg_1316_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                leanh::lean_inc_ref_n(v_arg_1316_, 2);
                                v___f_1317_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 4);
                                leanh::lean_closure_set(v___f_1317_, 0, v_fn_1315_);
                                leanh::lean_closure_set(v___f_1317_, 1, v_toPure_1286_);
                                leanh::lean_closure_set(v___f_1317_, 2, v_e_1269_);
                                leanh::lean_closure_set(v___f_1317_, 3, v_arg_1316_);
                                v___x_1318_ = leanh::lean_apply_1(v_g_1267_, v_arg_1316_);
                                v___x_1319_ = leanh::lean_apply_4(
                                    v_toBind_1284_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_1318_,
                                    v___f_1317_,
                                );
                                return v___x_1319_;
                            }
                            6 => {
                                leanh::lean_dec_ref(v_inst_1266_);
                                v_binderName_1320_ = leanh::lean_ctor_get(v_e_1269_, 0);
                                leanh::lean_inc(v_binderName_1320_);
                                v_binderType_1321_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                leanh::lean_inc_ref(v_binderType_1321_);
                                v_body_1322_ = leanh::lean_ctor_get(v_e_1269_, 2);
                                leanh::lean_inc_ref(v_body_1322_);
                                v_binderInfo_1323_ = leanh::lean_ctor_get_uint8(
                                    v_e_1269_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                        as u32,
                                );
                                leanh::lean_dec_ref_known(v_e_1269_, 3);
                                v___x_1324_ = leanh::lean_box((v___x_1295_) as usize);
                                v___x_1325_ = leanh::lean_box((v___x_1297_) as usize);
                                leanh::lean_inc(v_toBind_1284_);
                                v___f_1326_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed as *mut core::ffi::c_void, 8, 7);
                                leanh::lean_closure_set(v___f_1326_, 0, v___x_1296_);
                                leanh::lean_closure_set(v___f_1326_, 1, v___x_1324_);
                                leanh::lean_closure_set(v___f_1326_, 2, v___x_1325_);
                                leanh::lean_closure_set(v___f_1326_, 3, v_inst_1264_);
                                leanh::lean_closure_set(v___f_1326_, 4, v_body_1322_);
                                leanh::lean_closure_set(v___f_1326_, 5, v_g_1267_);
                                leanh::lean_closure_set(v___f_1326_, 6, v_toBind_1284_);
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
                                leanh::lean_dec_ref(v_inst_1266_);
                                v_binderName_1329_ = leanh::lean_ctor_get(v_e_1269_, 0);
                                leanh::lean_inc(v_binderName_1329_);
                                v_binderType_1330_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                leanh::lean_inc_ref(v_binderType_1330_);
                                v_body_1331_ = leanh::lean_ctor_get(v_e_1269_, 2);
                                leanh::lean_inc_ref(v_body_1331_);
                                v_binderInfo_1332_ = leanh::lean_ctor_get_uint8(
                                    v_e_1269_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                        as u32,
                                );
                                leanh::lean_dec_ref_known(v_e_1269_, 3);
                                v___x_1333_ = leanh::lean_box((v___x_1295_) as usize);
                                v___x_1334_ = leanh::lean_box((v___x_1297_) as usize);
                                leanh::lean_inc(v_toBind_1284_);
                                v___f_1335_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed as *mut core::ffi::c_void, 8, 7);
                                leanh::lean_closure_set(v___f_1335_, 0, v___x_1296_);
                                leanh::lean_closure_set(v___f_1335_, 1, v___x_1333_);
                                leanh::lean_closure_set(v___f_1335_, 2, v___x_1334_);
                                leanh::lean_closure_set(v___f_1335_, 3, v_inst_1264_);
                                leanh::lean_closure_set(v___f_1335_, 4, v_body_1331_);
                                leanh::lean_closure_set(v___f_1335_, 5, v_g_1267_);
                                leanh::lean_closure_set(v___f_1335_, 6, v_toBind_1284_);
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
                                leanh::lean_inc(v_toPure_1286_);
                                leanh::lean_inc(v_toBind_1284_);
                                leanh::lean_dec_ref(v_inst_1266_);
                                leanh::lean_dec_ref(v_inst_1265_);
                                leanh::lean_dec(v_inst_1264_);
                                leanh::lean_dec_ref(v_inst_1263_);
                                v_declName_1338_ = leanh::lean_ctor_get(v_e_1269_, 0);
                                leanh::lean_inc(v_declName_1338_);
                                v_type_1339_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                leanh::lean_inc_ref(v_type_1339_);
                                v_value_1340_ = leanh::lean_ctor_get(v_e_1269_, 2);
                                leanh::lean_inc_ref_n(v_value_1340_, 2);
                                v_body_1341_ = leanh::lean_ctor_get(v_e_1269_, 3);
                                leanh::lean_inc_ref(v_body_1341_);
                                v_nondep_1342_ = leanh::lean_ctor_get_uint8(
                                    v_e_1269_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8)
                                        as u32,
                                );
                                v___x_1343_ = leanh::lean_box((v_nondep_1342_) as usize);
                                v___f_1344_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed as *mut core::ffi::c_void, 8, 7);
                                leanh::lean_closure_set(v___f_1344_, 0, v_declName_1338_);
                                leanh::lean_closure_set(v___f_1344_, 1, v_type_1339_);
                                leanh::lean_closure_set(v___f_1344_, 2, v_body_1341_);
                                leanh::lean_closure_set(v___f_1344_, 3, v___x_1343_);
                                leanh::lean_closure_set(v___f_1344_, 4, v_toPure_1286_);
                                leanh::lean_closure_set(v___f_1344_, 5, v_e_1269_);
                                leanh::lean_closure_set(v___f_1344_, 6, v_value_1340_);
                                v___x_1345_ = leanh::lean_apply_1(v_g_1267_, v_value_1340_);
                                v___x_1346_ = leanh::lean_apply_4(
                                    v_toBind_1284_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_1345_,
                                    v___f_1344_,
                                );
                                return v___x_1346_;
                            }
                            10 => {
                                v_expr_1347_ = leanh::lean_ctor_get(v_e_1269_, 1);
                                leanh::lean_inc_ref(v_expr_1347_);
                                v_n_1288_ = v___x_1296_;
                                v_a_1289_ = v_expr_1347_;
                                state = 2;
                                continue;
                            }
                            _ => {
                                leanh::lean_dec(v_g_1267_);
                                leanh::lean_dec_ref(v_inst_1265_);
                                leanh::lean_dec(v_inst_1264_);
                                v_c_1271_ = v___x_1296_;
                                v_e_1272_ = v_e_1269_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_n_1268_);
                    match leanh::lean_obj_tag(v_e_1269_) {
                        5 => {
                            leanh::lean_inc(v_toPure_1286_);
                            leanh::lean_inc(v_toBind_1284_);
                            leanh::lean_dec_ref(v_inst_1266_);
                            leanh::lean_dec_ref(v_inst_1265_);
                            leanh::lean_dec(v_inst_1264_);
                            leanh::lean_dec_ref(v_inst_1263_);
                            v_fn_1348_ = leanh::lean_ctor_get(v_e_1269_, 0);
                            leanh::lean_inc_ref_n(v_fn_1348_, 2);
                            v_arg_1349_ = leanh::lean_ctor_get(v_e_1269_, 1);
                            leanh::lean_inc_ref(v_arg_1349_);
                            v___f_1350_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed as *mut core::ffi::c_void, 5, 4);
                            leanh::lean_closure_set(v___f_1350_, 0, v_arg_1349_);
                            leanh::lean_closure_set(v___f_1350_, 1, v_toPure_1286_);
                            leanh::lean_closure_set(v___f_1350_, 2, v_e_1269_);
                            leanh::lean_closure_set(v___f_1350_, 3, v_fn_1348_);
                            v___x_1351_ = leanh::lean_apply_1(v_g_1267_, v_fn_1348_);
                            v___x_1352_ = leanh::lean_apply_4(
                                v_toBind_1284_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1351_,
                                v___f_1350_,
                            );
                            return v___x_1352_;
                        }
                        6 => {
                            leanh::lean_inc(v_toPure_1286_);
                            leanh::lean_inc(v_toBind_1284_);
                            leanh::lean_dec_ref(v_inst_1266_);
                            leanh::lean_dec_ref(v_inst_1265_);
                            leanh::lean_dec(v_inst_1264_);
                            leanh::lean_dec_ref(v_inst_1263_);
                            v_binderName_1353_ = leanh::lean_ctor_get(v_e_1269_, 0);
                            leanh::lean_inc(v_binderName_1353_);
                            v_binderType_1354_ = leanh::lean_ctor_get(v_e_1269_, 1);
                            leanh::lean_inc_ref_n(v_binderType_1354_, 2);
                            v_body_1355_ = leanh::lean_ctor_get(v_e_1269_, 2);
                            leanh::lean_inc_ref(v_body_1355_);
                            v_binderInfo_1356_ = leanh::lean_ctor_get_uint8(
                                v_e_1269_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            v___x_1357_ = leanh::lean_box((v_binderInfo_1356_) as usize);
                            v___f_1358_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed as *mut core::ffi::c_void, 7, 6);
                            leanh::lean_closure_set(v___f_1358_, 0, v_binderName_1353_);
                            leanh::lean_closure_set(v___f_1358_, 1, v_body_1355_);
                            leanh::lean_closure_set(v___f_1358_, 2, v___x_1357_);
                            leanh::lean_closure_set(v___f_1358_, 3, v_toPure_1286_);
                            leanh::lean_closure_set(v___f_1358_, 4, v_e_1269_);
                            leanh::lean_closure_set(v___f_1358_, 5, v_binderType_1354_);
                            v___x_1359_ = leanh::lean_apply_1(v_g_1267_, v_binderType_1354_);
                            v___x_1360_ = leanh::lean_apply_4(
                                v_toBind_1284_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1359_,
                                v___f_1358_,
                            );
                            return v___x_1360_;
                        }
                        7 => {
                            leanh::lean_inc(v_toPure_1286_);
                            leanh::lean_inc(v_toBind_1284_);
                            leanh::lean_dec_ref(v_inst_1266_);
                            leanh::lean_dec_ref(v_inst_1265_);
                            leanh::lean_dec(v_inst_1264_);
                            leanh::lean_dec_ref(v_inst_1263_);
                            v_binderName_1361_ = leanh::lean_ctor_get(v_e_1269_, 0);
                            leanh::lean_inc(v_binderName_1361_);
                            v_binderType_1362_ = leanh::lean_ctor_get(v_e_1269_, 1);
                            leanh::lean_inc_ref_n(v_binderType_1362_, 2);
                            v_body_1363_ = leanh::lean_ctor_get(v_e_1269_, 2);
                            leanh::lean_inc_ref(v_body_1363_);
                            v_binderInfo_1364_ = leanh::lean_ctor_get_uint8(
                                v_e_1269_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            v___x_1365_ = leanh::lean_box((v_binderInfo_1364_) as usize);
                            v___f_1366_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed as *mut core::ffi::c_void, 7, 6);
                            leanh::lean_closure_set(v___f_1366_, 0, v_binderName_1361_);
                            leanh::lean_closure_set(v___f_1366_, 1, v_body_1363_);
                            leanh::lean_closure_set(v___f_1366_, 2, v___x_1365_);
                            leanh::lean_closure_set(v___f_1366_, 3, v_toPure_1286_);
                            leanh::lean_closure_set(v___f_1366_, 4, v_e_1269_);
                            leanh::lean_closure_set(v___f_1366_, 5, v_binderType_1362_);
                            v___x_1367_ = leanh::lean_apply_1(v_g_1267_, v_binderType_1362_);
                            v___x_1368_ = leanh::lean_apply_4(
                                v_toBind_1284_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1367_,
                                v___f_1366_,
                            );
                            return v___x_1368_;
                        }
                        8 => {
                            leanh::lean_inc(v_toPure_1286_);
                            leanh::lean_inc(v_toBind_1284_);
                            leanh::lean_dec_ref(v_inst_1266_);
                            leanh::lean_dec_ref(v_inst_1265_);
                            leanh::lean_dec(v_inst_1264_);
                            leanh::lean_dec_ref(v_inst_1263_);
                            v_declName_1369_ = leanh::lean_ctor_get(v_e_1269_, 0);
                            leanh::lean_inc(v_declName_1369_);
                            v_type_1370_ = leanh::lean_ctor_get(v_e_1269_, 1);
                            leanh::lean_inc_ref_n(v_type_1370_, 2);
                            v_value_1371_ = leanh::lean_ctor_get(v_e_1269_, 2);
                            leanh::lean_inc_ref(v_value_1371_);
                            v_body_1372_ = leanh::lean_ctor_get(v_e_1269_, 3);
                            leanh::lean_inc_ref(v_body_1372_);
                            v_nondep_1373_ = leanh::lean_ctor_get_uint8(
                                v_e_1269_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            v___x_1374_ = leanh::lean_box((v_nondep_1373_) as usize);
                            v___f_1375_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed as *mut core::ffi::c_void, 8, 7);
                            leanh::lean_closure_set(v___f_1375_, 0, v_declName_1369_);
                            leanh::lean_closure_set(v___f_1375_, 1, v_value_1371_);
                            leanh::lean_closure_set(v___f_1375_, 2, v_body_1372_);
                            leanh::lean_closure_set(v___f_1375_, 3, v___x_1374_);
                            leanh::lean_closure_set(v___f_1375_, 4, v_toPure_1286_);
                            leanh::lean_closure_set(v___f_1375_, 5, v_e_1269_);
                            leanh::lean_closure_set(v___f_1375_, 6, v_type_1370_);
                            v___x_1376_ = leanh::lean_apply_1(v_g_1267_, v_type_1370_);
                            v___x_1377_ = leanh::lean_apply_4(
                                v_toBind_1284_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1376_,
                                v___f_1375_,
                            );
                            return v___x_1377_;
                        }
                        11 => {
                            leanh::lean_inc_ref(v_toFunctor_1285_);
                            leanh::lean_dec_ref(v_inst_1266_);
                            leanh::lean_dec_ref(v_inst_1265_);
                            leanh::lean_dec(v_inst_1264_);
                            leanh::lean_dec_ref(v_inst_1263_);
                            v_struct_1378_ = leanh::lean_ctor_get(v_e_1269_, 2);
                            leanh::lean_inc_ref(v_struct_1378_);
                            v_map_1379_ = leanh::lean_ctor_get(v_toFunctor_1285_, 0);
                            leanh::lean_inc(v_map_1379_);
                            leanh::lean_dec_ref(v_toFunctor_1285_);
                            v___x_1380_ = leanh::lean_alloc_closure(
                                l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            leanh::lean_closure_set(v___x_1380_, 0, v_e_1269_);
                            v___x_1381_ = leanh::lean_apply_1(v_g_1267_, v_struct_1378_);
                            v___x_1382_ = leanh::lean_apply_4(
                                v_map_1379_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1380_,
                                v___x_1381_,
                            );
                            return v___x_1382_;
                        }
                        10 => {
                            v_expr_1383_ = leanh::lean_ctor_get(v_e_1269_, 1);
                            leanh::lean_inc_ref(v_expr_1383_);
                            v_n_1288_ = v___x_1294_;
                            v_a_1289_ = v_expr_1383_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec(v_g_1267_);
                            leanh::lean_dec_ref(v_inst_1265_);
                            leanh::lean_dec(v_inst_1264_);
                            v_c_1271_ = v___x_1294_;
                            v_e_1272_ = v_e_1269_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1273_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1);
                v___x_1274_ = l_Nat_reprFast(v_c_1271_);
                v___x_1275_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
                v___x_1276_ = l_Lean_MessageData_ofFormat(v___x_1275_);
                v___x_1277_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1277_, 0, v___x_1273_);
                leanh::lean_ctor_set(v___x_1277_, 1, v___x_1276_);
                v___x_1278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
                v___x_1279_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1279_, 0, v___x_1277_);
                leanh::lean_ctor_set(v___x_1279_, 1, v___x_1278_);
                v___x_1280_ = l_Lean_MessageData_ofExpr(v_e_1272_);
                v___x_1281_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1281_, 0, v___x_1279_);
                leanh::lean_ctor_set(v___x_1281_, 1, v___x_1280_);
                v___x_1282_ = l_Lean_throwError___redArg(v_inst_1263_, v_inst_1266_, v___x_1281_);
                return v___x_1282_;
            }
            2 => {
                v_map_1290_ = leanh::lean_ctor_get(v_toFunctor_1285_, 0);
                leanh::lean_inc(v_map_1290_);
                v___x_1291_ = leanh::lean_alloc_closure(
                    l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___x_1291_, 0, v_e_1269_);
                v___x_1292_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(
                    v_inst_1263_,
                    v_inst_1264_,
                    v_inst_1265_,
                    v_inst_1266_,
                    v_g_1267_,
                    v_n_1288_,
                    v_a_1289_,
                );
                v___x_1293_ = leanh::lean_apply_4(
                    v_map_1290_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_M_1384_: *mut leanh::LeanObject,
    mut v_inst_1385_: *mut leanh::LeanObject,
    mut v_inst_1386_: *mut leanh::LeanObject,
    mut v_inst_1387_: *mut leanh::LeanObject,
    mut v_inst_1388_: *mut leanh::LeanObject,
    mut v_g_1389_: *mut leanh::LeanObject,
    mut v_n_1390_: *mut leanh::LeanObject,
    mut v_e_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1393_: *mut leanh::LeanObject,
    mut v_inst_1394_: *mut leanh::LeanObject,
    mut v_inst_1395_: *mut leanh::LeanObject,
    mut v_inst_1396_: *mut leanh::LeanObject,
    mut v_g_1397_: *mut leanh::LeanObject,
    mut v_x_1398_: *mut leanh::LeanObject,
    mut v_x_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1398_) == 0 {
        let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1396_);
        leanh::lean_dec_ref(v_inst_1395_);
        leanh::lean_dec(v_inst_1394_);
        leanh::lean_dec_ref(v_inst_1393_);
        v___x_1400_ = leanh::lean_apply_1(v_g_1397_, v_x_1399_);
        return v___x_1400_;
    } else {
        let mut v_head_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_1401_ = leanh::lean_ctor_get(v_x_1398_, 0);
        leanh::lean_inc(v_head_1401_);
        v_tail_1402_ = leanh::lean_ctor_get(v_x_1398_, 1);
        leanh::lean_inc(v_tail_1402_);
        leanh::lean_dec_ref_known(v_x_1398_, 2);
        leanh::lean_inc_ref(v_inst_1396_);
        leanh::lean_inc_ref(v_inst_1395_);
        leanh::lean_inc(v_inst_1394_);
        leanh::lean_inc_ref(v_inst_1393_);
        v___x_1403_ = leanh::lean_alloc_closure(
            l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___x_1403_, 0, v_inst_1393_);
        leanh::lean_closure_set(v___x_1403_, 1, v_inst_1394_);
        leanh::lean_closure_set(v___x_1403_, 2, v_inst_1395_);
        leanh::lean_closure_set(v___x_1403_, 3, v_inst_1396_);
        leanh::lean_closure_set(v___x_1403_, 4, v_g_1397_);
        leanh::lean_closure_set(v___x_1403_, 5, v_tail_1402_);
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
    mut v_M_1405_: *mut leanh::LeanObject,
    mut v_inst_1406_: *mut leanh::LeanObject,
    mut v_inst_1407_: *mut leanh::LeanObject,
    mut v_inst_1408_: *mut leanh::LeanObject,
    mut v_inst_1409_: *mut leanh::LeanObject,
    mut v_g_1410_: *mut leanh::LeanObject,
    mut v_x_1411_: *mut leanh::LeanObject,
    mut v_x_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1414_: *mut leanh::LeanObject,
    mut v_inst_1415_: *mut leanh::LeanObject,
    mut v_inst_1416_: *mut leanh::LeanObject,
    mut v_inst_1417_: *mut leanh::LeanObject,
    mut v_replace_1418_: *mut leanh::LeanObject,
    mut v_p_1419_: *mut leanh::LeanObject,
    mut v_root_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1424_: *mut leanh::LeanObject,
    mut v_inst_1425_: *mut leanh::LeanObject,
    mut v_inst_1426_: *mut leanh::LeanObject,
    mut v_inst_1427_: *mut leanh::LeanObject,
    mut v_replace_1428_: *mut leanh::LeanObject,
    mut v_p_1429_: *mut leanh::LeanObject,
    mut v_root_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1431_ = l_Lean_Meta_replaceSubexpr___redArg(
        v_inst_1424_,
        v_inst_1425_,
        v_inst_1426_,
        v_inst_1427_,
        v_replace_1428_,
        v_p_1429_,
        v_root_1430_,
    );
    leanh::lean_dec(v_p_1429_);
    return v_res_1431_;
}
pub unsafe fn l_Lean_Meta_replaceSubexpr(
    mut v_M_1432_: *mut leanh::LeanObject,
    mut v_inst_1433_: *mut leanh::LeanObject,
    mut v_inst_1434_: *mut leanh::LeanObject,
    mut v_inst_1435_: *mut leanh::LeanObject,
    mut v_inst_1436_: *mut leanh::LeanObject,
    mut v_replace_1437_: *mut leanh::LeanObject,
    mut v_p_1438_: *mut leanh::LeanObject,
    mut v_root_1439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_1441_: *mut leanh::LeanObject,
    mut v_inst_1442_: *mut leanh::LeanObject,
    mut v_inst_1443_: *mut leanh::LeanObject,
    mut v_inst_1444_: *mut leanh::LeanObject,
    mut v_inst_1445_: *mut leanh::LeanObject,
    mut v_replace_1446_: *mut leanh::LeanObject,
    mut v_p_1447_: *mut leanh::LeanObject,
    mut v_root_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_p_1447_);
    return v_res_1449_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0(
    mut v_fvars_1450_: *mut leanh::LeanObject,
    mut v_k_1451_: *mut leanh::LeanObject,
    mut v_body_1452_: *mut leanh::LeanObject,
    mut v_x_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1454_ = lean_array_push(v_fvars_1450_, v_x_1453_);
    v___x_1455_ = leanh::lean_apply_2(v_k_1451_, v___x_1454_, v_body_1452_);
    return v___x_1455_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1(
    mut v_fvars_1456_: *mut leanh::LeanObject,
    mut v_k_1457_: *mut leanh::LeanObject,
    mut v_b_1458_: *mut leanh::LeanObject,
    mut v_x_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = lean_array_push(v_fvars_1456_, v_x_1459_);
    v___x_1461_ = leanh::lean_apply_2(v_k_1457_, v___x_1460_, v_b_1458_);
    return v___x_1461_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__0;
    v___x_1464_ = l_Lean_stringToMessageData(v___x_1463_);
    return v___x_1464_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(
    mut v_inst_1465_: *mut leanh::LeanObject,
    mut v_inst_1466_: *mut leanh::LeanObject,
    mut v_inst_1467_: *mut leanh::LeanObject,
    mut v_k_1468_: *mut leanh::LeanObject,
    mut v_fvars_1469_: *mut leanh::LeanObject,
    mut v_n_1470_: *mut leanh::LeanObject,
    mut v_e_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1489_: u8 = 0;
    let mut v___f_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: u8 = 0;
    let mut v_expr_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: u8 = 0;
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1520_: u8 = 0;
    let mut v_binderName_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1524_: u8 = 0;
    let mut v_value_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1494_ = leanh::lean_unsigned_to_nat(3);
                v___x_1495_ = lean_nat_dec_eq(v_n_1470_, v___x_1494_);
                if v___x_1495_ == 0 {
                    v___x_1496_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1497_ = lean_nat_dec_eq(v_n_1470_, v___x_1496_);
                    if v___x_1497_ == 0 {
                        v___x_1498_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1499_ = lean_nat_dec_eq(v_n_1470_, v___x_1498_);
                        if v___x_1499_ == 0 {
                            v___x_1500_ = leanh::lean_unsigned_to_nat(2);
                            v___x_1501_ = lean_nat_dec_eq(v_n_1470_, v___x_1500_);
                            if v___x_1501_ == 0 {
                                if leanh::lean_obj_tag(v_e_1471_) == 10 {
                                    v_expr_1502_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                    leanh::lean_inc_ref(v_expr_1502_);
                                    leanh::lean_dec_ref_known(v_e_1471_, 2);
                                    v_e_1471_ = v_expr_1502_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_fvars_1469_);
                                    leanh::lean_dec(v_k_1468_);
                                    leanh::lean_dec_ref(v_inst_1466_);
                                    v_c_1473_ = v_n_1470_;
                                    v_e_1474_ = v_e_1471_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_n_1470_);
                                match leanh::lean_obj_tag(v_e_1471_) {
                                    8 => {
                                        leanh::lean_dec_ref(v_inst_1467_);
                                        v_declName_1504_ =
                                            leanh::lean_ctor_get(v_e_1471_, 0);
                                        leanh::lean_inc(v_declName_1504_);
                                        v_type_1505_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                        leanh::lean_inc_ref(v_type_1505_);
                                        v_value_1506_ = leanh::lean_ctor_get(v_e_1471_, 2);
                                        leanh::lean_inc_ref(v_value_1506_);
                                        v_body_1507_ = leanh::lean_ctor_get(v_e_1471_, 3);
                                        leanh::lean_inc_ref(v_body_1507_);
                                        leanh::lean_dec_ref_known(v_e_1471_, 4);
                                        leanh::lean_inc_ref(v_fvars_1469_);
                                        v___f_1508_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
                                        leanh::lean_closure_set(
                                            v___f_1508_,
                                            0,
                                            v_fvars_1469_,
                                        );
                                        leanh::lean_closure_set(v___f_1508_, 1, v_k_1468_);
                                        leanh::lean_closure_set(
                                            v___f_1508_,
                                            2,
                                            v_body_1507_,
                                        );
                                        v___x_1509_ =
                                            lean_expr_instantiate_rev(v_type_1505_, v_fvars_1469_);
                                        leanh::lean_dec_ref(v_type_1505_);
                                        v___x_1510_ =
                                            lean_expr_instantiate_rev(v_value_1506_, v_fvars_1469_);
                                        leanh::lean_dec_ref(v_fvars_1469_);
                                        leanh::lean_dec_ref(v_value_1506_);
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
                                        v_expr_1513_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                        leanh::lean_inc_ref(v_expr_1513_);
                                        leanh::lean_dec_ref_known(v_e_1471_, 2);
                                        v_n_1470_ = v___x_1500_;
                                        v_e_1471_ = v_expr_1513_;
                                        state = 0;
                                        continue;
                                    }
                                    _ => {
                                        leanh::lean_dec_ref(v_fvars_1469_);
                                        leanh::lean_dec(v_k_1468_);
                                        leanh::lean_dec_ref(v_inst_1466_);
                                        v_c_1473_ = v___x_1500_;
                                        v_e_1474_ = v_e_1471_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_n_1470_);
                            match leanh::lean_obj_tag(v_e_1471_) {
                                5 => {
                                    leanh::lean_dec_ref(v_inst_1467_);
                                    leanh::lean_dec_ref(v_inst_1466_);
                                    leanh::lean_dec_ref(v_inst_1465_);
                                    v_arg_1515_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                    leanh::lean_inc_ref(v_arg_1515_);
                                    leanh::lean_dec_ref_known(v_e_1471_, 2);
                                    v___x_1516_ = leanh::lean_apply_2(
                                        v_k_1468_,
                                        v_fvars_1469_,
                                        v_arg_1515_,
                                    );
                                    return v___x_1516_;
                                }
                                6 => {
                                    leanh::lean_dec_ref(v_inst_1467_);
                                    v_binderName_1517_ = leanh::lean_ctor_get(v_e_1471_, 0);
                                    leanh::lean_inc(v_binderName_1517_);
                                    v_binderType_1518_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                    leanh::lean_inc_ref(v_binderType_1518_);
                                    v_body_1519_ = leanh::lean_ctor_get(v_e_1471_, 2);
                                    leanh::lean_inc_ref(v_body_1519_);
                                    v_binderInfo_1520_ = leanh::lean_ctor_get_uint8(
                                        v_e_1471_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    leanh::lean_dec_ref_known(v_e_1471_, 3);
                                    v_n_1486_ = v_binderName_1517_;
                                    v_y_1487_ = v_binderType_1518_;
                                    v_b_1488_ = v_body_1519_;
                                    v_c_1489_ = v_binderInfo_1520_;
                                    state = 2;
                                    continue;
                                }
                                7 => {
                                    leanh::lean_dec_ref(v_inst_1467_);
                                    v_binderName_1521_ = leanh::lean_ctor_get(v_e_1471_, 0);
                                    leanh::lean_inc(v_binderName_1521_);
                                    v_binderType_1522_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                    leanh::lean_inc_ref(v_binderType_1522_);
                                    v_body_1523_ = leanh::lean_ctor_get(v_e_1471_, 2);
                                    leanh::lean_inc_ref(v_body_1523_);
                                    v_binderInfo_1524_ = leanh::lean_ctor_get_uint8(
                                        v_e_1471_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    leanh::lean_dec_ref_known(v_e_1471_, 3);
                                    v_n_1486_ = v_binderName_1521_;
                                    v_y_1487_ = v_binderType_1522_;
                                    v_b_1488_ = v_body_1523_;
                                    v_c_1489_ = v_binderInfo_1524_;
                                    state = 2;
                                    continue;
                                }
                                8 => {
                                    leanh::lean_dec_ref(v_inst_1467_);
                                    leanh::lean_dec_ref(v_inst_1466_);
                                    leanh::lean_dec_ref(v_inst_1465_);
                                    v_value_1525_ = leanh::lean_ctor_get(v_e_1471_, 2);
                                    leanh::lean_inc_ref(v_value_1525_);
                                    leanh::lean_dec_ref_known(v_e_1471_, 4);
                                    v___x_1526_ = leanh::lean_apply_2(
                                        v_k_1468_,
                                        v_fvars_1469_,
                                        v_value_1525_,
                                    );
                                    return v___x_1526_;
                                }
                                10 => {
                                    v_expr_1527_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                    leanh::lean_inc_ref(v_expr_1527_);
                                    leanh::lean_dec_ref_known(v_e_1471_, 2);
                                    v_n_1470_ = v___x_1498_;
                                    v_e_1471_ = v_expr_1527_;
                                    state = 0;
                                    continue;
                                }
                                _ => {
                                    leanh::lean_dec_ref(v_fvars_1469_);
                                    leanh::lean_dec(v_k_1468_);
                                    leanh::lean_dec_ref(v_inst_1466_);
                                    v_c_1473_ = v___x_1498_;
                                    v_e_1474_ = v_e_1471_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_n_1470_);
                        match leanh::lean_obj_tag(v_e_1471_) {
                            5 => {
                                leanh::lean_dec_ref(v_inst_1467_);
                                leanh::lean_dec_ref(v_inst_1466_);
                                leanh::lean_dec_ref(v_inst_1465_);
                                v_fn_1529_ = leanh::lean_ctor_get(v_e_1471_, 0);
                                leanh::lean_inc_ref(v_fn_1529_);
                                leanh::lean_dec_ref_known(v_e_1471_, 2);
                                v___x_1530_ = leanh::lean_apply_2(
                                    v_k_1468_,
                                    v_fvars_1469_,
                                    v_fn_1529_,
                                );
                                return v___x_1530_;
                            }
                            6 => {
                                leanh::lean_dec_ref(v_inst_1467_);
                                leanh::lean_dec_ref(v_inst_1466_);
                                leanh::lean_dec_ref(v_inst_1465_);
                                v_binderType_1531_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                leanh::lean_inc_ref(v_binderType_1531_);
                                leanh::lean_dec_ref_known(v_e_1471_, 3);
                                v___x_1532_ = leanh::lean_apply_2(
                                    v_k_1468_,
                                    v_fvars_1469_,
                                    v_binderType_1531_,
                                );
                                return v___x_1532_;
                            }
                            7 => {
                                leanh::lean_dec_ref(v_inst_1467_);
                                leanh::lean_dec_ref(v_inst_1466_);
                                leanh::lean_dec_ref(v_inst_1465_);
                                v_binderType_1533_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                leanh::lean_inc_ref(v_binderType_1533_);
                                leanh::lean_dec_ref_known(v_e_1471_, 3);
                                v___x_1534_ = leanh::lean_apply_2(
                                    v_k_1468_,
                                    v_fvars_1469_,
                                    v_binderType_1533_,
                                );
                                return v___x_1534_;
                            }
                            8 => {
                                leanh::lean_dec_ref(v_inst_1467_);
                                leanh::lean_dec_ref(v_inst_1466_);
                                leanh::lean_dec_ref(v_inst_1465_);
                                v_type_1535_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                leanh::lean_inc_ref(v_type_1535_);
                                leanh::lean_dec_ref_known(v_e_1471_, 4);
                                v___x_1536_ = leanh::lean_apply_2(
                                    v_k_1468_,
                                    v_fvars_1469_,
                                    v_type_1535_,
                                );
                                return v___x_1536_;
                            }
                            11 => {
                                leanh::lean_dec_ref(v_inst_1467_);
                                leanh::lean_dec_ref(v_inst_1466_);
                                leanh::lean_dec_ref(v_inst_1465_);
                                v_struct_1537_ = leanh::lean_ctor_get(v_e_1471_, 2);
                                leanh::lean_inc_ref(v_struct_1537_);
                                leanh::lean_dec_ref_known(v_e_1471_, 3);
                                v___x_1538_ = leanh::lean_apply_2(
                                    v_k_1468_,
                                    v_fvars_1469_,
                                    v_struct_1537_,
                                );
                                return v___x_1538_;
                            }
                            10 => {
                                v_expr_1539_ = leanh::lean_ctor_get(v_e_1471_, 1);
                                leanh::lean_inc_ref(v_expr_1539_);
                                leanh::lean_dec_ref_known(v_e_1471_, 2);
                                v_n_1470_ = v___x_1496_;
                                v_e_1471_ = v_expr_1539_;
                                state = 0;
                                continue;
                            }
                            _ => {
                                leanh::lean_dec_ref(v_fvars_1469_);
                                leanh::lean_dec(v_k_1468_);
                                leanh::lean_dec_ref(v_inst_1466_);
                                v_c_1473_ = v___x_1496_;
                                v_e_1474_ = v_e_1471_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1471_);
                    leanh::lean_dec(v_n_1470_);
                    leanh::lean_dec_ref(v_fvars_1469_);
                    leanh::lean_dec(v_k_1468_);
                    leanh::lean_dec_ref(v_inst_1466_);
                    v___x_1541_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___closed__1);
                    v___x_1542_ =
                        l_Lean_throwError___redArg(v_inst_1465_, v_inst_1467_, v___x_1541_);
                    return v___x_1542_;
                }
            }
            1 => {
                v___x_1475_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__1);
                v___x_1476_ = l_Nat_reprFast(v_c_1473_);
                v___x_1477_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1477_, 0, v___x_1476_);
                v___x_1478_ = l_Lean_MessageData_ofFormat(v___x_1477_);
                v___x_1479_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1479_, 0, v___x_1475_);
                leanh::lean_ctor_set(v___x_1479_, 1, v___x_1478_);
                v___x_1480_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
                v___x_1481_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1481_, 0, v___x_1479_);
                leanh::lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                v___x_1482_ = l_Lean_MessageData_ofExpr(v_e_1474_);
                v___x_1483_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1483_, 0, v___x_1481_);
                leanh::lean_ctor_set(v___x_1483_, 1, v___x_1482_);
                v___x_1484_ = l_Lean_throwError___redArg(v_inst_1465_, v_inst_1467_, v___x_1483_);
                return v___x_1484_;
            }
            2 => {
                leanh::lean_inc_ref(v_fvars_1469_);
                v___f_1490_ = leanh::lean_alloc_closure(
                    l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_1490_, 0, v_fvars_1469_);
                leanh::lean_closure_set(v___f_1490_, 1, v_k_1468_);
                leanh::lean_closure_set(v___f_1490_, 2, v_b_1488_);
                v___x_1491_ = lean_expr_instantiate_rev(v_y_1487_, v_fvars_1469_);
                leanh::lean_dec_ref(v_fvars_1469_);
                leanh::lean_dec_ref(v_y_1487_);
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
    mut v_M_1543_: *mut leanh::LeanObject,
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_inst_1545_: *mut leanh::LeanObject,
    mut v_inst_1546_: *mut leanh::LeanObject,
    mut v_00_u03b1_1547_: *mut leanh::LeanObject,
    mut v_k_1548_: *mut leanh::LeanObject,
    mut v_fvars_1549_: *mut leanh::LeanObject,
    mut v_n_1550_: *mut leanh::LeanObject,
    mut v_e_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_fvars_1553_: *mut leanh::LeanObject,
    mut v_k_1554_: *mut leanh::LeanObject,
    mut v_otherFvars_1555_: *mut leanh::LeanObject,
    mut v___y_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = l_Array_append___redArg(v_fvars_1553_, v_otherFvars_1555_);
    v___x_1558_ = leanh::lean_apply_2(v_k_1554_, v___x_1557_, v___y_1556_);
    return v___x_1558_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed(
    mut v_fvars_1559_: *mut leanh::LeanObject,
    mut v_k_1560_: *mut leanh::LeanObject,
    mut v_otherFvars_1561_: *mut leanh::LeanObject,
    mut v___y_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(
        v_fvars_1559_,
        v_k_1560_,
        v_otherFvars_1561_,
        v___y_1562_,
    );
    leanh::lean_dec_ref(v_otherFvars_1561_);
    return v_res_1563_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2(
    mut v_inst_1566_: *mut leanh::LeanObject,
    mut v_inst_1567_: *mut leanh::LeanObject,
    mut v_inst_1568_: *mut leanh::LeanObject,
    mut v_inst_1569_: *mut leanh::LeanObject,
    mut v___f_1570_: *mut leanh::LeanObject,
    mut v_tail_1571_: *mut leanh::LeanObject,
    mut v_y_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1575_: *mut leanh::LeanObject,
    mut v_inst_1576_: *mut leanh::LeanObject,
    mut v_inst_1577_: *mut leanh::LeanObject,
    mut v_inst_1578_: *mut leanh::LeanObject,
    mut v_k_1579_: *mut leanh::LeanObject,
    mut v_fvars_1580_: *mut leanh::LeanObject,
    mut v_x_1581_: *mut leanh::LeanObject,
    mut v_x_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1581_) == 0 {
        let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1578_);
        leanh::lean_dec_ref(v_inst_1577_);
        leanh::lean_dec(v_inst_1576_);
        leanh::lean_dec_ref(v_inst_1575_);
        v___x_1583_ = lean_expr_instantiate_rev(v_x_1582_, v_fvars_1580_);
        leanh::lean_dec_ref(v_x_1582_);
        v___x_1584_ = leanh::lean_apply_2(v_k_1579_, v_fvars_1580_, v___x_1583_);
        return v___x_1584_;
    } else {
        let mut v_toBind_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: u8 = 0;
        v_toBind_1585_ = leanh::lean_ctor_get(v_inst_1575_, 1);
        v_head_1586_ = leanh::lean_ctor_get(v_x_1581_, 0);
        leanh::lean_inc(v_head_1586_);
        v_tail_1587_ = leanh::lean_ctor_get(v_x_1581_, 1);
        leanh::lean_inc(v_tail_1587_);
        leanh::lean_dec_ref_known(v_x_1581_, 2);
        v___x_1588_ = leanh::lean_unsigned_to_nat(3);
        v___x_1589_ = lean_nat_dec_eq(v_head_1586_, v___x_1588_);
        if v___x_1589_ == 0 {
            let mut v___f_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_inst_1578_);
            leanh::lean_inc_ref(v_inst_1577_);
            leanh::lean_inc_ref(v_inst_1575_);
            v___f_1590_ = leanh::lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0
                    as *mut core::ffi::c_void,
                8,
                6,
            );
            leanh::lean_closure_set(v___f_1590_, 0, v_inst_1575_);
            leanh::lean_closure_set(v___f_1590_, 1, v_inst_1576_);
            leanh::lean_closure_set(v___f_1590_, 2, v_inst_1577_);
            leanh::lean_closure_set(v___f_1590_, 3, v_inst_1578_);
            leanh::lean_closure_set(v___f_1590_, 4, v_k_1579_);
            leanh::lean_closure_set(v___f_1590_, 5, v_tail_1587_);
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
            let mut v___f_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_toBind_1585_);
            leanh::lean_dec(v_head_1586_);
            leanh::lean_inc_ref(v_fvars_1580_);
            v___f_1592_ = leanh::lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                4,
                2,
            );
            leanh::lean_closure_set(v___f_1592_, 0, v_fvars_1580_);
            leanh::lean_closure_set(v___f_1592_, 1, v_k_1579_);
            leanh::lean_inc(v_inst_1576_);
            v___f_1593_ = leanh::lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2
                    as *mut core::ffi::c_void,
                7,
                6,
            );
            leanh::lean_closure_set(v___f_1593_, 0, v_inst_1575_);
            leanh::lean_closure_set(v___f_1593_, 1, v_inst_1576_);
            leanh::lean_closure_set(v___f_1593_, 2, v_inst_1577_);
            leanh::lean_closure_set(v___f_1593_, 3, v_inst_1578_);
            leanh::lean_closure_set(v___f_1593_, 4, v___f_1592_);
            leanh::lean_closure_set(v___f_1593_, 5, v_tail_1587_);
            v___x_1594_ = lean_expr_instantiate_rev(v_x_1582_, v_fvars_1580_);
            leanh::lean_dec_ref(v_fvars_1580_);
            leanh::lean_dec_ref(v_x_1582_);
            v___x_1595_ = leanh::lean_alloc_closure(
                l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
                6,
                1,
            );
            leanh::lean_closure_set(v___x_1595_, 0, v___x_1594_);
            v___x_1596_ =
                leanh::lean_apply_2(v_inst_1576_, leanh::lean_box(0), v___x_1595_);
            v___x_1597_ = leanh::lean_apply_4(
                v_toBind_1585_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1596_,
                v___f_1593_,
            );
            return v___x_1597_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0(
    mut v_inst_1598_: *mut leanh::LeanObject,
    mut v_inst_1599_: *mut leanh::LeanObject,
    mut v_inst_1600_: *mut leanh::LeanObject,
    mut v_inst_1601_: *mut leanh::LeanObject,
    mut v_k_1602_: *mut leanh::LeanObject,
    mut v_tail_1603_: *mut leanh::LeanObject,
    mut v_fvars_1604_: *mut leanh::LeanObject,
    mut v___y_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_1607_: *mut leanh::LeanObject,
    mut v_inst_1608_: *mut leanh::LeanObject,
    mut v_inst_1609_: *mut leanh::LeanObject,
    mut v_inst_1610_: *mut leanh::LeanObject,
    mut v_inst_1611_: *mut leanh::LeanObject,
    mut v_00_u03b1_1612_: *mut leanh::LeanObject,
    mut v_k_1613_: *mut leanh::LeanObject,
    mut v_fvars_1614_: *mut leanh::LeanObject,
    mut v_x_1615_: *mut leanh::LeanObject,
    mut v_x_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1618_: *mut leanh::LeanObject,
    mut v_inst_1619_: *mut leanh::LeanObject,
    mut v_inst_1620_: *mut leanh::LeanObject,
    mut v_inst_1621_: *mut leanh::LeanObject,
    mut v_visit_1622_: *mut leanh::LeanObject,
    mut v_p_1623_: *mut leanh::LeanObject,
    mut v_root_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1629_: *mut leanh::LeanObject,
    mut v_inst_1630_: *mut leanh::LeanObject,
    mut v_inst_1631_: *mut leanh::LeanObject,
    mut v_inst_1632_: *mut leanh::LeanObject,
    mut v_visit_1633_: *mut leanh::LeanObject,
    mut v_p_1634_: *mut leanh::LeanObject,
    mut v_root_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1636_ = l_Lean_Meta_viewSubexpr___redArg(
        v_inst_1629_,
        v_inst_1630_,
        v_inst_1631_,
        v_inst_1632_,
        v_visit_1633_,
        v_p_1634_,
        v_root_1635_,
    );
    leanh::lean_dec(v_p_1634_);
    return v_res_1636_;
}
pub unsafe fn l_Lean_Meta_viewSubexpr(
    mut v_M_1637_: *mut leanh::LeanObject,
    mut v_inst_1638_: *mut leanh::LeanObject,
    mut v_inst_1639_: *mut leanh::LeanObject,
    mut v_inst_1640_: *mut leanh::LeanObject,
    mut v_inst_1641_: *mut leanh::LeanObject,
    mut v_00_u03b1_1642_: *mut leanh::LeanObject,
    mut v_visit_1643_: *mut leanh::LeanObject,
    mut v_p_1644_: *mut leanh::LeanObject,
    mut v_root_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_1647_: *mut leanh::LeanObject,
    mut v_inst_1648_: *mut leanh::LeanObject,
    mut v_inst_1649_: *mut leanh::LeanObject,
    mut v_inst_1650_: *mut leanh::LeanObject,
    mut v_inst_1651_: *mut leanh::LeanObject,
    mut v_00_u03b1_1652_: *mut leanh::LeanObject,
    mut v_visit_1653_: *mut leanh::LeanObject,
    mut v_p_1654_: *mut leanh::LeanObject,
    mut v_root_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_p_1654_);
    return v_res_1656_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(
    mut v_fvars_1657_: *mut leanh::LeanObject,
    mut v_k_1658_: *mut leanh::LeanObject,
    mut v_otherFvars_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Array_append___redArg(v_fvars_1657_, v_otherFvars_1659_);
    v___x_1664_ = leanh::lean_apply_4(
        v_k_1658_,
        v___x_1663_,
        v___y_1660_,
        v___y_1661_,
        v___y_1662_,
    );
    return v___x_1664_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed(
    mut v_fvars_1665_: *mut leanh::LeanObject,
    mut v_k_1666_: *mut leanh::LeanObject,
    mut v_otherFvars_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(
        v_fvars_1665_,
        v_k_1666_,
        v_otherFvars_1667_,
        v___y_1668_,
        v___y_1669_,
        v___y_1670_,
    );
    leanh::lean_dec_ref(v_otherFvars_1667_);
    return v_res_1671_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2(
    mut v_inst_1672_: *mut leanh::LeanObject,
    mut v_inst_1673_: *mut leanh::LeanObject,
    mut v_inst_1674_: *mut leanh::LeanObject,
    mut v_inst_1675_: *mut leanh::LeanObject,
    mut v___f_1676_: *mut leanh::LeanObject,
    mut v_tail_1677_: *mut leanh::LeanObject,
    mut v_y_1678_: *mut leanh::LeanObject,
    mut v_acc_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1682_: *mut leanh::LeanObject,
    mut v_inst_1683_: *mut leanh::LeanObject,
    mut v_inst_1684_: *mut leanh::LeanObject,
    mut v_inst_1685_: *mut leanh::LeanObject,
    mut v___f_1686_: *mut leanh::LeanObject,
    mut v_tail_1687_: *mut leanh::LeanObject,
    mut v_k_1688_: *mut leanh::LeanObject,
    mut v_fvars_1689_: *mut leanh::LeanObject,
    mut v_current_1690_: *mut leanh::LeanObject,
    mut v___x_1691_: *mut leanh::LeanObject,
    mut v_acc_1692_: *mut leanh::LeanObject,
    mut v_toBind_1693_: *mut leanh::LeanObject,
    mut v_y_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1695_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2
            as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1695_, 0, v_inst_1682_);
    leanh::lean_closure_set(v___f_1695_, 1, v_inst_1683_);
    leanh::lean_closure_set(v___f_1695_, 2, v_inst_1684_);
    leanh::lean_closure_set(v___f_1695_, 3, v_inst_1685_);
    leanh::lean_closure_set(v___f_1695_, 4, v___f_1686_);
    leanh::lean_closure_set(v___f_1695_, 5, v_tail_1687_);
    leanh::lean_closure_set(v___f_1695_, 6, v_y_1694_);
    v___x_1696_ = leanh::lean_apply_4(
        v_k_1688_,
        v_fvars_1689_,
        v_current_1690_,
        v___x_1691_,
        v_acc_1692_,
    );
    v___x_1697_ = leanh::lean_apply_4(
        v_toBind_1693_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1696_,
        v___f_1695_,
    );
    return v___x_1697_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(
    mut v_inst_1698_: *mut leanh::LeanObject,
    mut v_inst_1699_: *mut leanh::LeanObject,
    mut v_inst_1700_: *mut leanh::LeanObject,
    mut v_inst_1701_: *mut leanh::LeanObject,
    mut v_k_1702_: *mut leanh::LeanObject,
    mut v_acc_1703_: *mut leanh::LeanObject,
    mut v_address_1704_: *mut leanh::LeanObject,
    mut v_fvars_1705_: *mut leanh::LeanObject,
    mut v_current_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_address_1704_) == 0 {
        let mut v_toApplicative_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1707_ = leanh::lean_ctor_get(v_inst_1698_, 0);
        leanh::lean_inc_ref(v_toApplicative_1707_);
        leanh::lean_dec_ref(v_current_1706_);
        leanh::lean_dec_ref(v_fvars_1705_);
        leanh::lean_dec(v_k_1702_);
        leanh::lean_dec_ref(v_inst_1701_);
        leanh::lean_dec_ref(v_inst_1700_);
        leanh::lean_dec(v_inst_1699_);
        leanh::lean_dec_ref(v_inst_1698_);
        v_toPure_1708_ = leanh::lean_ctor_get(v_toApplicative_1707_, 1);
        leanh::lean_inc(v_toPure_1708_);
        leanh::lean_dec_ref(v_toApplicative_1707_);
        v___x_1709_ =
            leanh::lean_apply_2(v_toPure_1708_, leanh::lean_box(0), v_acc_1703_);
        return v___x_1709_;
    } else {
        let mut v_toBind_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1714_: u8 = 0;
        v_toBind_1710_ = leanh::lean_ctor_get(v_inst_1698_, 1);
        leanh::lean_inc(v_toBind_1710_);
        v_head_1711_ = leanh::lean_ctor_get(v_address_1704_, 0);
        leanh::lean_inc(v_head_1711_);
        v_tail_1712_ = leanh::lean_ctor_get(v_address_1704_, 1);
        leanh::lean_inc(v_tail_1712_);
        leanh::lean_dec_ref_known(v_address_1704_, 2);
        v___x_1713_ = leanh::lean_unsigned_to_nat(3);
        v___x_1714_ = lean_nat_dec_eq(v_head_1711_, v___x_1713_);
        if v___x_1714_ == 0 {
            let mut v___f_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_current_1706_);
            leanh::lean_inc(v_head_1711_);
            leanh::lean_inc_ref(v_fvars_1705_);
            leanh::lean_inc(v_k_1702_);
            v___f_1715_ = leanh::lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            leanh::lean_closure_set(v___f_1715_, 0, v_inst_1698_);
            leanh::lean_closure_set(v___f_1715_, 1, v_inst_1699_);
            leanh::lean_closure_set(v___f_1715_, 2, v_inst_1700_);
            leanh::lean_closure_set(v___f_1715_, 3, v_inst_1701_);
            leanh::lean_closure_set(v___f_1715_, 4, v_k_1702_);
            leanh::lean_closure_set(v___f_1715_, 5, v_tail_1712_);
            leanh::lean_closure_set(v___f_1715_, 6, v_fvars_1705_);
            leanh::lean_closure_set(v___f_1715_, 7, v_head_1711_);
            leanh::lean_closure_set(v___f_1715_, 8, v_current_1706_);
            v___x_1716_ = lean_expr_instantiate_rev(v_current_1706_, v_fvars_1705_);
            leanh::lean_dec_ref(v_current_1706_);
            v___x_1717_ = leanh::lean_apply_4(
                v_k_1702_,
                v_fvars_1705_,
                v___x_1716_,
                v_head_1711_,
                v_acc_1703_,
            );
            v___x_1718_ = leanh::lean_apply_4(
                v_toBind_1710_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1717_,
                v___f_1715_,
            );
            return v___x_1718_;
        } else {
            let mut v___f_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_current_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_head_1711_);
            leanh::lean_inc(v_k_1702_);
            leanh::lean_inc_ref(v_fvars_1705_);
            v___f_1719_ = leanh::lean_alloc_closure(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 2);
            leanh::lean_closure_set(v___f_1719_, 0, v_fvars_1705_);
            leanh::lean_closure_set(v___f_1719_, 1, v_k_1702_);
            v_current_1720_ = lean_expr_instantiate_rev(v_current_1706_, v_fvars_1705_);
            leanh::lean_dec_ref(v_current_1706_);
            leanh::lean_inc(v_toBind_1710_);
            leanh::lean_inc_ref(v_current_1720_);
            leanh::lean_inc(v_inst_1699_);
            v___f_1721_ = leanh::lean_alloc_closure(
                l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3
                    as *mut core::ffi::c_void,
                13,
                12,
            );
            leanh::lean_closure_set(v___f_1721_, 0, v_inst_1698_);
            leanh::lean_closure_set(v___f_1721_, 1, v_inst_1699_);
            leanh::lean_closure_set(v___f_1721_, 2, v_inst_1700_);
            leanh::lean_closure_set(v___f_1721_, 3, v_inst_1701_);
            leanh::lean_closure_set(v___f_1721_, 4, v___f_1719_);
            leanh::lean_closure_set(v___f_1721_, 5, v_tail_1712_);
            leanh::lean_closure_set(v___f_1721_, 6, v_k_1702_);
            leanh::lean_closure_set(v___f_1721_, 7, v_fvars_1705_);
            leanh::lean_closure_set(v___f_1721_, 8, v_current_1720_);
            leanh::lean_closure_set(v___f_1721_, 9, v___x_1713_);
            leanh::lean_closure_set(v___f_1721_, 10, v_acc_1703_);
            leanh::lean_closure_set(v___f_1721_, 11, v_toBind_1710_);
            v___x_1722_ = leanh::lean_alloc_closure(
                l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
                6,
                1,
            );
            leanh::lean_closure_set(v___x_1722_, 0, v_current_1720_);
            v___x_1723_ =
                leanh::lean_apply_2(v_inst_1699_, leanh::lean_box(0), v___x_1722_);
            v___x_1724_ = leanh::lean_apply_4(
                v_toBind_1710_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1723_,
                v___f_1721_,
            );
            return v___x_1724_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0(
    mut v_inst_1725_: *mut leanh::LeanObject,
    mut v_inst_1726_: *mut leanh::LeanObject,
    mut v_inst_1727_: *mut leanh::LeanObject,
    mut v_inst_1728_: *mut leanh::LeanObject,
    mut v_k_1729_: *mut leanh::LeanObject,
    mut v_tail_1730_: *mut leanh::LeanObject,
    mut v_fvars_1731_: *mut leanh::LeanObject,
    mut v_head_1732_: *mut leanh::LeanObject,
    mut v_current_1733_: *mut leanh::LeanObject,
    mut v_acc_1734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1728_);
    leanh::lean_inc_ref(v_inst_1727_);
    leanh::lean_inc_ref(v_inst_1725_);
    v___x_1735_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg
            as *mut core::ffi::c_void,
        9,
        7,
    );
    leanh::lean_closure_set(v___x_1735_, 0, v_inst_1725_);
    leanh::lean_closure_set(v___x_1735_, 1, v_inst_1726_);
    leanh::lean_closure_set(v___x_1735_, 2, v_inst_1727_);
    leanh::lean_closure_set(v___x_1735_, 3, v_inst_1728_);
    leanh::lean_closure_set(v___x_1735_, 4, v_k_1729_);
    leanh::lean_closure_set(v___x_1735_, 5, v_acc_1734_);
    leanh::lean_closure_set(v___x_1735_, 6, v_tail_1730_);
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
    mut v_M_1737_: *mut leanh::LeanObject,
    mut v_inst_1738_: *mut leanh::LeanObject,
    mut v_inst_1739_: *mut leanh::LeanObject,
    mut v_inst_1740_: *mut leanh::LeanObject,
    mut v_inst_1741_: *mut leanh::LeanObject,
    mut v_00_u03b1_1742_: *mut leanh::LeanObject,
    mut v_k_1743_: *mut leanh::LeanObject,
    mut v_acc_1744_: *mut leanh::LeanObject,
    mut v_address_1745_: *mut leanh::LeanObject,
    mut v_fvars_1746_: *mut leanh::LeanObject,
    mut v_current_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1749_: *mut leanh::LeanObject,
    mut v_inst_1750_: *mut leanh::LeanObject,
    mut v_inst_1751_: *mut leanh::LeanObject,
    mut v_inst_1752_: *mut leanh::LeanObject,
    mut v_k_1753_: *mut leanh::LeanObject,
    mut v_init_1754_: *mut leanh::LeanObject,
    mut v_p_1755_: *mut leanh::LeanObject,
    mut v_e_1756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1761_: *mut leanh::LeanObject,
    mut v_inst_1762_: *mut leanh::LeanObject,
    mut v_inst_1763_: *mut leanh::LeanObject,
    mut v_inst_1764_: *mut leanh::LeanObject,
    mut v_k_1765_: *mut leanh::LeanObject,
    mut v_init_1766_: *mut leanh::LeanObject,
    mut v_p_1767_: *mut leanh::LeanObject,
    mut v_e_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_p_1767_);
    return v_res_1769_;
}
pub unsafe fn l_Lean_Meta_foldAncestors(
    mut v_M_1770_: *mut leanh::LeanObject,
    mut v_inst_1771_: *mut leanh::LeanObject,
    mut v_inst_1772_: *mut leanh::LeanObject,
    mut v_inst_1773_: *mut leanh::LeanObject,
    mut v_inst_1774_: *mut leanh::LeanObject,
    mut v_00_u03b1_1775_: *mut leanh::LeanObject,
    mut v_k_1776_: *mut leanh::LeanObject,
    mut v_init_1777_: *mut leanh::LeanObject,
    mut v_p_1778_: *mut leanh::LeanObject,
    mut v_e_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_1781_: *mut leanh::LeanObject,
    mut v_inst_1782_: *mut leanh::LeanObject,
    mut v_inst_1783_: *mut leanh::LeanObject,
    mut v_inst_1784_: *mut leanh::LeanObject,
    mut v_inst_1785_: *mut leanh::LeanObject,
    mut v_00_u03b1_1786_: *mut leanh::LeanObject,
    mut v_k_1787_: *mut leanh::LeanObject,
    mut v_init_1788_: *mut leanh::LeanObject,
    mut v_p_1789_: *mut leanh::LeanObject,
    mut v_e_1790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_p_1789_);
    return v_res_1791_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1793_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__0;
    v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
    return v___x_1794_;
}
pub unsafe fn _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__2;
    v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
    return v___x_1797_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(
    mut v_inst_1798_: *mut leanh::LeanObject,
    mut v_inst_1799_: *mut leanh::LeanObject,
    mut v_e_1800_: *mut leanh::LeanObject,
    mut v_n_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v_expr_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1815_ = leanh::lean_ctor_get(v_inst_1798_, 0);
                v_toPure_1816_ = leanh::lean_ctor_get(v_toApplicative_1815_, 1);
                v___x_1817_ = leanh::lean_unsigned_to_nat(3);
                v___x_1818_ = lean_nat_dec_eq(v_n_1801_, v___x_1817_);
                if v___x_1818_ == 0 {
                    v___x_1819_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1820_ = lean_nat_dec_eq(v_n_1801_, v___x_1819_);
                    if v___x_1820_ == 0 {
                        v___x_1821_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1822_ = lean_nat_dec_eq(v_n_1801_, v___x_1821_);
                        if v___x_1822_ == 0 {
                            v___x_1823_ = leanh::lean_unsigned_to_nat(2);
                            v___x_1824_ = lean_nat_dec_eq(v_n_1801_, v___x_1823_);
                            if v___x_1824_ == 0 {
                                if leanh::lean_obj_tag(v_e_1800_) == 10 {
                                    v_expr_1825_ = leanh::lean_ctor_get(v_e_1800_, 1);
                                    leanh::lean_inc_ref(v_expr_1825_);
                                    leanh::lean_dec_ref_known(v_e_1800_, 2);
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
                                leanh::lean_dec(v_n_1801_);
                                match leanh::lean_obj_tag(v_e_1800_) {
                                    8 => {
                                        leanh::lean_inc(v_toPure_1816_);
                                        leanh::lean_dec_ref(v_inst_1799_);
                                        leanh::lean_dec_ref(v_inst_1798_);
                                        v_body_1827_ = leanh::lean_ctor_get(v_e_1800_, 3);
                                        leanh::lean_inc_ref(v_body_1827_);
                                        leanh::lean_dec_ref_known(v_e_1800_, 4);
                                        v___x_1828_ = leanh::lean_apply_2(
                                            v_toPure_1816_,
                                            leanh::lean_box(0),
                                            v_body_1827_,
                                        );
                                        return v___x_1828_;
                                    }
                                    10 => {
                                        v_expr_1829_ = leanh::lean_ctor_get(v_e_1800_, 1);
                                        leanh::lean_inc_ref(v_expr_1829_);
                                        leanh::lean_dec_ref_known(v_e_1800_, 2);
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
                            leanh::lean_dec(v_n_1801_);
                            match leanh::lean_obj_tag(v_e_1800_) {
                                5 => {
                                    leanh::lean_inc(v_toPure_1816_);
                                    leanh::lean_dec_ref(v_inst_1799_);
                                    leanh::lean_dec_ref(v_inst_1798_);
                                    v_arg_1831_ = leanh::lean_ctor_get(v_e_1800_, 1);
                                    leanh::lean_inc_ref(v_arg_1831_);
                                    leanh::lean_dec_ref_known(v_e_1800_, 2);
                                    v___x_1832_ = leanh::lean_apply_2(
                                        v_toPure_1816_,
                                        leanh::lean_box(0),
                                        v_arg_1831_,
                                    );
                                    return v___x_1832_;
                                }
                                6 => {
                                    leanh::lean_inc(v_toPure_1816_);
                                    leanh::lean_dec_ref(v_inst_1799_);
                                    leanh::lean_dec_ref(v_inst_1798_);
                                    v_body_1833_ = leanh::lean_ctor_get(v_e_1800_, 2);
                                    leanh::lean_inc_ref(v_body_1833_);
                                    leanh::lean_dec_ref_known(v_e_1800_, 3);
                                    v___x_1834_ = leanh::lean_apply_2(
                                        v_toPure_1816_,
                                        leanh::lean_box(0),
                                        v_body_1833_,
                                    );
                                    return v___x_1834_;
                                }
                                7 => {
                                    leanh::lean_inc(v_toPure_1816_);
                                    leanh::lean_dec_ref(v_inst_1799_);
                                    leanh::lean_dec_ref(v_inst_1798_);
                                    v_body_1835_ = leanh::lean_ctor_get(v_e_1800_, 2);
                                    leanh::lean_inc_ref(v_body_1835_);
                                    leanh::lean_dec_ref_known(v_e_1800_, 3);
                                    v___x_1836_ = leanh::lean_apply_2(
                                        v_toPure_1816_,
                                        leanh::lean_box(0),
                                        v_body_1835_,
                                    );
                                    return v___x_1836_;
                                }
                                8 => {
                                    leanh::lean_inc(v_toPure_1816_);
                                    leanh::lean_dec_ref(v_inst_1799_);
                                    leanh::lean_dec_ref(v_inst_1798_);
                                    v_value_1837_ = leanh::lean_ctor_get(v_e_1800_, 2);
                                    leanh::lean_inc_ref(v_value_1837_);
                                    leanh::lean_dec_ref_known(v_e_1800_, 4);
                                    v___x_1838_ = leanh::lean_apply_2(
                                        v_toPure_1816_,
                                        leanh::lean_box(0),
                                        v_value_1837_,
                                    );
                                    return v___x_1838_;
                                }
                                10 => {
                                    v_expr_1839_ = leanh::lean_ctor_get(v_e_1800_, 1);
                                    leanh::lean_inc_ref(v_expr_1839_);
                                    leanh::lean_dec_ref_known(v_e_1800_, 2);
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
                        leanh::lean_dec(v_n_1801_);
                        match leanh::lean_obj_tag(v_e_1800_) {
                            5 => {
                                leanh::lean_inc(v_toPure_1816_);
                                leanh::lean_dec_ref(v_inst_1799_);
                                leanh::lean_dec_ref(v_inst_1798_);
                                v_fn_1841_ = leanh::lean_ctor_get(v_e_1800_, 0);
                                leanh::lean_inc_ref(v_fn_1841_);
                                leanh::lean_dec_ref_known(v_e_1800_, 2);
                                v___x_1842_ = leanh::lean_apply_2(
                                    v_toPure_1816_,
                                    leanh::lean_box(0),
                                    v_fn_1841_,
                                );
                                return v___x_1842_;
                            }
                            6 => {
                                leanh::lean_inc(v_toPure_1816_);
                                leanh::lean_dec_ref(v_inst_1799_);
                                leanh::lean_dec_ref(v_inst_1798_);
                                v_binderType_1843_ = leanh::lean_ctor_get(v_e_1800_, 1);
                                leanh::lean_inc_ref(v_binderType_1843_);
                                leanh::lean_dec_ref_known(v_e_1800_, 3);
                                v___x_1844_ = leanh::lean_apply_2(
                                    v_toPure_1816_,
                                    leanh::lean_box(0),
                                    v_binderType_1843_,
                                );
                                return v___x_1844_;
                            }
                            7 => {
                                leanh::lean_inc(v_toPure_1816_);
                                leanh::lean_dec_ref(v_inst_1799_);
                                leanh::lean_dec_ref(v_inst_1798_);
                                v_binderType_1845_ = leanh::lean_ctor_get(v_e_1800_, 1);
                                leanh::lean_inc_ref(v_binderType_1845_);
                                leanh::lean_dec_ref_known(v_e_1800_, 3);
                                v___x_1846_ = leanh::lean_apply_2(
                                    v_toPure_1816_,
                                    leanh::lean_box(0),
                                    v_binderType_1845_,
                                );
                                return v___x_1846_;
                            }
                            8 => {
                                leanh::lean_inc(v_toPure_1816_);
                                leanh::lean_dec_ref(v_inst_1799_);
                                leanh::lean_dec_ref(v_inst_1798_);
                                v_type_1847_ = leanh::lean_ctor_get(v_e_1800_, 1);
                                leanh::lean_inc_ref(v_type_1847_);
                                leanh::lean_dec_ref_known(v_e_1800_, 4);
                                v___x_1848_ = leanh::lean_apply_2(
                                    v_toPure_1816_,
                                    leanh::lean_box(0),
                                    v_type_1847_,
                                );
                                return v___x_1848_;
                            }
                            11 => {
                                leanh::lean_inc(v_toPure_1816_);
                                leanh::lean_dec_ref(v_inst_1799_);
                                leanh::lean_dec_ref(v_inst_1798_);
                                v_struct_1849_ = leanh::lean_ctor_get(v_e_1800_, 2);
                                leanh::lean_inc_ref(v_struct_1849_);
                                leanh::lean_dec_ref_known(v_e_1800_, 3);
                                v___x_1850_ = leanh::lean_apply_2(
                                    v_toPure_1816_,
                                    leanh::lean_box(0),
                                    v_struct_1849_,
                                );
                                return v___x_1850_;
                            }
                            10 => {
                                v_expr_1851_ = leanh::lean_ctor_get(v_e_1800_, 1);
                                leanh::lean_inc_ref(v_expr_1851_);
                                leanh::lean_dec_ref_known(v_e_1800_, 2);
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
                    leanh::lean_dec(v_n_1801_);
                    v___x_1853_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__3);
                    v___x_1854_ = l_Lean_MessageData_ofExpr(v_e_1800_);
                    v___x_1855_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1855_, 0, v___x_1853_);
                    leanh::lean_ctor_set(v___x_1855_, 1, v___x_1854_);
                    v___x_1856_ =
                        l_Lean_throwError___redArg(v_inst_1798_, v_inst_1799_, v___x_1855_);
                    return v___x_1856_;
                }
            }
            1 => {
                v___x_1805_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___closed__1);
                v___x_1806_ = l_Nat_reprFast(v_c_1804_);
                v___x_1807_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1807_, 0, v___x_1806_);
                v___x_1808_ = l_Lean_MessageData_ofFormat(v___x_1807_);
                v___x_1809_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1809_, 0, v___x_1805_);
                leanh::lean_ctor_set(v___x_1809_, 1, v___x_1808_);
                v___x_1810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3_once), _init_l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___closed__3);
                v___x_1811_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1811_, 0, v___x_1809_);
                leanh::lean_ctor_set(v___x_1811_, 1, v___x_1810_);
                v___x_1812_ = l_Lean_MessageData_ofExpr(v_e_1803_);
                v___x_1813_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1813_, 0, v___x_1811_);
                leanh::lean_ctor_set(v___x_1813_, 1, v___x_1812_);
                v___x_1814_ = l_Lean_throwError___redArg(v_inst_1798_, v_inst_1799_, v___x_1813_);
                return v___x_1814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw(
    mut v_M_1857_: *mut leanh::LeanObject,
    mut v_inst_1858_: *mut leanh::LeanObject,
    mut v_inst_1859_: *mut leanh::LeanObject,
    mut v_e_1860_: *mut leanh::LeanObject,
    mut v_n_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(
        v_inst_1858_,
        v_inst_1859_,
        v_e_1860_,
        v_n_1861_,
    );
    return v___x_1862_;
}
pub unsafe fn l_Lean_Core_viewSubexpr___redArg(
    mut v_inst_1863_: *mut leanh::LeanObject,
    mut v_inst_1864_: *mut leanh::LeanObject,
    mut v_p_1865_: *mut leanh::LeanObject,
    mut v_root_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1863_);
    v___x_1867_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_1867_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1867_, 1, v_inst_1863_);
    leanh::lean_closure_set(v___x_1867_, 2, v_inst_1864_);
    v___x_1868_ =
        l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_1863_, v___x_1867_, v_root_1866_, v_p_1865_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_Core_viewSubexpr(
    mut v_M_1869_: *mut leanh::LeanObject,
    mut v_inst_1870_: *mut leanh::LeanObject,
    mut v_inst_1871_: *mut leanh::LeanObject,
    mut v_p_1872_: *mut leanh::LeanObject,
    mut v_root_1873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ =
        l_Lean_Core_viewSubexpr___redArg(v_inst_1870_, v_inst_1871_, v_p_1872_, v_root_1873_);
    return v___x_1874_;
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(
    mut v_x_1875_: *mut leanh::LeanObject,
    mut v_x_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1882_ = leanh::lean_unsigned_to_nat(1);
                v___x_1883_ = lean_nat_dec_eq(v_x_1875_, v___x_1882_);
                if v___x_1883_ == 0 {
                    v___x_1884_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1885_ = lean_nat_dec_eq(v_x_1875_, v___x_1884_);
                    if v___x_1885_ == 0 {
                        leanh::lean_dec_ref(v_x_1876_);
                        v___x_1886_ = leanh::lean_box(0);
                        return v___x_1886_;
                    } else {
                        if leanh::lean_obj_tag(v_x_1876_) == 8 {
                            v_declName_1887_ = leanh::lean_ctor_get(v_x_1876_, 0);
                            leanh::lean_inc(v_declName_1887_);
                            v_type_1888_ = leanh::lean_ctor_get(v_x_1876_, 1);
                            leanh::lean_inc_ref(v_type_1888_);
                            leanh::lean_dec_ref_known(v_x_1876_, 4);
                            v___x_1889_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1889_, 0, v_declName_1887_);
                            leanh::lean_ctor_set(v___x_1889_, 1, v_type_1888_);
                            v___x_1890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1890_, 0, v___x_1889_);
                            return v___x_1890_;
                        } else {
                            leanh::lean_dec_ref(v_x_1876_);
                            v___x_1891_ = leanh::lean_box(0);
                            return v___x_1891_;
                        }
                    }
                } else {
                    match leanh::lean_obj_tag(v_x_1876_) {
                        6 => {
                            v_binderName_1892_ = leanh::lean_ctor_get(v_x_1876_, 0);
                            leanh::lean_inc(v_binderName_1892_);
                            v_binderType_1893_ = leanh::lean_ctor_get(v_x_1876_, 1);
                            leanh::lean_inc_ref(v_binderType_1893_);
                            leanh::lean_dec_ref_known(v_x_1876_, 3);
                            v_n_1878_ = v_binderName_1892_;
                            v_y_1879_ = v_binderType_1893_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_binderName_1894_ = leanh::lean_ctor_get(v_x_1876_, 0);
                            leanh::lean_inc(v_binderName_1894_);
                            v_binderType_1895_ = leanh::lean_ctor_get(v_x_1876_, 1);
                            leanh::lean_inc_ref(v_binderType_1895_);
                            leanh::lean_dec_ref_known(v_x_1876_, 3);
                            v_n_1878_ = v_binderName_1894_;
                            v_y_1879_ = v_binderType_1895_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_x_1876_);
                            v___x_1896_ = leanh::lean_box(0);
                            return v___x_1896_;
                        }
                    }
                }
            }
            1 => {
                v___x_1880_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1880_, 0, v_n_1878_);
                leanh::lean_ctor_set(v___x_1880_, 1, v_y_1879_);
                v___x_1881_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1881_, 0, v___x_1880_);
                return v___x_1881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___boxed(
    mut v_x_1897_: *mut leanh::LeanObject,
    mut v_x_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ =
        l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(v_x_1897_, v_x_1898_);
    leanh::lean_dec(v_x_1897_);
    return v_res_1899_;
}
pub unsafe fn l_Lean_Core_viewBinders___redArg___lam__0(
    mut v_toPure_1900_: *mut leanh::LeanObject,
    mut v_c_1901_: *mut leanh::LeanObject,
    mut v_snd_1902_: *mut leanh::LeanObject,
    mut v_fst_1903_: *mut leanh::LeanObject,
    mut v_e_u2082_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1909_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(
                    v_c_1901_,
                    v_snd_1902_,
                );
                if leanh::lean_obj_tag(v___x_1909_) == 0 {
                    v___y_1906_ = v_fst_1903_;
                    state = 1;
                    continue;
                } else {
                    v_val_1910_ = leanh::lean_ctor_get(v___x_1909_, 0);
                    leanh::lean_inc(v_val_1910_);
                    leanh::lean_dec_ref_known(v___x_1909_, 1);
                    v___x_1911_ = lean_array_push(v_fst_1903_, v_val_1910_);
                    v___y_1906_ = v___x_1911_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1907_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1907_, 0, v___y_1906_);
                leanh::lean_ctor_set(v___x_1907_, 1, v_e_u2082_1904_);
                v___x_1908_ = leanh::lean_apply_2(
                    v_toPure_1900_,
                    leanh::lean_box(0),
                    v___x_1907_,
                );
                return v___x_1908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_viewBinders___redArg___lam__0___boxed(
    mut v_toPure_1912_: *mut leanh::LeanObject,
    mut v_c_1913_: *mut leanh::LeanObject,
    mut v_snd_1914_: *mut leanh::LeanObject,
    mut v_fst_1915_: *mut leanh::LeanObject,
    mut v_e_u2082_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1917_ = l_Lean_Core_viewBinders___redArg___lam__0(
        v_toPure_1912_,
        v_c_1913_,
        v_snd_1914_,
        v_fst_1915_,
        v_e_u2082_1916_,
    );
    leanh::lean_dec(v_c_1913_);
    return v_res_1917_;
}
pub unsafe fn l_Lean_Core_viewBinders___redArg___lam__1(
    mut v_toPure_1918_: *mut leanh::LeanObject,
    mut v_inst_1919_: *mut leanh::LeanObject,
    mut v_inst_1920_: *mut leanh::LeanObject,
    mut v_toBind_1921_: *mut leanh::LeanObject,
    mut v_x_1922_: *mut leanh::LeanObject,
    mut v_c_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1924_ = leanh::lean_ctor_get(v_x_1922_, 0);
    leanh::lean_inc(v_fst_1924_);
    v_snd_1925_ = leanh::lean_ctor_get(v_x_1922_, 1);
    leanh::lean_inc_n(v_snd_1925_, 2);
    leanh::lean_dec_ref(v_x_1922_);
    leanh::lean_inc(v_c_1923_);
    v___f_1926_ = leanh::lean_alloc_closure(
        l_Lean_Core_viewBinders___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1926_, 0, v_toPure_1918_);
    leanh::lean_closure_set(v___f_1926_, 1, v_c_1923_);
    leanh::lean_closure_set(v___f_1926_, 2, v_snd_1925_);
    leanh::lean_closure_set(v___f_1926_, 3, v_fst_1924_);
    v___x_1927_ = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(
        v_inst_1919_,
        v_inst_1920_,
        v_snd_1925_,
        v_c_1923_,
    );
    v___x_1928_ = leanh::lean_apply_4(
        v_toBind_1921_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1927_,
        v___f_1926_,
    );
    return v___x_1928_;
}
pub unsafe fn l_Lean_Core_viewBinders___redArg___lam__2(
    mut v_toPure_1929_: *mut leanh::LeanObject,
    mut v_____x_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1931_ = leanh::lean_ctor_get(v_____x_1930_, 0);
    leanh::lean_inc(v_fst_1931_);
    leanh::lean_dec_ref(v_____x_1930_);
    v___x_1932_ =
        leanh::lean_apply_2(v_toPure_1929_, leanh::lean_box(0), v_fst_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Lean_Core_viewBinders___redArg(
    mut v_inst_1935_: *mut leanh::LeanObject,
    mut v_inst_1936_: *mut leanh::LeanObject,
    mut v_p_1937_: *mut leanh::LeanObject,
    mut v_root_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1939_ = leanh::lean_ctor_get(v_inst_1935_, 0);
    v_toBind_1940_ = leanh::lean_ctor_get(v_inst_1935_, 1);
    leanh::lean_inc_n(v_toBind_1940_, 2);
    v_toPure_1941_ = leanh::lean_ctor_get(v_toApplicative_1939_, 1);
    leanh::lean_inc_ref(v_inst_1935_);
    leanh::lean_inc_n(v_toPure_1941_, 2);
    v___f_1942_ = leanh::lean_alloc_closure(
        l_Lean_Core_viewBinders___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___f_1942_, 0, v_toPure_1941_);
    leanh::lean_closure_set(v___f_1942_, 1, v_inst_1935_);
    leanh::lean_closure_set(v___f_1942_, 2, v_inst_1936_);
    leanh::lean_closure_set(v___f_1942_, 3, v_toBind_1940_);
    v___f_1943_ = leanh::lean_alloc_closure(
        l_Lean_Core_viewBinders___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1943_, 0, v_toPure_1941_);
    v___x_1944_ = l_Lean_Core_viewBinders___redArg___closed__0;
    v___x_1945_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1945_, 0, v___x_1944_);
    leanh::lean_ctor_set(v___x_1945_, 1, v_root_1938_);
    v___x_1946_ =
        l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_1935_, v___f_1942_, v___x_1945_, v_p_1937_);
    v___x_1947_ = leanh::lean_apply_4(
        v_toBind_1940_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1946_,
        v___f_1943_,
    );
    return v___x_1947_;
}
pub unsafe fn l_Lean_Core_viewBinders(
    mut v_M_1948_: *mut leanh::LeanObject,
    mut v_inst_1949_: *mut leanh::LeanObject,
    mut v_inst_1950_: *mut leanh::LeanObject,
    mut v_p_1951_: *mut leanh::LeanObject,
    mut v_root_1952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1953_ =
        l_Lean_Core_viewBinders___redArg(v_inst_1949_, v_inst_1950_, v_p_1951_, v_root_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_Core_numBinders___redArg(
    mut v_inst_1955_: *mut leanh::LeanObject,
    mut v_inst_1956_: *mut leanh::LeanObject,
    mut v_p_1957_: *mut leanh::LeanObject,
    mut v_e_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1959_ = leanh::lean_ctor_get(v_inst_1955_, 0);
    v_toFunctor_1960_ = leanh::lean_ctor_get(v_toApplicative_1959_, 0);
    v_map_1961_ = leanh::lean_ctor_get(v_toFunctor_1960_, 0);
    leanh::lean_inc(v_map_1961_);
    v___x_1962_ = l_Lean_Core_numBinders___redArg___closed__0;
    v___x_1963_ =
        l_Lean_Core_viewBinders___redArg(v_inst_1955_, v_inst_1956_, v_p_1957_, v_e_1958_);
    v___x_1964_ = leanh::lean_apply_4(
        v_map_1961_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1962_,
        v___x_1963_,
    );
    return v___x_1964_;
}
pub unsafe fn l_Lean_Core_numBinders(
    mut v_M_1965_: *mut leanh::LeanObject,
    mut v_inst_1966_: *mut leanh::LeanObject,
    mut v_inst_1967_: *mut leanh::LeanObject,
    mut v_p_1968_: *mut leanh::LeanObject,
    mut v_e_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_Lean_Core_numBinders___redArg(v_inst_1966_, v_inst_1967_, v_p_1968_, v_e_1969_);
    return v___x_1970_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ExprLens(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_SubExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ExprLens(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ExprLens(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_SubExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ExprLens(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ExprLens(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_ExprLens(builtin);
}