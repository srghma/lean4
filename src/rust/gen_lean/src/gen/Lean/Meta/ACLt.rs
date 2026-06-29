// Lean compiler output
// Module: Lean.Meta.ACLt
// Imports: Lean.Meta.DiscrTree.Main Init.Data.Range.Polymorphic.Iterators Lean.Meta.FunInfo
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_set,
    lean_expr_eqv, lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint8_dec_lt,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_lt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_bindingBody_x21,
    l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_bvarIdx_x21, l_Lean_Expr_constName_x21,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isMData, l_Lean_Expr_letBody_x21,
    l_Lean_Expr_letValue_x21, l_Lean_Expr_litValue_x21, l_Lean_Expr_mdataExpr_x21,
    l_Lean_Expr_mvarId_x21, l_Lean_Expr_projExpr_x21, l_Lean_Expr_projIdx_x21,
    l_Lean_Expr_sort___override, l_Lean_Expr_sortLevel_x21, l_Lean_Literal_lt,
    l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Level::l_Lean_Level_normLt;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_index, l_Lean_instInhabitedLocalDecl_default,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey, l_Lean_FVarId_findDecl_x3f___redArg,
    l_Lean_Meta_Config_toConfigWithKey, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_instInhabitedParamInfo_default,
};
use crate::r#gen::Lean::Meta::DiscrTree::Main::{
    initialize_Lean_Meta_DiscrTree_Main, l_Lean_Meta_DiscrTree_reduce,
    runtime_initialize_Lean_Meta_DiscrTree_Main,
};
use crate::r#gen::Lean::Meta::FunInfo::{
    initialize_Lean_Meta_FunInfo, l_Lean_Meta_getFunInfoNArgs, runtime_initialize_Lean_Meta_FunInfo,
};
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut crate::leanh::LeanObject,
        72058693566333441 as *mut crate::leanh::LeanObject,
        65793 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0_value:
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
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 97, 99, 76, 116, 0,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5_value:
    crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65,
        67, 76, 116, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 67, 76, 116, 46,
        109, 97, 105, 110, 46, 108, 101, 120, 83, 97, 109, 101, 67, 116, 111, 114, 0,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 67, 76, 116, 0,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Expr_ctorWeight(mut v_x_1194_: *mut crate::leanh::LeanObject) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_1194_) {
        0 => {
            let mut v___x_1195_: u8 = 0;
            v___x_1195_ = 0;
            return v___x_1195_;
        }
        1 => {
            let mut v___x_1196_: u8 = 0;
            v___x_1196_ = 1;
            return v___x_1196_;
        }
        2 => {
            let mut v___x_1197_: u8 = 0;
            v___x_1197_ = 2;
            return v___x_1197_;
        }
        3 => {
            let mut v___x_1198_: u8 = 0;
            v___x_1198_ = 3;
            return v___x_1198_;
        }
        4 => {
            let mut v___x_1199_: u8 = 0;
            v___x_1199_ = 4;
            return v___x_1199_;
        }
        5 => {
            let mut v___x_1200_: u8 = 0;
            v___x_1200_ = 8;
            return v___x_1200_;
        }
        6 => {
            let mut v___x_1201_: u8 = 0;
            v___x_1201_ = 9;
            return v___x_1201_;
        }
        7 => {
            let mut v___x_1202_: u8 = 0;
            v___x_1202_ = 10;
            return v___x_1202_;
        }
        8 => {
            let mut v___x_1203_: u8 = 0;
            v___x_1203_ = 11;
            return v___x_1203_;
        }
        9 => {
            let mut v___x_1204_: u8 = 0;
            v___x_1204_ = 5;
            return v___x_1204_;
        }
        10 => {
            let mut v___x_1205_: u8 = 0;
            v___x_1205_ = 6;
            return v___x_1205_;
        }
        _ => {
            let mut v___x_1206_: u8 = 0;
            v___x_1206_ = 7;
            return v___x_1206_;
        }
    }
}
pub unsafe fn l_Lean_Expr_ctorWeight___boxed(
    mut v_x_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1208_: u8 = 0;
    let mut v_r_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1208_ = l_Lean_Expr_ctorWeight(v_x_1207_);
    crate::leanh::lean_dec_ref(v_x_1207_);
    v_r_1209_ = crate::leanh::lean_box((v_res_1208_) as usize);
    return v_r_1209_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorIdx(
    mut v_x_1210_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1210_ {
        0 => {
            let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1211_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1211_;
        }
        1 => {
            let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1212_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1212_;
        }
        _ => {
            let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1213_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1213_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorIdx___boxed(
    mut v_x_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1215_: u8 = 0;
    let mut v_res_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1215_ = (crate::leanh::lean_unbox(v_x_1214_) as u8);
    v_res_1216_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx(v_x_boxed_1215_);
    return v_res_1216_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(
    mut v_x_1217_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1218_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx(v_x_1217_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_toCtorIdx___boxed(
    mut v_x_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1220_: u8 = 0;
    let mut v_res_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1220_ = (crate::leanh::lean_unbox(v_x_1219_) as u8);
    v_res_1221_ = l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(v_x_4__boxed_1220_);
    return v_res_1221_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(
    mut v_k_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1222_);
    return v_k_1222_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg___boxed(
    mut v_k_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(v_k_1223_);
    crate::leanh::lean_dec(v_k_1223_);
    return v_res_1224_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim(
    mut v_motive_1225_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1226_: *mut crate::leanh::LeanObject,
    mut v_t_1227_: u8,
    mut v_h_1228_: *mut crate::leanh::LeanObject,
    mut v_k_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1229_);
    return v_k_1229_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___boxed(
    mut v_motive_1230_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1231_: *mut crate::leanh::LeanObject,
    mut v_t_1232_: *mut crate::leanh::LeanObject,
    mut v_h_1233_: *mut crate::leanh::LeanObject,
    mut v_k_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1235_: u8 = 0;
    let mut v_res_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1235_ = (crate::leanh::lean_unbox(v_t_1232_) as u8);
    v_res_1236_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim(
        v_motive_1230_,
        v_ctorIdx_1231_,
        v_t_boxed_1235_,
        v_h_1233_,
        v_k_1234_,
    );
    crate::leanh::lean_dec(v_k_1234_);
    crate::leanh::lean_dec(v_ctorIdx_1231_);
    return v_res_1236_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(
    mut v_reduce_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_reduce_1237_);
    return v_reduce_1237_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg___boxed(
    mut v_reduce_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(v_reduce_1238_);
    crate::leanh::lean_dec(v_reduce_1238_);
    return v_res_1239_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim(
    mut v_motive_1240_: *mut crate::leanh::LeanObject,
    mut v_t_1241_: u8,
    mut v_h_1242_: *mut crate::leanh::LeanObject,
    mut v_reduce_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_reduce_1243_);
    return v_reduce_1243_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___boxed(
    mut v_motive_1244_: *mut crate::leanh::LeanObject,
    mut v_t_1245_: *mut crate::leanh::LeanObject,
    mut v_h_1246_: *mut crate::leanh::LeanObject,
    mut v_reduce_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1248_: u8 = 0;
    let mut v_res_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1248_ = (crate::leanh::lean_unbox(v_t_1245_) as u8);
    v_res_1249_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim(
        v_motive_1244_,
        v_t_boxed_1248_,
        v_h_1246_,
        v_reduce_1247_,
    );
    crate::leanh::lean_dec(v_reduce_1247_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(
    mut v_reduceSimpleOnly_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_reduceSimpleOnly_1250_);
    return v_reduceSimpleOnly_1250_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg___boxed(
    mut v_reduceSimpleOnly_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1252_ =
        l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(v_reduceSimpleOnly_1251_);
    crate::leanh::lean_dec(v_reduceSimpleOnly_1251_);
    return v_res_1252_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(
    mut v_motive_1253_: *mut crate::leanh::LeanObject,
    mut v_t_1254_: u8,
    mut v_h_1255_: *mut crate::leanh::LeanObject,
    mut v_reduceSimpleOnly_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_reduceSimpleOnly_1256_);
    return v_reduceSimpleOnly_1256_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___boxed(
    mut v_motive_1257_: *mut crate::leanh::LeanObject,
    mut v_t_1258_: *mut crate::leanh::LeanObject,
    mut v_h_1259_: *mut crate::leanh::LeanObject,
    mut v_reduceSimpleOnly_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1261_: u8 = 0;
    let mut v_res_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1261_ = (crate::leanh::lean_unbox(v_t_1258_) as u8);
    v_res_1262_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(
        v_motive_1257_,
        v_t_boxed_1261_,
        v_h_1259_,
        v_reduceSimpleOnly_1260_,
    );
    crate::leanh::lean_dec(v_reduceSimpleOnly_1260_);
    return v_res_1262_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(
    mut v_none_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_1263_);
    return v_none_1263_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg___boxed(
    mut v_none_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(v_none_1264_);
    crate::leanh::lean_dec(v_none_1264_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim(
    mut v_motive_1266_: *mut crate::leanh::LeanObject,
    mut v_t_1267_: u8,
    mut v_h_1268_: *mut crate::leanh::LeanObject,
    mut v_none_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_1269_);
    return v_none_1269_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___boxed(
    mut v_motive_1270_: *mut crate::leanh::LeanObject,
    mut v_t_1271_: *mut crate::leanh::LeanObject,
    mut v_h_1272_: *mut crate::leanh::LeanObject,
    mut v_none_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1274_: u8 = 0;
    let mut v_res_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1274_ = (crate::leanh::lean_unbox(v_t_1271_) as u8);
    v_res_1275_ = l_Lean_Meta_ACLt_ReduceMode_none_elim(
        v_motive_1270_,
        v_t_boxed_1274_,
        v_h_1272_,
        v_none_1273_,
    );
    crate::leanh::lean_dec(v_none_1273_);
    return v_res_1275_;
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0;
    v___x_1283_ = l_Lean_Meta_Config_toConfigWithKey(v___x_1282_);
    return v___x_1283_;
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1_once
        ),
        _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1,
    );
    return v___x_1284_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(
    mut v_mode_1285_: u8,
    mut v_e_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_a_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1292_: u8 = 0;
    v___x_1292_ = l_Lean_Expr_hasLooseBVars(v_e_1286_);
    if v___x_1292_ == 0 {
        match v_mode_1285_ {
            0 => {
                let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1293_ = l_Lean_Meta_DiscrTree_reduce(
                    v_e_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_,
                );
                return v___x_1293_;
            }
            1 => {
                let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_config_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_trackZetaDelta_1296_: u8 = 0;
                let mut v_zetaDeltaSet_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_lctx_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_localInstances_1299_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_defEqCtx_x3f_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_synthPendingDepth_1301_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_canUnfold_x3f_1302_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_univApprox_1303_: u8 = 0;
                let mut v_inTypeClassResolution_1304_: u8 = 0;
                let mut v_cacheInferType_1305_: u8 = 0;
                let mut v___x_1306_: u64 = 0;
                let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1294_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
                v_config_1295_ = crate::leanh::lean_ctor_get(v___x_1294_, 0);
                v_trackZetaDelta_1296_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1297_ = crate::leanh::lean_ctor_get(v_a_1287_, 1);
                v_lctx_1298_ = crate::leanh::lean_ctor_get(v_a_1287_, 2);
                v_localInstances_1299_ = crate::leanh::lean_ctor_get(v_a_1287_, 3);
                v_defEqCtx_x3f_1300_ = crate::leanh::lean_ctor_get(v_a_1287_, 4);
                v_synthPendingDepth_1301_ = crate::leanh::lean_ctor_get(v_a_1287_, 5);
                v_canUnfold_x3f_1302_ = crate::leanh::lean_ctor_get(v_a_1287_, 6);
                v_univApprox_1303_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1304_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1305_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1306_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1295_);
                crate::leanh::lean_inc_ref(v_config_1295_);
                v___x_1307_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1307_, 0, v_config_1295_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1307_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1306_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1302_);
                crate::leanh::lean_inc(v_synthPendingDepth_1301_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1300_);
                crate::leanh::lean_inc_ref(v_localInstances_1299_);
                crate::leanh::lean_inc_ref(v_lctx_1298_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1297_);
                v___x_1308_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1308_, 0, v___x_1307_);
                crate::leanh::lean_ctor_set(v___x_1308_, 1, v_zetaDeltaSet_1297_);
                crate::leanh::lean_ctor_set(v___x_1308_, 2, v_lctx_1298_);
                crate::leanh::lean_ctor_set(v___x_1308_, 3, v_localInstances_1299_);
                crate::leanh::lean_ctor_set(v___x_1308_, 4, v_defEqCtx_x3f_1300_);
                crate::leanh::lean_ctor_set(v___x_1308_, 5, v_synthPendingDepth_1301_);
                crate::leanh::lean_ctor_set(v___x_1308_, 6, v_canUnfold_x3f_1302_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1296_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1303_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1304_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1305_,
                );
                v___x_1309_ = l_Lean_Meta_DiscrTree_reduce(
                    v_e_1286_,
                    v___x_1308_,
                    v_a_1288_,
                    v_a_1289_,
                    v_a_1290_,
                );
                crate::leanh::lean_dec_ref_known(v___x_1308_, 7);
                return v___x_1309_;
            }
            _ => {
                let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1310_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1310_, 0, v_e_1286_);
                return v___x_1310_;
            }
        }
    } else {
        let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1311_, 0, v_e_1286_);
        return v___x_1311_;
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(
    mut v_mode_1312_: *mut crate::leanh::LeanObject,
    mut v_e_1313_: *mut crate::leanh::LeanObject,
    mut v_a_1314_: *mut crate::leanh::LeanObject,
    mut v_a_1315_: *mut crate::leanh::LeanObject,
    mut v_a_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
    mut v_a_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_1319_: u8 = 0;
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_1319_ = (crate::leanh::lean_unbox(v_mode_1312_) as u8);
    v_res_1320_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(
        v_mode_boxed_1319_,
        v_e_1313_,
        v_a_1314_,
        v_a_1315_,
        v_a_1316_,
        v_a_1317_,
    );
    crate::leanh::lean_dec(v_a_1317_);
    crate::leanh::lean_dec_ref(v_a_1316_);
    crate::leanh::lean_dec(v_a_1315_);
    crate::leanh::lean_dec_ref(v_a_1314_);
    return v_res_1320_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
    mut v_f_1323_: *mut crate::leanh::LeanObject,
    mut v_numArgs_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
    mut v_a_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1335_: u8 = 0;
    let mut v_paramInfo_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut v_a_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1330_ = l_Lean_Expr_hasLooseBVars(v_f_1323_);
                if v___x_1330_ == 0 {
                    v___x_1331_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_1323_,
                        v_numArgs_1324_,
                        v_a_1325_,
                        v_a_1326_,
                        v_a_1327_,
                        v_a_1328_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1331_) == 0 {
                        v_a_1332_ = crate::leanh::lean_ctor_get(v___x_1331_, 0);
                        v_isSharedCheck_1340_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1331_)) as u8;
                        if v_isSharedCheck_1340_ == 0 {
                            v___x_1334_ = v___x_1331_;
                            v_isShared_1335_ = v_isSharedCheck_1340_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1332_);
                            crate::leanh::lean_dec(v___x_1331_);
                            v___x_1334_ = crate::leanh::lean_box(0);
                            v_isShared_1335_ = v_isSharedCheck_1340_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1341_ = crate::leanh::lean_ctor_get(v___x_1331_, 0);
                        v_isSharedCheck_1348_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1331_)) as u8;
                        if v_isSharedCheck_1348_ == 0 {
                            v___x_1343_ = v___x_1331_;
                            v_isShared_1344_ = v_isSharedCheck_1348_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1341_);
                            crate::leanh::lean_dec(v___x_1331_);
                            v___x_1343_ = crate::leanh::lean_box(0);
                            v_isShared_1344_ = v_isSharedCheck_1348_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_numArgs_1324_);
                    crate::leanh::lean_dec_ref(v_f_1323_);
                    v___x_1349_ =
                        l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0;
                    v___x_1350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1350_, 0, v___x_1349_);
                    return v___x_1350_;
                }
            }
            1 => {
                v_paramInfo_1336_ = crate::leanh::lean_ctor_get(v_a_1332_, 0);
                crate::leanh::lean_inc_ref(v_paramInfo_1336_);
                crate::leanh::lean_dec(v_a_1332_);
                if v_isShared_1335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1334_, 0, v_paramInfo_1336_);
                    v___x_1338_ = v___x_1334_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_paramInfo_1336_);
                    v___x_1338_ = v_reuseFailAlloc_1339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1338_;
            }
            3 => {
                if v_isShared_1344_ == 0 {
                    v___x_1346_ = v___x_1343_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
                    v___x_1346_ = v_reuseFailAlloc_1347_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___boxed(
    mut v_f_1351_: *mut crate::leanh::LeanObject,
    mut v_numArgs_1352_: *mut crate::leanh::LeanObject,
    mut v_a_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
    mut v_a_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
        v_f_1351_,
        v_numArgs_1352_,
        v_a_1353_,
        v_a_1354_,
        v_a_1355_,
        v_a_1356_,
    );
    crate::leanh::lean_dec(v_a_1356_);
    crate::leanh::lean_dec_ref(v_a_1355_);
    crate::leanh::lean_dec(v_a_1354_);
    crate::leanh::lean_dec_ref(v_a_1353_);
    return v_res_1358_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(
    mut v_msg_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_16292__overap_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1366_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0;
    v___x_16292__overap_1367_ = lean_panic_fn_borrowed(v___f_1366_, v_msg_1360_);
    crate::leanh::lean_inc(v___y_1364_);
    crate::leanh::lean_inc_ref(v___y_1363_);
    crate::leanh::lean_inc(v___y_1362_);
    crate::leanh::lean_inc_ref(v___y_1361_);
    v___x_1368_ = crate::leanh::lean_apply_5(
        v___x_16292__overap_1367_,
        v___y_1361_,
        v___y_1362_,
        v___y_1363_,
        v___y_1364_,
        crate::leanh::lean_box(0),
    );
    return v___x_1368_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(
    mut v_msg_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ =
        l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(
            v_msg_1369_,
            v___y_1370_,
            v___y_1371_,
            v___y_1372_,
            v___y_1373_,
        );
    crate::leanh::lean_dec(v___y_1373_);
    crate::leanh::lean_dec_ref(v___y_1372_);
    crate::leanh::lean_dec(v___y_1371_);
    crate::leanh::lean_dec_ref(v___y_1370_);
    return v_res_1375_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(
    mut v_msg_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lean_instInhabitedLocalDecl_default;
    v___x_1378_ = lean_panic_fn_borrowed(v___x_1377_, v_msg_1376_);
    return v___x_1378_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(
    mut v_mode_1380_: u8,
    mut v_a_u2081_1381_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_1382_: *mut crate::leanh::LeanObject,
    mut v_b_u2081_1383_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_b_u2081_1383_);
                crate::leanh::lean_inc_ref(v_a_u2081_1381_);
                v___x_1390_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_1380_,
                    v_a_u2081_1381_,
                    v_b_u2081_1383_,
                    v_a_1385_,
                    v_a_1386_,
                    v_a_1387_,
                    v_a_1388_,
                );
                if crate::leanh::lean_obj_tag(v___x_1390_) == 0 {
                    v_a_1391_ = crate::leanh::lean_ctor_get(v___x_1390_, 0);
                    crate::leanh::lean_inc(v_a_1391_);
                    v___x_1392_ = (crate::leanh::lean_unbox(v_a_1391_) as u8);
                    if v___x_1392_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1390_, 1);
                        v___x_1393_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1380_,
                            v_b_u2081_1383_,
                            v_a_u2081_1381_,
                            v_a_1385_,
                            v_a_1386_,
                            v_a_1387_,
                            v_a_1388_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1393_) == 0 {
                            v_a_1394_ = crate::leanh::lean_ctor_get(v___x_1393_, 0);
                            v_isSharedCheck_1403_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1393_)) as u8;
                            if v_isSharedCheck_1403_ == 0 {
                                v___x_1396_ = v___x_1393_;
                                v_isShared_1397_ = v_isSharedCheck_1403_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1394_);
                                crate::leanh::lean_dec(v___x_1393_);
                                v___x_1396_ = crate::leanh::lean_box(0);
                                v_isShared_1397_ = v_isSharedCheck_1403_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1391_);
                            crate::leanh::lean_dec_ref(v_b_u2082_1384_);
                            crate::leanh::lean_dec_ref(v_a_u2082_1382_);
                            return v___x_1393_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1391_);
                        crate::leanh::lean_dec_ref(v_b_u2082_1384_);
                        crate::leanh::lean_dec_ref(v_b_u2081_1383_);
                        crate::leanh::lean_dec_ref(v_a_u2082_1382_);
                        crate::leanh::lean_dec_ref(v_a_u2081_1381_);
                        return v___x_1390_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_u2082_1384_);
                    crate::leanh::lean_dec_ref(v_b_u2081_1383_);
                    crate::leanh::lean_dec_ref(v_a_u2082_1382_);
                    crate::leanh::lean_dec_ref(v_a_u2081_1381_);
                    return v___x_1390_;
                }
            }
            1 => {
                v___x_1398_ = (crate::leanh::lean_unbox(v_a_1394_) as u8);
                crate::leanh::lean_dec(v_a_1394_);
                if v___x_1398_ == 0 {
                    crate::leanh::lean_del_object(v___x_1396_);
                    crate::leanh::lean_dec(v_a_1391_);
                    v___x_1399_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1380_,
                        v_a_u2082_1382_,
                        v_b_u2082_1384_,
                        v_a_1385_,
                        v_a_1386_,
                        v_a_1387_,
                        v_a_1388_,
                    );
                    return v___x_1399_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_u2082_1384_);
                    crate::leanh::lean_dec_ref(v_a_u2082_1382_);
                    if v_isShared_1397_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1396_, 0, v_a_1391_);
                        v___x_1401_ = v___x_1396_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1391_);
                        v___x_1401_ = v_reuseFailAlloc_1402_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2;
    v___x_1408_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_1409_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_1410_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1;
    v___x_1411_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0;
    v___x_1412_ = l_mkPanicMessageWithDecl(
        v___x_1411_,
        v___x_1410_,
        v___x_1409_,
        v___x_1408_,
        v___x_1407_,
    );
    return v___x_1412_;
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = crate::leanh::lean_box(0);
    v_dummy_1414_ = l_Lean_Expr_sort___override(v___x_1413_);
    return v_dummy_1414_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(
    mut v_upperBound_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v___x_1420_: *mut crate::leanh::LeanObject,
    mut v___x_1421_: *mut crate::leanh::LeanObject,
    mut v_mode_1422_: u8,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
    mut v_b_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_1439_: u8 = 0;
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_a_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1470_: u8 = 0;
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1476_: u8 = 0;
    let mut v_a_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1435_ = lean_nat_dec_lt(v_a_1423_, v_upperBound_1418_);
                if v___x_1435_ == 0 {
                    crate::leanh::lean_dec(v_a_1423_);
                    v___x_1436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1436_, 0, v_b_1424_);
                    return v___x_1436_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1424_);
                    v___x_1437_ = l_Lean_Meta_instInhabitedParamInfo_default;
                    v___x_1438_ = lean_array_get_borrowed(v___x_1437_, v_a_1419_, v_a_1423_);
                    v_isInstance_1439_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1438_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 4) as u32,
                    );
                    v___x_1440_ = crate::leanh::lean_box(0);
                    v___x_1441_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    if v_isInstance_1439_ == 0 {
                        v___x_1442_ = l_Lean_instInhabitedExpr;
                        v___x_1443_ = lean_array_get_borrowed(v___x_1442_, v___x_1420_, v_a_1423_);
                        v___x_1444_ = lean_array_get_borrowed(v___x_1442_, v___x_1421_, v_a_1423_);
                        crate::leanh::lean_inc(v___x_1444_);
                        crate::leanh::lean_inc(v___x_1443_);
                        v___x_1445_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1422_,
                            v___x_1443_,
                            v___x_1444_,
                            v___y_1425_,
                            v___y_1426_,
                            v___y_1427_,
                            v___y_1428_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1445_) == 0 {
                            v_a_1446_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                            v_isSharedCheck_1476_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1445_)) as u8;
                            if v_isSharedCheck_1476_ == 0 {
                                v___x_1448_ = v___x_1445_;
                                v_isShared_1449_ = v_isSharedCheck_1476_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1446_);
                                crate::leanh::lean_dec(v___x_1445_);
                                v___x_1448_ = crate::leanh::lean_box(0);
                                v_isShared_1449_ = v_isSharedCheck_1476_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1423_);
                            v_a_1477_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                            v_isSharedCheck_1484_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1445_)) as u8;
                            if v_isSharedCheck_1484_ == 0 {
                                v___x_1479_ = v___x_1445_;
                                v_isShared_1480_ = v_isSharedCheck_1484_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1477_);
                                crate::leanh::lean_dec(v___x_1445_);
                                v___x_1479_ = crate::leanh::lean_box(0);
                                v_isShared_1480_ = v_isSharedCheck_1484_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        v_a_1431_ = v___x_1441_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1432_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1433_ = lean_nat_add(v_a_1423_, v___x_1432_);
                crate::leanh::lean_dec(v_a_1423_);
                crate::leanh::lean_inc_ref(v_a_1431_);
                v_a_1423_ = v___x_1433_;
                v_b_1424_ = v_a_1431_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1450_ = (crate::leanh::lean_unbox(v_a_1446_) as u8);
                if v___x_1450_ == 0 {
                    crate::leanh::lean_del_object(v___x_1448_);
                    crate::leanh::lean_inc(v___x_1443_);
                    crate::leanh::lean_inc(v___x_1444_);
                    v___x_1451_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1422_,
                        v___x_1444_,
                        v___x_1443_,
                        v___y_1425_,
                        v___y_1426_,
                        v___y_1427_,
                        v___y_1428_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1451_) == 0 {
                        v_a_1452_ = crate::leanh::lean_ctor_get(v___x_1451_, 0);
                        v_isSharedCheck_1462_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1451_)) as u8;
                        if v_isSharedCheck_1462_ == 0 {
                            v___x_1454_ = v___x_1451_;
                            v_isShared_1455_ = v_isSharedCheck_1462_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1452_);
                            crate::leanh::lean_dec(v___x_1451_);
                            v___x_1454_ = crate::leanh::lean_box(0);
                            v_isShared_1455_ = v_isSharedCheck_1462_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1446_);
                        crate::leanh::lean_dec(v_a_1423_);
                        v_a_1463_ = crate::leanh::lean_ctor_get(v___x_1451_, 0);
                        v_isSharedCheck_1470_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1451_)) as u8;
                        if v_isSharedCheck_1470_ == 0 {
                            v___x_1465_ = v___x_1451_;
                            v_isShared_1466_ = v_isSharedCheck_1470_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1463_);
                            crate::leanh::lean_dec(v___x_1451_);
                            v___x_1465_ = crate::leanh::lean_box(0);
                            v_isShared_1466_ = v_isSharedCheck_1470_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1423_);
                    v___x_1471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1471_, 0, v_a_1446_);
                    v___x_1472_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                    crate::leanh::lean_ctor_set(v___x_1472_, 1, v___x_1440_);
                    if v_isShared_1449_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1448_, 0, v___x_1472_);
                        v___x_1474_ = v___x_1448_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
                        v___x_1474_ = v_reuseFailAlloc_1475_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1456_ = (crate::leanh::lean_unbox(v_a_1452_) as u8);
                crate::leanh::lean_dec(v_a_1452_);
                if v___x_1456_ == 0 {
                    crate::leanh::lean_del_object(v___x_1454_);
                    crate::leanh::lean_dec(v_a_1446_);
                    v_a_1431_ = v___x_1441_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1423_);
                    v___x_1457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1457_, 0, v_a_1446_);
                    v___x_1458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
                    crate::leanh::lean_ctor_set(v___x_1458_, 1, v___x_1440_);
                    if v_isShared_1455_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1454_, 0, v___x_1458_);
                        v___x_1460_ = v___x_1454_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
                        v___x_1460_ = v_reuseFailAlloc_1461_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1460_;
            }
            5 => {
                if v_isShared_1466_ == 0 {
                    v___x_1468_ = v___x_1465_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
                    v___x_1468_ = v_reuseFailAlloc_1469_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1468_;
            }
            7 => {
                return v___x_1474_;
            }
            8 => {
                if v_isShared_1480_ == 0 {
                    v___x_1482_ = v___x_1479_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
                    v___x_1482_ = v_reuseFailAlloc_1483_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(
    mut v_upperBound_1485_: *mut crate::leanh::LeanObject,
    mut v___x_1486_: *mut crate::leanh::LeanObject,
    mut v___x_1487_: *mut crate::leanh::LeanObject,
    mut v_mode_1488_: u8,
    mut v_a_1489_: *mut crate::leanh::LeanObject,
    mut v_b_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
    mut v___y_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1496_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1523_: u8 = 0;
    let mut v_a_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1537_: u8 = 0;
    let mut v_a_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1496_ = lean_nat_dec_lt(v_a_1489_, v_upperBound_1485_);
                if v___x_1496_ == 0 {
                    crate::leanh::lean_dec(v_a_1489_);
                    v___x_1497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1497_, 0, v_b_1490_);
                    return v___x_1497_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1490_);
                    v___x_1498_ = l_Lean_instInhabitedExpr;
                    v___x_1499_ = lean_array_get_borrowed(v___x_1498_, v___x_1486_, v_a_1489_);
                    v___x_1500_ = lean_array_get_borrowed(v___x_1498_, v___x_1487_, v_a_1489_);
                    crate::leanh::lean_inc(v___x_1500_);
                    crate::leanh::lean_inc(v___x_1499_);
                    v___x_1501_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1488_,
                        v___x_1499_,
                        v___x_1500_,
                        v___y_1491_,
                        v___y_1492_,
                        v___y_1493_,
                        v___y_1494_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1501_) == 0 {
                        v_a_1502_ = crate::leanh::lean_ctor_get(v___x_1501_, 0);
                        v_isSharedCheck_1537_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1501_)) as u8;
                        if v_isSharedCheck_1537_ == 0 {
                            v___x_1504_ = v___x_1501_;
                            v_isShared_1505_ = v_isSharedCheck_1537_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1502_);
                            crate::leanh::lean_dec(v___x_1501_);
                            v___x_1504_ = crate::leanh::lean_box(0);
                            v_isShared_1505_ = v_isSharedCheck_1537_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1489_);
                        v_a_1538_ = crate::leanh::lean_ctor_get(v___x_1501_, 0);
                        v_isSharedCheck_1545_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1501_)) as u8;
                        if v_isSharedCheck_1545_ == 0 {
                            v___x_1540_ = v___x_1501_;
                            v_isShared_1541_ = v_isSharedCheck_1545_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1538_);
                            crate::leanh::lean_dec(v___x_1501_);
                            v___x_1540_ = crate::leanh::lean_box(0);
                            v_isShared_1541_ = v_isSharedCheck_1545_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1506_ = crate::leanh::lean_box(0);
                v___x_1507_ = (crate::leanh::lean_unbox(v_a_1502_) as u8);
                if v___x_1507_ == 0 {
                    crate::leanh::lean_del_object(v___x_1504_);
                    crate::leanh::lean_inc(v___x_1499_);
                    crate::leanh::lean_inc(v___x_1500_);
                    v___x_1508_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1488_,
                        v___x_1500_,
                        v___x_1499_,
                        v___y_1491_,
                        v___y_1492_,
                        v___y_1493_,
                        v___y_1494_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1508_) == 0 {
                        v_a_1509_ = crate::leanh::lean_ctor_get(v___x_1508_, 0);
                        v_isSharedCheck_1523_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1508_)) as u8;
                        if v_isSharedCheck_1523_ == 0 {
                            v___x_1511_ = v___x_1508_;
                            v_isShared_1512_ = v_isSharedCheck_1523_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1509_);
                            crate::leanh::lean_dec(v___x_1508_);
                            v___x_1511_ = crate::leanh::lean_box(0);
                            v_isShared_1512_ = v_isSharedCheck_1523_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1502_);
                        crate::leanh::lean_dec(v_a_1489_);
                        v_a_1524_ = crate::leanh::lean_ctor_get(v___x_1508_, 0);
                        v_isSharedCheck_1531_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1508_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1526_ = v___x_1508_;
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1524_);
                            crate::leanh::lean_dec(v___x_1508_);
                            v___x_1526_ = crate::leanh::lean_box(0);
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1489_);
                    v___x_1532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1532_, 0, v_a_1502_);
                    v___x_1533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1533_, 0, v___x_1532_);
                    crate::leanh::lean_ctor_set(v___x_1533_, 1, v___x_1506_);
                    if v_isShared_1505_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1504_, 0, v___x_1533_);
                        v___x_1535_ = v___x_1504_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
                        v___x_1535_ = v_reuseFailAlloc_1536_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1513_ = (crate::leanh::lean_unbox(v_a_1509_) as u8);
                crate::leanh::lean_dec(v_a_1509_);
                if v___x_1513_ == 0 {
                    crate::leanh::lean_del_object(v___x_1511_);
                    crate::leanh::lean_dec(v_a_1502_);
                    v___x_1514_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    v___x_1515_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1516_ = lean_nat_add(v_a_1489_, v___x_1515_);
                    crate::leanh::lean_dec(v_a_1489_);
                    v_a_1489_ = v___x_1516_;
                    v_b_1490_ = v___x_1514_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1489_);
                    v___x_1518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1518_, 0, v_a_1502_);
                    v___x_1519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1519_, 0, v___x_1518_);
                    crate::leanh::lean_ctor_set(v___x_1519_, 1, v___x_1506_);
                    if v_isShared_1512_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1511_, 0, v___x_1519_);
                        v___x_1521_ = v___x_1511_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
                        v___x_1521_ = v_reuseFailAlloc_1522_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1521_;
            }
            4 => {
                if v_isShared_1527_ == 0 {
                    v___x_1529_ = v___x_1526_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
                    v___x_1529_ = v_reuseFailAlloc_1530_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1529_;
            }
            6 => {
                return v___x_1535_;
            }
            7 => {
                if v_isShared_1541_ == 0 {
                    v___x_1543_ = v___x_1540_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
                    v___x_1543_ = v_reuseFailAlloc_1544_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(
    mut v_mode_1546_: u8,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
    mut v_b_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_aFn_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bFn_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v_dummy_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v_fst_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1595_: u8 = 0;
    let mut v_fst_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut v_a_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_val_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1617_: u8 = 0;
    let mut v_a_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_a_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1636_: u8 = 0;
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut v_unused_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1649_: u8 = 0;
    let mut v_unused_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aFn_1554_ = l_Lean_Expr_getAppFn(v_a_1547_);
                v_bFn_1555_ = l_Lean_Expr_getAppFn(v_b_1548_);
                crate::leanh::lean_inc_ref(v_bFn_1555_);
                crate::leanh::lean_inc_ref(v_aFn_1554_);
                v___x_1556_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_1546_,
                    v_aFn_1554_,
                    v_bFn_1555_,
                    v_a_1549_,
                    v_a_1550_,
                    v_a_1551_,
                    v_a_1552_,
                );
                if crate::leanh::lean_obj_tag(v___x_1556_) == 0 {
                    v_a_1557_ = crate::leanh::lean_ctor_get(v___x_1556_, 0);
                    v_isSharedCheck_1655_ = (!crate::leanh::lean_is_exclusive(v___x_1556_)) as u8;
                    if v_isSharedCheck_1655_ == 0 {
                        v___x_1559_ = v___x_1556_;
                        v_isShared_1560_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1557_);
                        crate::leanh::lean_dec(v___x_1556_);
                        v___x_1559_ = crate::leanh::lean_box(0);
                        v_isShared_1560_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_bFn_1555_);
                    crate::leanh::lean_dec_ref(v_aFn_1554_);
                    crate::leanh::lean_dec_ref(v_b_1548_);
                    crate::leanh::lean_dec_ref(v_a_1547_);
                    return v___x_1556_;
                }
            }
            1 => {
                v___x_1561_ = 1;
                v___x_1562_ = (crate::leanh::lean_unbox(v_a_1557_) as u8);
                if v___x_1562_ == 0 {
                    crate::leanh::lean_del_object(v___x_1559_);
                    crate::leanh::lean_inc_ref(v_aFn_1554_);
                    v___x_1563_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1546_,
                        v_bFn_1555_,
                        v_aFn_1554_,
                        v_a_1549_,
                        v_a_1550_,
                        v_a_1551_,
                        v_a_1552_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1563_) == 0 {
                        v_a_1564_ = crate::leanh::lean_ctor_get(v___x_1563_, 0);
                        crate::leanh::lean_inc(v_a_1564_);
                        v___x_1565_ = (crate::leanh::lean_unbox(v_a_1564_) as u8);
                        if v___x_1565_ == 0 {
                            crate::leanh::lean_dec(v_a_1557_);
                            v_dummy_1566_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
                            v_nargs_1567_ = l_Lean_Expr_getAppNumArgs(v_a_1547_);
                            crate::leanh::lean_inc(v_nargs_1567_);
                            v___x_1568_ = lean_mk_array(v_nargs_1567_, v_dummy_1566_);
                            v___x_1569_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1570_ = lean_nat_sub(v_nargs_1567_, v___x_1569_);
                            crate::leanh::lean_dec(v_nargs_1567_);
                            v___x_1571_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_a_1547_,
                                v___x_1568_,
                                v___x_1570_,
                            );
                            v_nargs_1572_ = l_Lean_Expr_getAppNumArgs(v_b_1548_);
                            crate::leanh::lean_inc(v_nargs_1572_);
                            v___x_1573_ = lean_mk_array(v_nargs_1572_, v_dummy_1566_);
                            v___x_1574_ = lean_nat_sub(v_nargs_1572_, v___x_1569_);
                            crate::leanh::lean_dec(v_nargs_1572_);
                            v___x_1575_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_b_1548_,
                                v___x_1573_,
                                v___x_1574_,
                            );
                            v___x_1576_ = lean_array_get_size(v___x_1571_);
                            v___x_1577_ = lean_array_get_size(v___x_1575_);
                            v___x_1578_ = lean_nat_dec_lt(v___x_1576_, v___x_1577_);
                            if v___x_1578_ == 0 {
                                v___x_1579_ = lean_nat_dec_lt(v___x_1577_, v___x_1576_);
                                if v___x_1579_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1563_, 1);
                                    v___x_1580_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_1554_, v___x_1576_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                                    if crate::leanh::lean_obj_tag(v___x_1580_) == 0 {
                                        v_a_1581_ = crate::leanh::lean_ctor_get(v___x_1580_, 0);
                                        crate::leanh::lean_inc(v_a_1581_);
                                        crate::leanh::lean_dec_ref_known(v___x_1580_, 1);
                                        v___x_1582_ = lean_array_get_size(v_a_1581_);
                                        v___x_1583_ = crate::leanh::lean_unsigned_to_nat(0);
                                        v___x_1584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                                        v___x_1585_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_1582_, v_a_1581_, v___x_1571_, v___x_1575_, v_mode_1546_, v___x_1583_, v___x_1584_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                                        crate::leanh::lean_dec(v_a_1581_);
                                        if crate::leanh::lean_obj_tag(v___x_1585_) == 0 {
                                            v_a_1586_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                                            v_isSharedCheck_1617_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1585_))
                                                    as u8;
                                            if v_isSharedCheck_1617_ == 0 {
                                                v___x_1588_ = v___x_1585_;
                                                v_isShared_1589_ = v_isSharedCheck_1617_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1586_);
                                                crate::leanh::lean_dec(v___x_1585_);
                                                v___x_1588_ = crate::leanh::lean_box(0);
                                                v_isShared_1589_ = v_isSharedCheck_1617_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1575_);
                                            crate::leanh::lean_dec_ref(v___x_1571_);
                                            crate::leanh::lean_dec(v_a_1564_);
                                            v_a_1618_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                                            v_isSharedCheck_1625_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1585_))
                                                    as u8;
                                            if v_isSharedCheck_1625_ == 0 {
                                                v___x_1620_ = v___x_1585_;
                                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                                state = 9;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1618_);
                                                crate::leanh::lean_dec(v___x_1585_);
                                                v___x_1620_ = crate::leanh::lean_box(0);
                                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_1575_);
                                        crate::leanh::lean_dec_ref(v___x_1571_);
                                        crate::leanh::lean_dec(v_a_1564_);
                                        v_a_1626_ = crate::leanh::lean_ctor_get(v___x_1580_, 0);
                                        v_isSharedCheck_1633_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1580_)) as u8;
                                        if v_isSharedCheck_1633_ == 0 {
                                            v___x_1628_ = v___x_1580_;
                                            v_isShared_1629_ = v_isSharedCheck_1633_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1626_);
                                            crate::leanh::lean_dec(v___x_1580_);
                                            v___x_1628_ = crate::leanh::lean_box(0);
                                            v_isShared_1629_ = v_isSharedCheck_1633_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_1575_);
                                    crate::leanh::lean_dec_ref(v___x_1571_);
                                    crate::leanh::lean_dec(v_a_1564_);
                                    crate::leanh::lean_dec_ref(v_aFn_1554_);
                                    return v___x_1563_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1575_);
                                crate::leanh::lean_dec_ref(v___x_1571_);
                                crate::leanh::lean_dec(v_a_1564_);
                                crate::leanh::lean_dec_ref(v_aFn_1554_);
                                v_isSharedCheck_1641_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1563_)) as u8;
                                if v_isSharedCheck_1641_ == 0 {
                                    v_unused_1642_ = crate::leanh::lean_ctor_get(v___x_1563_, 0);
                                    crate::leanh::lean_dec(v_unused_1642_);
                                    v___x_1635_ = v___x_1563_;
                                    v_isShared_1636_ = v_isSharedCheck_1641_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1563_);
                                    v___x_1635_ = crate::leanh::lean_box(0);
                                    v_isShared_1636_ = v_isSharedCheck_1641_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1564_);
                            crate::leanh::lean_dec_ref(v_aFn_1554_);
                            crate::leanh::lean_dec_ref(v_b_1548_);
                            crate::leanh::lean_dec_ref(v_a_1547_);
                            v_isSharedCheck_1649_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1563_)) as u8;
                            if v_isSharedCheck_1649_ == 0 {
                                v_unused_1650_ = crate::leanh::lean_ctor_get(v___x_1563_, 0);
                                crate::leanh::lean_dec(v_unused_1650_);
                                v___x_1644_ = v___x_1563_;
                                v_isShared_1645_ = v_isSharedCheck_1649_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1563_);
                                v___x_1644_ = crate::leanh::lean_box(0);
                                v_isShared_1645_ = v_isSharedCheck_1649_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1557_);
                        crate::leanh::lean_dec_ref(v_aFn_1554_);
                        crate::leanh::lean_dec_ref(v_b_1548_);
                        crate::leanh::lean_dec_ref(v_a_1547_);
                        return v___x_1563_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1557_);
                    crate::leanh::lean_dec_ref(v_bFn_1555_);
                    crate::leanh::lean_dec_ref(v_aFn_1554_);
                    crate::leanh::lean_dec_ref(v_b_1548_);
                    crate::leanh::lean_dec_ref(v_a_1547_);
                    v___x_1651_ = crate::leanh::lean_box((v___x_1561_) as usize);
                    if v_isShared_1560_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1559_, 0, v___x_1651_);
                        v___x_1653_ = v___x_1559_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
                        v___x_1653_ = v_reuseFailAlloc_1654_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1590_ = crate::leanh::lean_ctor_get(v_a_1586_, 0);
                crate::leanh::lean_inc(v_fst_1590_);
                crate::leanh::lean_dec(v_a_1586_);
                if crate::leanh::lean_obj_tag(v_fst_1590_) == 0 {
                    crate::leanh::lean_del_object(v___x_1588_);
                    v___x_1591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_1576_, v___x_1571_, v___x_1575_, v_mode_1546_, v___x_1582_, v___x_1584_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                    crate::leanh::lean_dec_ref(v___x_1575_);
                    crate::leanh::lean_dec_ref(v___x_1571_);
                    if crate::leanh::lean_obj_tag(v___x_1591_) == 0 {
                        v_a_1592_ = crate::leanh::lean_ctor_get(v___x_1591_, 0);
                        v_isSharedCheck_1604_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1591_)) as u8;
                        if v_isSharedCheck_1604_ == 0 {
                            v___x_1594_ = v___x_1591_;
                            v_isShared_1595_ = v_isSharedCheck_1604_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1592_);
                            crate::leanh::lean_dec(v___x_1591_);
                            v___x_1594_ = crate::leanh::lean_box(0);
                            v_isShared_1595_ = v_isSharedCheck_1604_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1564_);
                        v_a_1605_ = crate::leanh::lean_ctor_get(v___x_1591_, 0);
                        v_isSharedCheck_1612_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1591_)) as u8;
                        if v_isSharedCheck_1612_ == 0 {
                            v___x_1607_ = v___x_1591_;
                            v_isShared_1608_ = v_isSharedCheck_1612_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1605_);
                            crate::leanh::lean_dec(v___x_1591_);
                            v___x_1607_ = crate::leanh::lean_box(0);
                            v_isShared_1608_ = v_isSharedCheck_1612_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1575_);
                    crate::leanh::lean_dec_ref(v___x_1571_);
                    crate::leanh::lean_dec(v_a_1564_);
                    v_val_1613_ = crate::leanh::lean_ctor_get(v_fst_1590_, 0);
                    crate::leanh::lean_inc(v_val_1613_);
                    crate::leanh::lean_dec_ref_known(v_fst_1590_, 1);
                    if v_isShared_1589_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1588_, 0, v_val_1613_);
                        v___x_1615_ = v___x_1588_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_val_1613_);
                        v___x_1615_ = v_reuseFailAlloc_1616_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_1596_ = crate::leanh::lean_ctor_get(v_a_1592_, 0);
                crate::leanh::lean_inc(v_fst_1596_);
                crate::leanh::lean_dec(v_a_1592_);
                if crate::leanh::lean_obj_tag(v_fst_1596_) == 0 {
                    if v_isShared_1595_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1594_, 0, v_a_1564_);
                        v___x_1598_ = v___x_1594_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1564_);
                        v___x_1598_ = v_reuseFailAlloc_1599_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1564_);
                    v_val_1600_ = crate::leanh::lean_ctor_get(v_fst_1596_, 0);
                    crate::leanh::lean_inc(v_val_1600_);
                    crate::leanh::lean_dec_ref_known(v_fst_1596_, 1);
                    if v_isShared_1595_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1594_, 0, v_val_1600_);
                        v___x_1602_ = v___x_1594_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
                        v___x_1602_ = v_reuseFailAlloc_1603_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1598_;
            }
            5 => {
                return v___x_1602_;
            }
            6 => {
                if v_isShared_1608_ == 0 {
                    v___x_1610_ = v___x_1607_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
                    v___x_1610_ = v_reuseFailAlloc_1611_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1610_;
            }
            8 => {
                return v___x_1615_;
            }
            9 => {
                if v_isShared_1621_ == 0 {
                    v___x_1623_ = v___x_1620_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
                    v___x_1623_ = v_reuseFailAlloc_1624_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1623_;
            }
            11 => {
                if v_isShared_1629_ == 0 {
                    v___x_1631_ = v___x_1628_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
                    v___x_1631_ = v_reuseFailAlloc_1632_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1631_;
            }
            13 => {
                v___x_1637_ = crate::leanh::lean_box((v___x_1561_) as usize);
                if v_isShared_1636_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1635_, 0, v___x_1637_);
                    v___x_1639_ = v___x_1635_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
                    v___x_1639_ = v_reuseFailAlloc_1640_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1639_;
            }
            15 => {
                if v_isShared_1645_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1644_, 0, v_a_1557_);
                    v___x_1647_ = v___x_1644_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1648_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1557_);
                    v___x_1647_ = v_reuseFailAlloc_1648_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1647_;
            }
            17 => {
                return v___x_1653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6;
    v___x_1660_ = crate::leanh::lean_unsigned_to_nat(27);
    v___x_1661_ = crate::leanh::lean_unsigned_to_nat(152);
    v___x_1662_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5;
    v___x_1663_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4;
    v___x_1664_ = l_mkPanicMessageWithDecl(
        v___x_1663_,
        v___x_1662_,
        v___x_1661_,
        v___x_1660_,
        v___x_1659_,
    );
    return v___x_1664_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(
    mut v_mode_1665_: u8,
    mut v_a_1666_: *mut crate::leanh::LeanObject,
    mut v_b_1667_: *mut crate::leanh::LeanObject,
    mut v_a_1668_: *mut crate::leanh::LeanObject,
    mut v_a_1669_: *mut crate::leanh::LeanObject,
    mut v_a_1670_: *mut crate::leanh::LeanObject,
    mut v_a_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___y_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut v_a_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut v_mvarId_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_1666_) {
                0 => {
                    v_deBruijnIndex_1683_ = crate::leanh::lean_ctor_get(v_a_1666_, 0);
                    crate::leanh::lean_inc(v_deBruijnIndex_1683_);
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1684_ = l_Lean_Expr_bvarIdx_x21(v_b_1667_);
                    crate::leanh::lean_dec_ref(v_b_1667_);
                    v___x_1685_ = lean_nat_dec_lt(v_deBruijnIndex_1683_, v___x_1684_);
                    crate::leanh::lean_dec(v___x_1684_);
                    crate::leanh::lean_dec(v_deBruijnIndex_1683_);
                    v___x_1686_ = crate::leanh::lean_box((v___x_1685_) as usize);
                    v___x_1687_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1687_, 0, v___x_1686_);
                    return v___x_1687_;
                }
                1 => {
                    v_fvarId_1688_ = crate::leanh::lean_ctor_get(v_a_1666_, 0);
                    crate::leanh::lean_inc(v_fvarId_1688_);
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1689_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_1688_, v_a_1668_);
                    if crate::leanh::lean_obj_tag(v___x_1689_) == 0 {
                        v_a_1690_ = crate::leanh::lean_ctor_get(v___x_1689_, 0);
                        crate::leanh::lean_inc(v_a_1690_);
                        crate::leanh::lean_dec_ref_known(v___x_1689_, 1);
                        v___x_1691_ = l_Lean_Expr_fvarId_x21(v_b_1667_);
                        crate::leanh::lean_dec_ref(v_b_1667_);
                        v___x_1692_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_1691_, v_a_1668_);
                        if crate::leanh::lean_obj_tag(v___x_1692_) == 0 {
                            v_a_1693_ = crate::leanh::lean_ctor_get(v___x_1692_, 0);
                            v_isSharedCheck_1715_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1692_)) as u8;
                            if v_isSharedCheck_1715_ == 0 {
                                v___x_1695_ = v___x_1692_;
                                v_isShared_1696_ = v_isSharedCheck_1715_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1693_);
                                crate::leanh::lean_dec(v___x_1692_);
                                v___x_1695_ = crate::leanh::lean_box(0);
                                v_isShared_1696_ = v_isSharedCheck_1715_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1690_);
                            v_a_1716_ = crate::leanh::lean_ctor_get(v___x_1692_, 0);
                            v_isSharedCheck_1723_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1692_)) as u8;
                            if v_isSharedCheck_1723_ == 0 {
                                v___x_1718_ = v___x_1692_;
                                v_isShared_1719_ = v_isSharedCheck_1723_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1716_);
                                crate::leanh::lean_dec(v___x_1692_);
                                v___x_1718_ = crate::leanh::lean_box(0);
                                v_isShared_1719_ = v_isSharedCheck_1723_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1667_);
                        v_a_1724_ = crate::leanh::lean_ctor_get(v___x_1689_, 0);
                        v_isSharedCheck_1731_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1689_)) as u8;
                        if v_isSharedCheck_1731_ == 0 {
                            v___x_1726_ = v___x_1689_;
                            v_isShared_1727_ = v_isSharedCheck_1731_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1724_);
                            crate::leanh::lean_dec(v___x_1689_);
                            v___x_1726_ = crate::leanh::lean_box(0);
                            v_isShared_1727_ = v_isSharedCheck_1731_;
                            state = 8;
                            continue;
                        }
                    }
                }
                2 => {
                    v_mvarId_1732_ = crate::leanh::lean_ctor_get(v_a_1666_, 0);
                    crate::leanh::lean_inc(v_mvarId_1732_);
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1733_ = l_Lean_Expr_mvarId_x21(v_b_1667_);
                    crate::leanh::lean_dec_ref(v_b_1667_);
                    v___x_1734_ = l_Lean_Name_lt(v_mvarId_1732_, v___x_1733_);
                    crate::leanh::lean_dec(v___x_1733_);
                    crate::leanh::lean_dec(v_mvarId_1732_);
                    v___x_1735_ = crate::leanh::lean_box((v___x_1734_) as usize);
                    v___x_1736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1736_, 0, v___x_1735_);
                    return v___x_1736_;
                }
                3 => {
                    v_u_1737_ = crate::leanh::lean_ctor_get(v_a_1666_, 0);
                    crate::leanh::lean_inc(v_u_1737_);
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1738_ = l_Lean_Expr_sortLevel_x21(v_b_1667_);
                    crate::leanh::lean_dec_ref(v_b_1667_);
                    v___x_1739_ = l_Lean_Level_normLt(v_u_1737_, v___x_1738_);
                    crate::leanh::lean_dec(v___x_1738_);
                    crate::leanh::lean_dec(v_u_1737_);
                    v___x_1740_ = crate::leanh::lean_box((v___x_1739_) as usize);
                    v___x_1741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1741_, 0, v___x_1740_);
                    return v___x_1741_;
                }
                4 => {
                    v_declName_1742_ = crate::leanh::lean_ctor_get(v_a_1666_, 0);
                    crate::leanh::lean_inc(v_declName_1742_);
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 2);
                    v___x_1743_ = l_Lean_Expr_constName_x21(v_b_1667_);
                    crate::leanh::lean_dec_ref(v_b_1667_);
                    v___x_1744_ = l_Lean_Name_lt(v_declName_1742_, v___x_1743_);
                    crate::leanh::lean_dec(v___x_1743_);
                    crate::leanh::lean_dec(v_declName_1742_);
                    v___x_1745_ = crate::leanh::lean_box((v___x_1744_) as usize);
                    v___x_1746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1746_, 0, v___x_1745_);
                    return v___x_1746_;
                }
                5 => {
                    v___x_1747_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(
                        v_mode_1665_,
                        v_a_1666_,
                        v_b_1667_,
                        v_a_1668_,
                        v_a_1669_,
                        v_a_1670_,
                        v_a_1671_,
                    );
                    return v___x_1747_;
                }
                8 => {
                    v_value_1748_ = crate::leanh::lean_ctor_get(v_a_1666_, 2);
                    crate::leanh::lean_inc_ref(v_value_1748_);
                    v_body_1749_ = crate::leanh::lean_ctor_get(v_a_1666_, 3);
                    crate::leanh::lean_inc_ref(v_body_1749_);
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 4);
                    v___x_1750_ = l_Lean_Expr_letValue_x21(v_b_1667_);
                    v___x_1751_ = l_Lean_Expr_letBody_x21(v_b_1667_);
                    crate::leanh::lean_dec_ref(v_b_1667_);
                    v___x_1752_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(
                        v_mode_1665_,
                        v_value_1748_,
                        v_body_1749_,
                        v___x_1750_,
                        v___x_1751_,
                        v_a_1668_,
                        v_a_1669_,
                        v_a_1670_,
                        v_a_1671_,
                    );
                    return v___x_1752_;
                }
                9 => {
                    v_a_1753_ = crate::leanh::lean_ctor_get(v_a_1666_, 0);
                    crate::leanh::lean_inc_ref(v_a_1753_);
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1754_ = l_Lean_Expr_litValue_x21(v_b_1667_);
                    crate::leanh::lean_dec_ref(v_b_1667_);
                    v___x_1755_ = l_Lean_Literal_lt(v_a_1753_, v___x_1754_);
                    crate::leanh::lean_dec_ref(v___x_1754_);
                    crate::leanh::lean_dec_ref(v_a_1753_);
                    v___x_1756_ = crate::leanh::lean_box((v___x_1755_) as usize);
                    v___x_1757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1757_, 0, v___x_1756_);
                    return v___x_1757_;
                }
                10 => {
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 2);
                    crate::leanh::lean_dec_ref(v_b_1667_);
                    v___x_1758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
                    v___x_1759_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_1758_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
                    return v___x_1759_;
                }
                11 => {
                    v_idx_1760_ = crate::leanh::lean_ctor_get(v_a_1666_, 1);
                    crate::leanh::lean_inc(v_idx_1760_);
                    v_struct_1761_ = crate::leanh::lean_ctor_get(v_a_1666_, 2);
                    crate::leanh::lean_inc_ref(v_struct_1761_);
                    crate::leanh::lean_dec_ref_known(v_a_1666_, 3);
                    v___x_1762_ = l_Lean_Expr_projIdx_x21(v_b_1667_);
                    v___x_1763_ = lean_nat_dec_eq(v_idx_1760_, v___x_1762_);
                    if v___x_1763_ == 0 {
                        crate::leanh::lean_dec_ref(v_struct_1761_);
                        crate::leanh::lean_dec_ref(v_b_1667_);
                        v___x_1764_ = lean_nat_dec_lt(v_idx_1760_, v___x_1762_);
                        crate::leanh::lean_dec(v___x_1762_);
                        crate::leanh::lean_dec(v_idx_1760_);
                        v___x_1765_ = crate::leanh::lean_box((v___x_1764_) as usize);
                        v___x_1766_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1765_);
                        return v___x_1766_;
                    } else {
                        crate::leanh::lean_dec(v___x_1762_);
                        crate::leanh::lean_dec(v_idx_1760_);
                        v___x_1767_ = l_Lean_Expr_projExpr_x21(v_b_1667_);
                        crate::leanh::lean_dec_ref(v_b_1667_);
                        v___x_1768_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1665_,
                            v_struct_1761_,
                            v___x_1767_,
                            v_a_1668_,
                            v_a_1669_,
                            v_a_1670_,
                            v_a_1671_,
                        );
                        return v___x_1768_;
                    }
                }
                _ => {
                    v_binderType_1769_ = crate::leanh::lean_ctor_get(v_a_1666_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_1769_);
                    v_body_1770_ = crate::leanh::lean_ctor_get(v_a_1666_, 2);
                    crate::leanh::lean_inc_ref(v_body_1770_);
                    crate::leanh::lean_dec_ref(v_a_1666_);
                    v_d_1674_ = v_binderType_1769_;
                    v_e_1675_ = v_body_1770_;
                    v___y_1676_ = v_a_1668_;
                    v___y_1677_ = v_a_1669_;
                    v___y_1678_ = v_a_1670_;
                    v___y_1679_ = v_a_1671_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1680_ = l_Lean_Expr_bindingDomain_x21(v_b_1667_);
                v___x_1681_ = l_Lean_Expr_bindingBody_x21(v_b_1667_);
                crate::leanh::lean_dec_ref(v_b_1667_);
                v___x_1682_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(
                    v_mode_1665_,
                    v_d_1674_,
                    v_e_1675_,
                    v___x_1680_,
                    v___x_1681_,
                    v___y_1676_,
                    v___y_1677_,
                    v___y_1678_,
                    v___y_1679_,
                );
                return v___x_1682_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1690_) == 0 {
                    v___x_1712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
                    v___x_1713_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_1712_);
                    v___y_1707_ = v___x_1713_;
                    state = 5;
                    continue;
                } else {
                    v_val_1714_ = crate::leanh::lean_ctor_get(v_a_1690_, 0);
                    crate::leanh::lean_inc(v_val_1714_);
                    crate::leanh::lean_dec_ref_known(v_a_1690_, 1);
                    v___y_1707_ = v_val_1714_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_1700_ = l_Lean_LocalDecl_index(v___y_1699_);
                crate::leanh::lean_dec_ref(v___y_1699_);
                v___x_1701_ = lean_nat_dec_lt(v___y_1698_, v___x_1700_);
                crate::leanh::lean_dec(v___x_1700_);
                crate::leanh::lean_dec(v___y_1698_);
                v___x_1702_ = crate::leanh::lean_box((v___x_1701_) as usize);
                if v_isShared_1696_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1695_, 0, v___x_1702_);
                    v___x_1704_ = v___x_1695_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
                    v___x_1704_ = v_reuseFailAlloc_1705_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1704_;
            }
            5 => {
                v___x_1708_ = l_Lean_LocalDecl_index(v___y_1707_);
                crate::leanh::lean_dec_ref(v___y_1707_);
                if crate::leanh::lean_obj_tag(v_a_1693_) == 0 {
                    v___x_1709_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
                    v___x_1710_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_1709_);
                    v___y_1698_ = v___x_1708_;
                    v___y_1699_ = v___x_1710_;
                    state = 3;
                    continue;
                } else {
                    v_val_1711_ = crate::leanh::lean_ctor_get(v_a_1693_, 0);
                    crate::leanh::lean_inc(v_val_1711_);
                    crate::leanh::lean_dec_ref_known(v_a_1693_, 1);
                    v___y_1698_ = v___x_1708_;
                    v___y_1699_ = v_val_1711_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                if v_isShared_1719_ == 0 {
                    v___x_1721_ = v___x_1718_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
                    v___x_1721_ = v_reuseFailAlloc_1722_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1721_;
            }
            8 => {
                if v_isShared_1727_ == 0 {
                    v___x_1729_ = v___x_1726_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
                    v___x_1729_ = v_reuseFailAlloc_1730_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(
    mut v_mode_1771_: u8,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
    mut v_b_1773_: *mut crate::leanh::LeanObject,
    mut v_a_1774_: *mut crate::leanh::LeanObject,
    mut v_a_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1811_: u8 = 0;
    let mut v_unused_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1779_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0;
                v___x_1780_ = l_Lean_Core_checkSystem(v___x_1779_, v_a_1776_, v_a_1777_);
                if crate::leanh::lean_obj_tag(v___x_1780_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1780_, 1);
                    crate::leanh::lean_inc_ref(v_a_1772_);
                    crate::leanh::lean_inc_ref(v_b_1773_);
                    v___x_1781_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
                        v_mode_1771_,
                        v_b_1773_,
                        v_a_1772_,
                        v_a_1774_,
                        v_a_1775_,
                        v_a_1776_,
                        v_a_1777_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1781_) == 0 {
                        v_a_1782_ = crate::leanh::lean_ctor_get(v___x_1781_, 0);
                        crate::leanh::lean_inc(v_a_1782_);
                        v___x_1783_ = 1;
                        v___x_1784_ = (crate::leanh::lean_unbox(v_a_1782_) as u8);
                        if v___x_1784_ == 0 {
                            v___x_1785_ = l_Lean_Expr_ctorWeight(v_b_1773_);
                            v___x_1786_ = l_Lean_Expr_ctorWeight(v_a_1772_);
                            v___x_1787_ = lean_uint8_dec_lt(v___x_1785_, v___x_1786_);
                            if v___x_1787_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1781_, 1);
                                crate::leanh::lean_inc_ref(v_b_1773_);
                                crate::leanh::lean_inc_ref(v_a_1772_);
                                v___x_1788_ =
                                    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(
                                        v_mode_1771_,
                                        v_a_1772_,
                                        v_b_1773_,
                                        v_a_1774_,
                                        v_a_1775_,
                                        v_a_1776_,
                                        v_a_1777_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_1788_) == 0 {
                                    v_a_1789_ = crate::leanh::lean_ctor_get(v___x_1788_, 0);
                                    v_isSharedCheck_1803_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1788_)) as u8;
                                    if v_isSharedCheck_1803_ == 0 {
                                        v___x_1791_ = v___x_1788_;
                                        v_isShared_1792_ = v_isSharedCheck_1803_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1789_);
                                        crate::leanh::lean_dec(v___x_1788_);
                                        v___x_1791_ = crate::leanh::lean_box(0);
                                        v_isShared_1792_ = v_isSharedCheck_1803_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1782_);
                                    crate::leanh::lean_dec_ref(v_b_1773_);
                                    crate::leanh::lean_dec_ref(v_a_1772_);
                                    return v___x_1788_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1782_);
                                crate::leanh::lean_dec_ref(v_b_1773_);
                                crate::leanh::lean_dec_ref(v_a_1772_);
                                return v___x_1781_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1782_);
                            crate::leanh::lean_dec_ref(v_b_1773_);
                            crate::leanh::lean_dec_ref(v_a_1772_);
                            v_isSharedCheck_1811_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1781_)) as u8;
                            if v_isSharedCheck_1811_ == 0 {
                                v_unused_1812_ = crate::leanh::lean_ctor_get(v___x_1781_, 0);
                                crate::leanh::lean_dec(v_unused_1812_);
                                v___x_1805_ = v___x_1781_;
                                v_isShared_1806_ = v_isSharedCheck_1811_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1781_);
                                v___x_1805_ = crate::leanh::lean_box(0);
                                v_isShared_1806_ = v_isSharedCheck_1811_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1773_);
                        crate::leanh::lean_dec_ref(v_a_1772_);
                        return v___x_1781_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_1773_);
                    crate::leanh::lean_dec_ref(v_a_1772_);
                    v_a_1813_ = crate::leanh::lean_ctor_get(v___x_1780_, 0);
                    v_isSharedCheck_1820_ = (!crate::leanh::lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1815_ = v___x_1780_;
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1813_);
                        crate::leanh::lean_dec(v___x_1780_);
                        v___x_1815_ = crate::leanh::lean_box(0);
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1793_ = (crate::leanh::lean_unbox(v_a_1789_) as u8);
                crate::leanh::lean_dec(v_a_1789_);
                if v___x_1793_ == 0 {
                    crate::leanh::lean_dec_ref(v_b_1773_);
                    crate::leanh::lean_dec_ref(v_a_1772_);
                    if v_isShared_1792_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1791_, 0, v_a_1782_);
                        v___x_1795_ = v___x_1791_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1796_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1782_);
                        v___x_1795_ = v_reuseFailAlloc_1796_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1782_);
                    v___x_1797_ = lean_uint8_dec_lt(v___x_1786_, v___x_1785_);
                    if v___x_1797_ == 0 {
                        crate::leanh::lean_del_object(v___x_1791_);
                        v___x_1798_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(
                            v_mode_1771_,
                            v_a_1772_,
                            v_b_1773_,
                            v_a_1774_,
                            v_a_1775_,
                            v_a_1776_,
                            v_a_1777_,
                        );
                        return v___x_1798_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1773_);
                        crate::leanh::lean_dec_ref(v_a_1772_);
                        v___x_1799_ = crate::leanh::lean_box((v___x_1783_) as usize);
                        if v_isShared_1792_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1799_);
                            v___x_1801_ = v___x_1791_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1802_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
                            v___x_1801_ = v_reuseFailAlloc_1802_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1795_;
            }
            3 => {
                return v___x_1801_;
            }
            4 => {
                v___x_1807_ = crate::leanh::lean_box((v___x_1783_) as usize);
                if v_isShared_1806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1805_, 0, v___x_1807_);
                    v___x_1809_ = v___x_1805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
                    v___x_1809_ = v_reuseFailAlloc_1810_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1809_;
            }
            6 => {
                if v_isShared_1816_ == 0 {
                    v___x_1818_ = v___x_1815_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
                    v___x_1818_ = v_reuseFailAlloc_1819_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
    mut v_mode_1821_: u8,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
    mut v_b_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_a_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1852_: u8 = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1829_ = lean_expr_eqv(v_a_1822_, v_b_1823_);
                if v___x_1829_ == 0 {
                    v___x_1830_ = l_Lean_Expr_isMData(v_a_1822_);
                    if v___x_1830_ == 0 {
                        v___x_1831_ = l_Lean_Expr_isMData(v_b_1823_);
                        if v___x_1831_ == 0 {
                            v___x_1832_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(
                                v_mode_1821_,
                                v_a_1822_,
                                v_a_1824_,
                                v_a_1825_,
                                v_a_1826_,
                                v_a_1827_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1832_) == 0 {
                                v_a_1833_ = crate::leanh::lean_ctor_get(v___x_1832_, 0);
                                crate::leanh::lean_inc(v_a_1833_);
                                crate::leanh::lean_dec_ref_known(v___x_1832_, 1);
                                v___x_1834_ =
                                    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(
                                        v_mode_1821_,
                                        v_b_1823_,
                                        v_a_1824_,
                                        v_a_1825_,
                                        v_a_1826_,
                                        v_a_1827_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_1834_) == 0 {
                                    v_a_1835_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                                    crate::leanh::lean_inc(v_a_1835_);
                                    crate::leanh::lean_dec_ref_known(v___x_1834_, 1);
                                    v___x_1836_ =
                                        l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(
                                            v_mode_1821_,
                                            v_a_1833_,
                                            v_a_1835_,
                                            v_a_1824_,
                                            v_a_1825_,
                                            v_a_1826_,
                                            v_a_1827_,
                                        );
                                    return v___x_1836_;
                                } else {
                                    crate::leanh::lean_dec(v_a_1833_);
                                    v_a_1837_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                                    v_isSharedCheck_1844_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1834_)) as u8;
                                    if v_isSharedCheck_1844_ == 0 {
                                        v___x_1839_ = v___x_1834_;
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1837_);
                                        crate::leanh::lean_dec(v___x_1834_);
                                        v___x_1839_ = crate::leanh::lean_box(0);
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_b_1823_);
                                v_a_1845_ = crate::leanh::lean_ctor_get(v___x_1832_, 0);
                                v_isSharedCheck_1852_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1832_)) as u8;
                                if v_isSharedCheck_1852_ == 0 {
                                    v___x_1847_ = v___x_1832_;
                                    v_isShared_1848_ = v_isSharedCheck_1852_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1845_);
                                    crate::leanh::lean_dec(v___x_1832_);
                                    v___x_1847_ = crate::leanh::lean_box(0);
                                    v_isShared_1848_ = v_isSharedCheck_1852_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_1853_ = l_Lean_Expr_mdataExpr_x21(v_b_1823_);
                            crate::leanh::lean_dec_ref(v_b_1823_);
                            v_b_1823_ = v___x_1853_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1855_ = l_Lean_Expr_mdataExpr_x21(v_a_1822_);
                        crate::leanh::lean_dec_ref(v_a_1822_);
                        v_a_1822_ = v___x_1855_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_1823_);
                    crate::leanh::lean_dec_ref(v_a_1822_);
                    v___x_1857_ = 0;
                    v___x_1858_ = crate::leanh::lean_box((v___x_1857_) as usize);
                    v___x_1859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1859_, 0, v___x_1858_);
                    return v___x_1859_;
                }
            }
            1 => {
                if v_isShared_1840_ == 0 {
                    v___x_1842_ = v___x_1839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
                    v___x_1842_ = v_reuseFailAlloc_1843_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1842_;
            }
            3 => {
                if v_isShared_1848_ == 0 {
                    v___x_1850_ = v___x_1847_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
                    v___x_1850_ = v_reuseFailAlloc_1851_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(
    mut v_upperBound_1860_: *mut crate::leanh::LeanObject,
    mut v_a_1861_: *mut crate::leanh::LeanObject,
    mut v_args_1862_: *mut crate::leanh::LeanObject,
    mut v_mode_1863_: u8,
    mut v_b_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_b_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_1881_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1891_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_a_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1877_ = lean_nat_dec_lt(v_a_1865_, v_upperBound_1860_);
                if v___x_1877_ == 0 {
                    crate::leanh::lean_dec(v_a_1865_);
                    crate::leanh::lean_dec_ref(v_b_1864_);
                    v___x_1878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1878_, 0, v_b_1866_);
                    return v___x_1878_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1866_);
                    v___x_1879_ = l_Lean_Meta_instInhabitedParamInfo_default;
                    v___x_1880_ = lean_array_get_borrowed(v___x_1879_, v_a_1861_, v_a_1865_);
                    v_isInstance_1881_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1880_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 4) as u32,
                    );
                    v___x_1882_ = crate::leanh::lean_box(0);
                    v___x_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    if v_isInstance_1881_ == 0 {
                        v___x_1884_ = l_Lean_instInhabitedExpr;
                        v___x_1885_ = lean_array_get_borrowed(v___x_1884_, v_args_1862_, v_a_1865_);
                        crate::leanh::lean_inc_ref(v_b_1864_);
                        crate::leanh::lean_inc(v___x_1885_);
                        v___x_1886_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1863_,
                            v___x_1885_,
                            v_b_1864_,
                            v___y_1867_,
                            v___y_1868_,
                            v___y_1869_,
                            v___y_1870_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1886_) == 0 {
                            v_a_1887_ = crate::leanh::lean_ctor_get(v___x_1886_, 0);
                            v_isSharedCheck_1897_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1886_)) as u8;
                            if v_isSharedCheck_1897_ == 0 {
                                v___x_1889_ = v___x_1886_;
                                v_isShared_1890_ = v_isSharedCheck_1897_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1887_);
                                crate::leanh::lean_dec(v___x_1886_);
                                v___x_1889_ = crate::leanh::lean_box(0);
                                v_isShared_1890_ = v_isSharedCheck_1897_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1865_);
                            crate::leanh::lean_dec_ref(v_b_1864_);
                            v_a_1898_ = crate::leanh::lean_ctor_get(v___x_1886_, 0);
                            v_isSharedCheck_1905_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1886_)) as u8;
                            if v_isSharedCheck_1905_ == 0 {
                                v___x_1900_ = v___x_1886_;
                                v_isShared_1901_ = v_isSharedCheck_1905_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1898_);
                                crate::leanh::lean_dec(v___x_1886_);
                                v___x_1900_ = crate::leanh::lean_box(0);
                                v_isShared_1901_ = v_isSharedCheck_1905_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_1873_ = v___x_1883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1874_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1875_ = lean_nat_add(v_a_1865_, v___x_1874_);
                crate::leanh::lean_dec(v_a_1865_);
                crate::leanh::lean_inc_ref(v_a_1873_);
                v_a_1865_ = v___x_1875_;
                v_b_1866_ = v_a_1873_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1891_ = (crate::leanh::lean_unbox(v_a_1887_) as u8);
                if v___x_1891_ == 0 {
                    crate::leanh::lean_dec(v_a_1865_);
                    crate::leanh::lean_dec_ref(v_b_1864_);
                    v___x_1892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1892_, 0, v_a_1887_);
                    v___x_1893_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1893_, 0, v___x_1892_);
                    crate::leanh::lean_ctor_set(v___x_1893_, 1, v___x_1882_);
                    if v_isShared_1890_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1889_, 0, v___x_1893_);
                        v___x_1895_ = v___x_1889_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1896_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
                        v___x_1895_ = v_reuseFailAlloc_1896_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1889_);
                    crate::leanh::lean_dec(v_a_1887_);
                    v_a_1873_ = v___x_1883_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_1895_;
            }
            4 => {
                if v_isShared_1901_ == 0 {
                    v___x_1903_ = v___x_1900_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
                    v___x_1903_ = v_reuseFailAlloc_1904_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(
    mut v_upperBound_1906_: *mut crate::leanh::LeanObject,
    mut v_args_1907_: *mut crate::leanh::LeanObject,
    mut v_mode_1908_: u8,
    mut v_b_1909_: *mut crate::leanh::LeanObject,
    mut v_a_1910_: *mut crate::leanh::LeanObject,
    mut v_b_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v_a_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ = lean_nat_dec_lt(v_a_1910_, v_upperBound_1906_);
                if v___x_1917_ == 0 {
                    crate::leanh::lean_dec(v_a_1910_);
                    crate::leanh::lean_dec_ref(v_b_1909_);
                    v___x_1918_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1918_, 0, v_b_1911_);
                    return v___x_1918_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1911_);
                    v___x_1919_ = lean_array_fget_borrowed(v_args_1907_, v_a_1910_);
                    crate::leanh::lean_inc_ref(v_b_1909_);
                    crate::leanh::lean_inc(v___x_1919_);
                    v___x_1920_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1908_,
                        v___x_1919_,
                        v_b_1909_,
                        v___y_1912_,
                        v___y_1913_,
                        v___y_1914_,
                        v___y_1915_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1920_) == 0 {
                        v_a_1921_ = crate::leanh::lean_ctor_get(v___x_1920_, 0);
                        v_isSharedCheck_1936_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1920_)) as u8;
                        if v_isSharedCheck_1936_ == 0 {
                            v___x_1923_ = v___x_1920_;
                            v_isShared_1924_ = v_isSharedCheck_1936_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1921_);
                            crate::leanh::lean_dec(v___x_1920_);
                            v___x_1923_ = crate::leanh::lean_box(0);
                            v_isShared_1924_ = v_isSharedCheck_1936_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1910_);
                        crate::leanh::lean_dec_ref(v_b_1909_);
                        v_a_1937_ = crate::leanh::lean_ctor_get(v___x_1920_, 0);
                        v_isSharedCheck_1944_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1920_)) as u8;
                        if v_isSharedCheck_1944_ == 0 {
                            v___x_1939_ = v___x_1920_;
                            v_isShared_1940_ = v_isSharedCheck_1944_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1937_);
                            crate::leanh::lean_dec(v___x_1920_);
                            v___x_1939_ = crate::leanh::lean_box(0);
                            v_isShared_1940_ = v_isSharedCheck_1944_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1925_ = crate::leanh::lean_box(0);
                v___x_1926_ = (crate::leanh::lean_unbox(v_a_1921_) as u8);
                if v___x_1926_ == 0 {
                    crate::leanh::lean_dec(v_a_1910_);
                    crate::leanh::lean_dec_ref(v_b_1909_);
                    v___x_1927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1927_, 0, v_a_1921_);
                    v___x_1928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1928_, 0, v___x_1927_);
                    crate::leanh::lean_ctor_set(v___x_1928_, 1, v___x_1925_);
                    if v_isShared_1924_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1923_, 0, v___x_1928_);
                        v___x_1930_ = v___x_1923_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                        v___x_1930_ = v_reuseFailAlloc_1931_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1923_);
                    crate::leanh::lean_dec(v_a_1921_);
                    v___x_1932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    v___x_1933_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1934_ = lean_nat_add(v_a_1910_, v___x_1933_);
                    crate::leanh::lean_dec(v_a_1910_);
                    v_a_1910_ = v___x_1934_;
                    v_b_1911_ = v___x_1932_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_1930_;
            }
            3 => {
                if v_isShared_1940_ == 0 {
                    v___x_1942_ = v___x_1939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
                    v___x_1942_ = v_reuseFailAlloc_1943_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1942_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(
    mut v_mode_1945_: u8,
    mut v_b_1946_: *mut crate::leanh::LeanObject,
    mut v_x_1947_: *mut crate::leanh::LeanObject,
    mut v_x_1948_: *mut crate::leanh::LeanObject,
    mut v_x_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v_fst_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v_fst_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut v_a_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut v_val_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_a_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1947_) == 5 {
                    v_fn_1955_ = crate::leanh::lean_ctor_get(v_x_1947_, 0);
                    crate::leanh::lean_inc_ref(v_fn_1955_);
                    v_arg_1956_ = crate::leanh::lean_ctor_get(v_x_1947_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1956_);
                    crate::leanh::lean_dec_ref_known(v_x_1947_, 2);
                    v___x_1957_ = lean_array_set(v_x_1948_, v_x_1949_, v_arg_1956_);
                    v___x_1958_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1959_ = lean_nat_sub(v_x_1949_, v___x_1958_);
                    crate::leanh::lean_dec(v_x_1949_);
                    v_x_1947_ = v_fn_1955_;
                    v_x_1948_ = v___x_1957_;
                    v_x_1949_ = v___x_1959_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1949_);
                    v___x_1961_ = lean_array_get_size(v_x_1948_);
                    v___x_1962_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
                        v_x_1947_,
                        v___x_1961_,
                        v___y_1950_,
                        v___y_1951_,
                        v___y_1952_,
                        v___y_1953_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1962_) == 0 {
                        v_a_1963_ = crate::leanh::lean_ctor_get(v___x_1962_, 0);
                        crate::leanh::lean_inc(v_a_1963_);
                        crate::leanh::lean_dec_ref_known(v___x_1962_, 1);
                        v___x_1964_ = lean_array_get_size(v_a_1963_);
                        v___x_1965_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1966_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                        crate::leanh::lean_inc_ref(v_b_1946_);
                        v___x_1967_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_1964_, v_a_1963_, v_x_1948_, v_mode_1945_, v_b_1946_, v___x_1965_, v___x_1966_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
                        crate::leanh::lean_dec(v_a_1963_);
                        if crate::leanh::lean_obj_tag(v___x_1967_) == 0 {
                            v_a_1968_ = crate::leanh::lean_ctor_get(v___x_1967_, 0);
                            v_isSharedCheck_2001_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1967_)) as u8;
                            if v_isSharedCheck_2001_ == 0 {
                                v___x_1970_ = v___x_1967_;
                                v_isShared_1971_ = v_isSharedCheck_2001_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1968_);
                                crate::leanh::lean_dec(v___x_1967_);
                                v___x_1970_ = crate::leanh::lean_box(0);
                                v_isShared_1971_ = v_isSharedCheck_2001_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_x_1948_);
                            crate::leanh::lean_dec_ref(v_b_1946_);
                            v_a_2002_ = crate::leanh::lean_ctor_get(v___x_1967_, 0);
                            v_isSharedCheck_2009_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1967_)) as u8;
                            if v_isSharedCheck_2009_ == 0 {
                                v___x_2004_ = v___x_1967_;
                                v_isShared_2005_ = v_isSharedCheck_2009_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2002_);
                                crate::leanh::lean_dec(v___x_1967_);
                                v___x_2004_ = crate::leanh::lean_box(0);
                                v_isShared_2005_ = v_isSharedCheck_2009_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1948_);
                        crate::leanh::lean_dec_ref(v_b_1946_);
                        v_a_2010_ = crate::leanh::lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_2017_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_2017_ == 0 {
                            v___x_2012_ = v___x_1962_;
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2010_);
                            crate::leanh::lean_dec(v___x_1962_);
                            v___x_2012_ = crate::leanh::lean_box(0);
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1972_ = crate::leanh::lean_ctor_get(v_a_1968_, 0);
                crate::leanh::lean_inc(v_fst_1972_);
                crate::leanh::lean_dec(v_a_1968_);
                if crate::leanh::lean_obj_tag(v_fst_1972_) == 0 {
                    crate::leanh::lean_del_object(v___x_1970_);
                    v___x_1973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_1961_, v_x_1948_, v_mode_1945_, v_b_1946_, v___x_1964_, v___x_1966_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
                    crate::leanh::lean_dec_ref(v_x_1948_);
                    if crate::leanh::lean_obj_tag(v___x_1973_) == 0 {
                        v_a_1974_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                        v_isSharedCheck_1988_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1973_)) as u8;
                        if v_isSharedCheck_1988_ == 0 {
                            v___x_1976_ = v___x_1973_;
                            v_isShared_1977_ = v_isSharedCheck_1988_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1974_);
                            crate::leanh::lean_dec(v___x_1973_);
                            v___x_1976_ = crate::leanh::lean_box(0);
                            v_isShared_1977_ = v_isSharedCheck_1988_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1989_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                        v_isSharedCheck_1996_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1973_)) as u8;
                        if v_isSharedCheck_1996_ == 0 {
                            v___x_1991_ = v___x_1973_;
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1989_);
                            crate::leanh::lean_dec(v___x_1973_);
                            v___x_1991_ = crate::leanh::lean_box(0);
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1948_);
                    crate::leanh::lean_dec_ref(v_b_1946_);
                    v_val_1997_ = crate::leanh::lean_ctor_get(v_fst_1972_, 0);
                    crate::leanh::lean_inc(v_val_1997_);
                    crate::leanh::lean_dec_ref_known(v_fst_1972_, 1);
                    if v_isShared_1971_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1970_, 0, v_val_1997_);
                        v___x_1999_ = v___x_1970_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1997_);
                        v___x_1999_ = v_reuseFailAlloc_2000_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1978_ = crate::leanh::lean_ctor_get(v_a_1974_, 0);
                crate::leanh::lean_inc(v_fst_1978_);
                crate::leanh::lean_dec(v_a_1974_);
                if crate::leanh::lean_obj_tag(v_fst_1978_) == 0 {
                    v___x_1979_ = 1;
                    v___x_1980_ = crate::leanh::lean_box((v___x_1979_) as usize);
                    if v_isShared_1977_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1976_, 0, v___x_1980_);
                        v___x_1982_ = v___x_1976_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1983_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
                        v___x_1982_ = v_reuseFailAlloc_1983_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1984_ = crate::leanh::lean_ctor_get(v_fst_1978_, 0);
                    crate::leanh::lean_inc(v_val_1984_);
                    crate::leanh::lean_dec_ref_known(v_fst_1978_, 1);
                    if v_isShared_1977_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1976_, 0, v_val_1984_);
                        v___x_1986_ = v___x_1976_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_val_1984_);
                        v___x_1986_ = v_reuseFailAlloc_1987_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1982_;
            }
            4 => {
                return v___x_1986_;
            }
            5 => {
                if v_isShared_1992_ == 0 {
                    v___x_1994_ = v___x_1991_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
                    v___x_1994_ = v_reuseFailAlloc_1995_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1994_;
            }
            7 => {
                return v___x_1999_;
            }
            8 => {
                if v_isShared_2005_ == 0 {
                    v___x_2007_ = v___x_2004_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2007_;
            }
            10 => {
                if v_isShared_2013_ == 0 {
                    v___x_2015_ = v___x_2012_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
                    v___x_2015_ = v_reuseFailAlloc_2016_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(
    mut v_mode_2018_: u8,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
    mut v_b_2020_: *mut crate::leanh::LeanObject,
    mut v_a_2021_: *mut crate::leanh::LeanObject,
    mut v_a_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_2019_) {
                11 => {
                    v_struct_2037_ = crate::leanh::lean_ctor_get(v_a_2019_, 2);
                    crate::leanh::lean_inc_ref(v_struct_2037_);
                    crate::leanh::lean_dec_ref_known(v_a_2019_, 3);
                    v___x_2038_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_2018_,
                        v_struct_2037_,
                        v_b_2020_,
                        v_a_2021_,
                        v_a_2022_,
                        v_a_2023_,
                        v_a_2024_,
                    );
                    return v___x_2038_;
                }
                5 => {
                    v_dummy_2039_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
                    v_nargs_2040_ = l_Lean_Expr_getAppNumArgs(v_a_2019_);
                    crate::leanh::lean_inc(v_nargs_2040_);
                    v___x_2041_ = lean_mk_array(v_nargs_2040_, v_dummy_2039_);
                    v___x_2042_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2043_ = lean_nat_sub(v_nargs_2040_, v___x_2042_);
                    crate::leanh::lean_dec(v_nargs_2040_);
                    v___x_2044_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_2018_, v_b_2020_, v_a_2019_, v___x_2041_, v___x_2043_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
                    return v___x_2044_;
                }
                6 => {
                    v_binderType_2045_ = crate::leanh::lean_ctor_get(v_a_2019_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_2045_);
                    v_body_2046_ = crate::leanh::lean_ctor_get(v_a_2019_, 2);
                    crate::leanh::lean_inc_ref(v_body_2046_);
                    crate::leanh::lean_dec_ref_known(v_a_2019_, 3);
                    v_d_2027_ = v_binderType_2045_;
                    v_e_2028_ = v_body_2046_;
                    v___y_2029_ = v_a_2021_;
                    v___y_2030_ = v_a_2022_;
                    v___y_2031_ = v_a_2023_;
                    v___y_2032_ = v_a_2024_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_binderType_2047_ = crate::leanh::lean_ctor_get(v_a_2019_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_2047_);
                    v_body_2048_ = crate::leanh::lean_ctor_get(v_a_2019_, 2);
                    crate::leanh::lean_inc_ref(v_body_2048_);
                    crate::leanh::lean_dec_ref_known(v_a_2019_, 3);
                    v_d_2027_ = v_binderType_2047_;
                    v_e_2028_ = v_body_2048_;
                    v___y_2029_ = v_a_2021_;
                    v___y_2030_ = v_a_2022_;
                    v___y_2031_ = v_a_2023_;
                    v___y_2032_ = v_a_2024_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_value_2049_ = crate::leanh::lean_ctor_get(v_a_2019_, 2);
                    crate::leanh::lean_inc_ref(v_value_2049_);
                    v_body_2050_ = crate::leanh::lean_ctor_get(v_a_2019_, 3);
                    crate::leanh::lean_inc_ref(v_body_2050_);
                    crate::leanh::lean_dec_ref_known(v_a_2019_, 4);
                    crate::leanh::lean_inc_ref(v_b_2020_);
                    v___x_2051_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_2018_,
                        v_value_2049_,
                        v_b_2020_,
                        v_a_2021_,
                        v_a_2022_,
                        v_a_2023_,
                        v_a_2024_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2051_) == 0 {
                        v_a_2052_ = crate::leanh::lean_ctor_get(v___x_2051_, 0);
                        crate::leanh::lean_inc(v_a_2052_);
                        v___x_2053_ = (crate::leanh::lean_unbox(v_a_2052_) as u8);
                        crate::leanh::lean_dec(v_a_2052_);
                        if v___x_2053_ == 0 {
                            crate::leanh::lean_dec_ref(v_body_2050_);
                            crate::leanh::lean_dec_ref(v_b_2020_);
                            return v___x_2051_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2051_, 1);
                            v___x_2054_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                                v_mode_2018_,
                                v_body_2050_,
                                v_b_2020_,
                                v_a_2021_,
                                v_a_2022_,
                                v_a_2023_,
                                v_a_2024_,
                            );
                            return v___x_2054_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_2050_);
                        crate::leanh::lean_dec_ref(v_b_2020_);
                        return v___x_2051_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_b_2020_);
                    crate::leanh::lean_dec_ref(v_a_2019_);
                    v___x_2055_ = 1;
                    v___x_2056_ = crate::leanh::lean_box((v___x_2055_) as usize);
                    v___x_2057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2057_, 0, v___x_2056_);
                    return v___x_2057_;
                }
            },
            1 => {
                crate::leanh::lean_inc_ref(v_b_2020_);
                v___x_2033_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_2018_,
                    v_d_2027_,
                    v_b_2020_,
                    v___y_2029_,
                    v___y_2030_,
                    v___y_2031_,
                    v___y_2032_,
                );
                if crate::leanh::lean_obj_tag(v___x_2033_) == 0 {
                    v_a_2034_ = crate::leanh::lean_ctor_get(v___x_2033_, 0);
                    crate::leanh::lean_inc(v_a_2034_);
                    v___x_2035_ = (crate::leanh::lean_unbox(v_a_2034_) as u8);
                    crate::leanh::lean_dec(v_a_2034_);
                    if v___x_2035_ == 0 {
                        crate::leanh::lean_dec_ref(v_e_2028_);
                        crate::leanh::lean_dec_ref(v_b_2020_);
                        return v___x_2033_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2033_, 1);
                        v___x_2036_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_2018_,
                            v_e_2028_,
                            v_b_2020_,
                            v___y_2029_,
                            v___y_2030_,
                            v___y_2031_,
                            v___y_2032_,
                        );
                        return v___x_2036_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2028_);
                    crate::leanh::lean_dec_ref(v_b_2020_);
                    return v___x_2033_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
    mut v_mode_2058_: u8,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
    mut v_b_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2082_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2066_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(
                    v_mode_2058_,
                    v_a_2059_,
                    v_b_2060_,
                    v_a_2061_,
                    v_a_2062_,
                    v_a_2063_,
                    v_a_2064_,
                );
                if crate::leanh::lean_obj_tag(v___x_2066_) == 0 {
                    v_a_2067_ = crate::leanh::lean_ctor_get(v___x_2066_, 0);
                    v_isSharedCheck_2082_ = (!crate::leanh::lean_is_exclusive(v___x_2066_)) as u8;
                    if v_isSharedCheck_2082_ == 0 {
                        v___x_2069_ = v___x_2066_;
                        v_isShared_2070_ = v_isSharedCheck_2082_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2067_);
                        crate::leanh::lean_dec(v___x_2066_);
                        v___x_2069_ = crate::leanh::lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2082_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2066_;
                }
            }
            1 => {
                v___x_2071_ = (crate::leanh::lean_unbox(v_a_2067_) as u8);
                crate::leanh::lean_dec(v_a_2067_);
                if v___x_2071_ == 0 {
                    v___x_2072_ = 1;
                    v___x_2073_ = crate::leanh::lean_box((v___x_2072_) as usize);
                    if v_isShared_2070_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2069_, 0, v___x_2073_);
                        v___x_2075_ = v___x_2069_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
                        v___x_2075_ = v_reuseFailAlloc_2076_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2077_ = 0;
                    v___x_2078_ = crate::leanh::lean_box((v___x_2077_) as usize);
                    if v_isShared_2070_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2069_, 0, v___x_2078_);
                        v___x_2080_ = v___x_2069_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2081_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
                        v___x_2080_ = v_reuseFailAlloc_2081_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2075_;
            }
            3 => {
                return v___x_2080_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(
    mut v_mode_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
    mut v_b_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
    mut v_a_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
    mut v_a_2090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2091_: u8 = 0;
    let mut v_res_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2091_ = (crate::leanh::lean_unbox(v_mode_2083_) as u8);
    v_res_2092_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
        v_mode_boxed_2091_,
        v_a_2084_,
        v_b_2085_,
        v_a_2086_,
        v_a_2087_,
        v_a_2088_,
        v_a_2089_,
    );
    crate::leanh::lean_dec(v_a_2089_);
    crate::leanh::lean_dec_ref(v_a_2088_);
    crate::leanh::lean_dec(v_a_2087_);
    crate::leanh::lean_dec_ref(v_a_2086_);
    return v_res_2092_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(
    mut v_mode_2093_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_2094_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_2095_: *mut crate::leanh::LeanObject,
    mut v_b_u2081_2096_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2103_: u8 = 0;
    let mut v_res_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2103_ = (crate::leanh::lean_unbox(v_mode_2093_) as u8);
    v_res_2104_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(
        v_mode_boxed_2103_,
        v_a_u2081_2094_,
        v_a_u2082_2095_,
        v_b_u2081_2096_,
        v_b_u2082_2097_,
        v_a_2098_,
        v_a_2099_,
        v_a_2100_,
        v_a_2101_,
    );
    crate::leanh::lean_dec(v_a_2101_);
    crate::leanh::lean_dec_ref(v_a_2100_);
    crate::leanh::lean_dec(v_a_2099_);
    crate::leanh::lean_dec_ref(v_a_2098_);
    return v_res_2104_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(
    mut v_upperBound_2105_: *mut crate::leanh::LeanObject,
    mut v_args_2106_: *mut crate::leanh::LeanObject,
    mut v_mode_2107_: *mut crate::leanh::LeanObject,
    mut v_b_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_b_2110_: *mut crate::leanh::LeanObject,
    mut v___y_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2116_: u8 = 0;
    let mut v_res_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2116_ = (crate::leanh::lean_unbox(v_mode_2107_) as u8);
    v_res_2117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_2105_, v_args_2106_, v_mode_boxed_2116_, v_b_2108_, v_a_2109_, v_b_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
    crate::leanh::lean_dec(v___y_2114_);
    crate::leanh::lean_dec_ref(v___y_2113_);
    crate::leanh::lean_dec(v___y_2112_);
    crate::leanh::lean_dec_ref(v___y_2111_);
    crate::leanh::lean_dec_ref(v_args_2106_);
    crate::leanh::lean_dec(v_upperBound_2105_);
    return v_res_2117_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(
    mut v_mode_2118_: *mut crate::leanh::LeanObject,
    mut v_a_2119_: *mut crate::leanh::LeanObject,
    mut v_b_2120_: *mut crate::leanh::LeanObject,
    mut v_a_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_a_2123_: *mut crate::leanh::LeanObject,
    mut v_a_2124_: *mut crate::leanh::LeanObject,
    mut v_a_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2126_: u8 = 0;
    let mut v_res_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2126_ = (crate::leanh::lean_unbox(v_mode_2118_) as u8);
    v_res_2127_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
        v_mode_boxed_2126_,
        v_a_2119_,
        v_b_2120_,
        v_a_2121_,
        v_a_2122_,
        v_a_2123_,
        v_a_2124_,
    );
    crate::leanh::lean_dec(v_a_2124_);
    crate::leanh::lean_dec_ref(v_a_2123_);
    crate::leanh::lean_dec(v_a_2122_);
    crate::leanh::lean_dec_ref(v_a_2121_);
    return v_res_2127_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(
    mut v_upperBound_2128_: *mut crate::leanh::LeanObject,
    mut v_a_2129_: *mut crate::leanh::LeanObject,
    mut v_args_2130_: *mut crate::leanh::LeanObject,
    mut v_mode_2131_: *mut crate::leanh::LeanObject,
    mut v_b_2132_: *mut crate::leanh::LeanObject,
    mut v_a_2133_: *mut crate::leanh::LeanObject,
    mut v_b_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2140_: u8 = 0;
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2140_ = (crate::leanh::lean_unbox(v_mode_2131_) as u8);
    v_res_2141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_2128_, v_a_2129_, v_args_2130_, v_mode_boxed_2140_, v_b_2132_, v_a_2133_, v_b_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
    crate::leanh::lean_dec(v___y_2138_);
    crate::leanh::lean_dec_ref(v___y_2137_);
    crate::leanh::lean_dec(v___y_2136_);
    crate::leanh::lean_dec_ref(v___y_2135_);
    crate::leanh::lean_dec_ref(v_args_2130_);
    crate::leanh::lean_dec_ref(v_a_2129_);
    crate::leanh::lean_dec(v_upperBound_2128_);
    return v_res_2141_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(
    mut v_mode_2142_: *mut crate::leanh::LeanObject,
    mut v_a_2143_: *mut crate::leanh::LeanObject,
    mut v_b_2144_: *mut crate::leanh::LeanObject,
    mut v_a_2145_: *mut crate::leanh::LeanObject,
    mut v_a_2146_: *mut crate::leanh::LeanObject,
    mut v_a_2147_: *mut crate::leanh::LeanObject,
    mut v_a_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2150_: u8 = 0;
    let mut v_res_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2150_ = (crate::leanh::lean_unbox(v_mode_2142_) as u8);
    v_res_2151_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(
        v_mode_boxed_2150_,
        v_a_2143_,
        v_b_2144_,
        v_a_2145_,
        v_a_2146_,
        v_a_2147_,
        v_a_2148_,
    );
    crate::leanh::lean_dec(v_a_2148_);
    crate::leanh::lean_dec_ref(v_a_2147_);
    crate::leanh::lean_dec(v_a_2146_);
    crate::leanh::lean_dec_ref(v_a_2145_);
    return v_res_2151_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(
    mut v_mode_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
    mut v_b_2154_: *mut crate::leanh::LeanObject,
    mut v_a_2155_: *mut crate::leanh::LeanObject,
    mut v_a_2156_: *mut crate::leanh::LeanObject,
    mut v_a_2157_: *mut crate::leanh::LeanObject,
    mut v_a_2158_: *mut crate::leanh::LeanObject,
    mut v_a_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2160_: u8 = 0;
    let mut v_res_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2160_ = (crate::leanh::lean_unbox(v_mode_2152_) as u8);
    v_res_2161_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(
        v_mode_boxed_2160_,
        v_a_2153_,
        v_b_2154_,
        v_a_2155_,
        v_a_2156_,
        v_a_2157_,
        v_a_2158_,
    );
    crate::leanh::lean_dec(v_a_2158_);
    crate::leanh::lean_dec_ref(v_a_2157_);
    crate::leanh::lean_dec(v_a_2156_);
    crate::leanh::lean_dec_ref(v_a_2155_);
    return v_res_2161_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(
    mut v_upperBound_2162_: *mut crate::leanh::LeanObject,
    mut v___x_2163_: *mut crate::leanh::LeanObject,
    mut v___x_2164_: *mut crate::leanh::LeanObject,
    mut v_mode_2165_: *mut crate::leanh::LeanObject,
    mut v_a_2166_: *mut crate::leanh::LeanObject,
    mut v_b_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2173_: u8 = 0;
    let mut v_res_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2173_ = (crate::leanh::lean_unbox(v_mode_2165_) as u8);
    v_res_2174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_2162_, v___x_2163_, v___x_2164_, v_mode_boxed_2173_, v_a_2166_, v_b_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
    crate::leanh::lean_dec(v___y_2171_);
    crate::leanh::lean_dec_ref(v___y_2170_);
    crate::leanh::lean_dec(v___y_2169_);
    crate::leanh::lean_dec_ref(v___y_2168_);
    crate::leanh::lean_dec_ref(v___x_2164_);
    crate::leanh::lean_dec_ref(v___x_2163_);
    crate::leanh::lean_dec(v_upperBound_2162_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(
    mut v_mode_2175_: *mut crate::leanh::LeanObject,
    mut v_b_2176_: *mut crate::leanh::LeanObject,
    mut v_x_2177_: *mut crate::leanh::LeanObject,
    mut v_x_2178_: *mut crate::leanh::LeanObject,
    mut v_x_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2185_: u8 = 0;
    let mut v_res_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2185_ = (crate::leanh::lean_unbox(v_mode_2175_) as u8);
    v_res_2186_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_2185_, v_b_2176_, v_x_2177_, v_x_2178_, v_x_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
    crate::leanh::lean_dec(v___y_2183_);
    crate::leanh::lean_dec_ref(v___y_2182_);
    crate::leanh::lean_dec(v___y_2181_);
    crate::leanh::lean_dec_ref(v___y_2180_);
    return v_res_2186_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(
    mut v_upperBound_2187_: *mut crate::leanh::LeanObject,
    mut v_a_2188_: *mut crate::leanh::LeanObject,
    mut v___x_2189_: *mut crate::leanh::LeanObject,
    mut v___x_2190_: *mut crate::leanh::LeanObject,
    mut v_mode_2191_: *mut crate::leanh::LeanObject,
    mut v_a_2192_: *mut crate::leanh::LeanObject,
    mut v_b_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v___y_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2199_: u8 = 0;
    let mut v_res_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2199_ = (crate::leanh::lean_unbox(v_mode_2191_) as u8);
    v_res_2200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_2187_, v_a_2188_, v___x_2189_, v___x_2190_, v_mode_boxed_2199_, v_a_2192_, v_b_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
    crate::leanh::lean_dec(v___y_2197_);
    crate::leanh::lean_dec_ref(v___y_2196_);
    crate::leanh::lean_dec(v___y_2195_);
    crate::leanh::lean_dec_ref(v___y_2194_);
    crate::leanh::lean_dec_ref(v___x_2190_);
    crate::leanh::lean_dec_ref(v___x_2189_);
    crate::leanh::lean_dec_ref(v_a_2188_);
    crate::leanh::lean_dec(v_upperBound_2187_);
    return v_res_2200_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(
    mut v_mode_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_b_2203_: *mut crate::leanh::LeanObject,
    mut v_a_2204_: *mut crate::leanh::LeanObject,
    mut v_a_2205_: *mut crate::leanh::LeanObject,
    mut v_a_2206_: *mut crate::leanh::LeanObject,
    mut v_a_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2209_: u8 = 0;
    let mut v_res_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2209_ = (crate::leanh::lean_unbox(v_mode_2201_) as u8);
    v_res_2210_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(
        v_mode_boxed_2209_,
        v_a_2202_,
        v_b_2203_,
        v_a_2204_,
        v_a_2205_,
        v_a_2206_,
        v_a_2207_,
    );
    crate::leanh::lean_dec(v_a_2207_);
    crate::leanh::lean_dec_ref(v_a_2206_);
    crate::leanh::lean_dec(v_a_2205_);
    crate::leanh::lean_dec_ref(v_a_2204_);
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(
    mut v_mode_2211_: *mut crate::leanh::LeanObject,
    mut v_a_2212_: *mut crate::leanh::LeanObject,
    mut v_b_2213_: *mut crate::leanh::LeanObject,
    mut v_a_2214_: *mut crate::leanh::LeanObject,
    mut v_a_2215_: *mut crate::leanh::LeanObject,
    mut v_a_2216_: *mut crate::leanh::LeanObject,
    mut v_a_2217_: *mut crate::leanh::LeanObject,
    mut v_a_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2219_: u8 = 0;
    let mut v_res_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2219_ = (crate::leanh::lean_unbox(v_mode_2211_) as u8);
    v_res_2220_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(
        v_mode_boxed_2219_,
        v_a_2212_,
        v_b_2213_,
        v_a_2214_,
        v_a_2215_,
        v_a_2216_,
        v_a_2217_,
    );
    crate::leanh::lean_dec(v_a_2217_);
    crate::leanh::lean_dec_ref(v_a_2216_);
    crate::leanh::lean_dec(v_a_2215_);
    crate::leanh::lean_dec_ref(v_a_2214_);
    return v_res_2220_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(
    mut v_upperBound_2221_: *mut crate::leanh::LeanObject,
    mut v___x_2222_: *mut crate::leanh::LeanObject,
    mut v___x_2223_: *mut crate::leanh::LeanObject,
    mut v_mode_2224_: u8,
    mut v_inst_2225_: *mut crate::leanh::LeanObject,
    mut v_R_2226_: *mut crate::leanh::LeanObject,
    mut v_a_2227_: *mut crate::leanh::LeanObject,
    mut v_b_2228_: *mut crate::leanh::LeanObject,
    mut v_c_2229_: *mut crate::leanh::LeanObject,
    mut v___y_2230_: *mut crate::leanh::LeanObject,
    mut v___y_2231_: *mut crate::leanh::LeanObject,
    mut v___y_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_2221_, v___x_2222_, v___x_2223_, v_mode_2224_, v_a_2227_, v_b_2228_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
    return v___x_2235_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(
    mut v_upperBound_2236_: *mut crate::leanh::LeanObject,
    mut v___x_2237_: *mut crate::leanh::LeanObject,
    mut v___x_2238_: *mut crate::leanh::LeanObject,
    mut v_mode_2239_: *mut crate::leanh::LeanObject,
    mut v_inst_2240_: *mut crate::leanh::LeanObject,
    mut v_R_2241_: *mut crate::leanh::LeanObject,
    mut v_a_2242_: *mut crate::leanh::LeanObject,
    mut v_b_2243_: *mut crate::leanh::LeanObject,
    mut v_c_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2250_: u8 = 0;
    let mut v_res_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2250_ = (crate::leanh::lean_unbox(v_mode_2239_) as u8);
    v_res_2251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_2236_, v___x_2237_, v___x_2238_, v_mode_boxed_2250_, v_inst_2240_, v_R_2241_, v_a_2242_, v_b_2243_, v_c_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
    crate::leanh::lean_dec(v___y_2248_);
    crate::leanh::lean_dec_ref(v___y_2247_);
    crate::leanh::lean_dec(v___y_2246_);
    crate::leanh::lean_dec_ref(v___y_2245_);
    crate::leanh::lean_dec_ref(v___x_2238_);
    crate::leanh::lean_dec_ref(v___x_2237_);
    crate::leanh::lean_dec(v_upperBound_2236_);
    return v_res_2251_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(
    mut v_upperBound_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v___x_2254_: *mut crate::leanh::LeanObject,
    mut v___x_2255_: *mut crate::leanh::LeanObject,
    mut v_mode_2256_: u8,
    mut v_inst_2257_: *mut crate::leanh::LeanObject,
    mut v_R_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
    mut v_b_2260_: *mut crate::leanh::LeanObject,
    mut v_c_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_2252_, v_a_2253_, v___x_2254_, v___x_2255_, v_mode_2256_, v_a_2259_, v_b_2260_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
    return v___x_2267_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(
    mut v_upperBound_2268_: *mut crate::leanh::LeanObject,
    mut v_a_2269_: *mut crate::leanh::LeanObject,
    mut v___x_2270_: *mut crate::leanh::LeanObject,
    mut v___x_2271_: *mut crate::leanh::LeanObject,
    mut v_mode_2272_: *mut crate::leanh::LeanObject,
    mut v_inst_2273_: *mut crate::leanh::LeanObject,
    mut v_R_2274_: *mut crate::leanh::LeanObject,
    mut v_a_2275_: *mut crate::leanh::LeanObject,
    mut v_b_2276_: *mut crate::leanh::LeanObject,
    mut v_c_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2283_: u8 = 0;
    let mut v_res_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2283_ = (crate::leanh::lean_unbox(v_mode_2272_) as u8);
    v_res_2284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_2268_, v_a_2269_, v___x_2270_, v___x_2271_, v_mode_boxed_2283_, v_inst_2273_, v_R_2274_, v_a_2275_, v_b_2276_, v_c_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
    crate::leanh::lean_dec(v___y_2281_);
    crate::leanh::lean_dec_ref(v___y_2280_);
    crate::leanh::lean_dec(v___y_2279_);
    crate::leanh::lean_dec_ref(v___y_2278_);
    crate::leanh::lean_dec_ref(v___x_2271_);
    crate::leanh::lean_dec_ref(v___x_2270_);
    crate::leanh::lean_dec_ref(v_a_2269_);
    crate::leanh::lean_dec(v_upperBound_2268_);
    return v_res_2284_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(
    mut v_upperBound_2285_: *mut crate::leanh::LeanObject,
    mut v_args_2286_: *mut crate::leanh::LeanObject,
    mut v_mode_2287_: u8,
    mut v_b_2288_: *mut crate::leanh::LeanObject,
    mut v_inst_2289_: *mut crate::leanh::LeanObject,
    mut v_R_2290_: *mut crate::leanh::LeanObject,
    mut v_a_2291_: *mut crate::leanh::LeanObject,
    mut v_b_2292_: *mut crate::leanh::LeanObject,
    mut v_c_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_2285_, v_args_2286_, v_mode_2287_, v_b_2288_, v_a_2291_, v_b_2292_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
    return v___x_2299_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(
    mut v_upperBound_2300_: *mut crate::leanh::LeanObject,
    mut v_args_2301_: *mut crate::leanh::LeanObject,
    mut v_mode_2302_: *mut crate::leanh::LeanObject,
    mut v_b_2303_: *mut crate::leanh::LeanObject,
    mut v_inst_2304_: *mut crate::leanh::LeanObject,
    mut v_R_2305_: *mut crate::leanh::LeanObject,
    mut v_a_2306_: *mut crate::leanh::LeanObject,
    mut v_b_2307_: *mut crate::leanh::LeanObject,
    mut v_c_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2314_: u8 = 0;
    let mut v_res_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2314_ = (crate::leanh::lean_unbox(v_mode_2302_) as u8);
    v_res_2315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_2300_, v_args_2301_, v_mode_boxed_2314_, v_b_2303_, v_inst_2304_, v_R_2305_, v_a_2306_, v_b_2307_, v_c_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    crate::leanh::lean_dec(v___y_2312_);
    crate::leanh::lean_dec_ref(v___y_2311_);
    crate::leanh::lean_dec(v___y_2310_);
    crate::leanh::lean_dec_ref(v___y_2309_);
    crate::leanh::lean_dec_ref(v_args_2301_);
    crate::leanh::lean_dec(v_upperBound_2300_);
    return v_res_2315_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(
    mut v_upperBound_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_args_2318_: *mut crate::leanh::LeanObject,
    mut v_mode_2319_: u8,
    mut v_b_2320_: *mut crate::leanh::LeanObject,
    mut v_inst_2321_: *mut crate::leanh::LeanObject,
    mut v_R_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
    mut v_b_2324_: *mut crate::leanh::LeanObject,
    mut v_c_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2331_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_2316_, v_a_2317_, v_args_2318_, v_mode_2319_, v_b_2320_, v_a_2323_, v_b_2324_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
    return v___x_2331_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(
    mut v_upperBound_2332_: *mut crate::leanh::LeanObject,
    mut v_a_2333_: *mut crate::leanh::LeanObject,
    mut v_args_2334_: *mut crate::leanh::LeanObject,
    mut v_mode_2335_: *mut crate::leanh::LeanObject,
    mut v_b_2336_: *mut crate::leanh::LeanObject,
    mut v_inst_2337_: *mut crate::leanh::LeanObject,
    mut v_R_2338_: *mut crate::leanh::LeanObject,
    mut v_a_2339_: *mut crate::leanh::LeanObject,
    mut v_b_2340_: *mut crate::leanh::LeanObject,
    mut v_c_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2347_: u8 = 0;
    let mut v_res_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2347_ = (crate::leanh::lean_unbox(v_mode_2335_) as u8);
    v_res_2348_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_2332_, v_a_2333_, v_args_2334_, v_mode_boxed_2347_, v_b_2336_, v_inst_2337_, v_R_2338_, v_a_2339_, v_b_2340_, v_c_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
    crate::leanh::lean_dec(v___y_2345_);
    crate::leanh::lean_dec_ref(v___y_2344_);
    crate::leanh::lean_dec(v___y_2343_);
    crate::leanh::lean_dec_ref(v___y_2342_);
    crate::leanh::lean_dec_ref(v_args_2334_);
    crate::leanh::lean_dec_ref(v_a_2333_);
    crate::leanh::lean_dec(v_upperBound_2332_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_Meta_ACLt_main(
    mut v_a_2349_: *mut crate::leanh::LeanObject,
    mut v_b_2350_: *mut crate::leanh::LeanObject,
    mut v_mode_2351_: u8,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
    mut v_a_2353_: *mut crate::leanh::LeanObject,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
    mut v_a_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2357_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
        v_mode_2351_,
        v_a_2349_,
        v_b_2350_,
        v_a_2352_,
        v_a_2353_,
        v_a_2354_,
        v_a_2355_,
    );
    return v___x_2357_;
}
pub unsafe fn l_Lean_Meta_ACLt_main___boxed(
    mut v_a_2358_: *mut crate::leanh::LeanObject,
    mut v_b_2359_: *mut crate::leanh::LeanObject,
    mut v_mode_2360_: *mut crate::leanh::LeanObject,
    mut v_a_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_a_2363_: *mut crate::leanh::LeanObject,
    mut v_a_2364_: *mut crate::leanh::LeanObject,
    mut v_a_2365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2366_: u8 = 0;
    let mut v_res_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2366_ = (crate::leanh::lean_unbox(v_mode_2360_) as u8);
    v_res_2367_ = l_Lean_Meta_ACLt_main(
        v_a_2358_,
        v_b_2359_,
        v_mode_boxed_2366_,
        v_a_2361_,
        v_a_2362_,
        v_a_2363_,
        v_a_2364_,
    );
    crate::leanh::lean_dec(v_a_2364_);
    crate::leanh::lean_dec_ref(v_a_2363_);
    crate::leanh::lean_dec(v_a_2362_);
    crate::leanh::lean_dec_ref(v_a_2361_);
    return v_res_2367_;
}
pub unsafe fn l_Lean_Meta_acLt(
    mut v_a_2368_: *mut crate::leanh::LeanObject,
    mut v_b_2369_: *mut crate::leanh::LeanObject,
    mut v_mode_2370_: u8,
    mut v_a_2371_: *mut crate::leanh::LeanObject,
    mut v_a_2372_: *mut crate::leanh::LeanObject,
    mut v_a_2373_: *mut crate::leanh::LeanObject,
    mut v_a_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
        v_mode_2370_,
        v_a_2368_,
        v_b_2369_,
        v_a_2371_,
        v_a_2372_,
        v_a_2373_,
        v_a_2374_,
    );
    return v___x_2376_;
}
pub unsafe fn l_Lean_Meta_acLt___boxed(
    mut v_a_2377_: *mut crate::leanh::LeanObject,
    mut v_b_2378_: *mut crate::leanh::LeanObject,
    mut v_mode_2379_: *mut crate::leanh::LeanObject,
    mut v_a_2380_: *mut crate::leanh::LeanObject,
    mut v_a_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mode_boxed_2385_: u8 = 0;
    let mut v_res_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2385_ = (crate::leanh::lean_unbox(v_mode_2379_) as u8);
    v_res_2386_ = l_Lean_Meta_acLt(
        v_a_2377_,
        v_b_2378_,
        v_mode_boxed_2385_,
        v_a_2380_,
        v_a_2381_,
        v_a_2382_,
        v_a_2383_,
    );
    crate::leanh::lean_dec(v_a_2383_);
    crate::leanh::lean_dec_ref(v_a_2382_);
    crate::leanh::lean_dec(v_a_2381_);
    crate::leanh::lean_dec_ref(v_a_2380_);
    return v_res_2386_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ACLt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_DiscrTree_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config =
        _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config();
    crate::leanh::lean_mark_persistent(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ACLt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ACLt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_DiscrTree_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ACLt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ACLt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_ACLt(builtin);
}
