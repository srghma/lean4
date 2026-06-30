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
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut leanh::LeanObject,
        72058693566333441 as *mut leanh::LeanObject,
        65793 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0_value:
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
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6_value:
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
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5_value:
    leanh::LeanStringObject<58> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Expr_ctorWeight(mut v_x_1194_: *mut leanh::LeanObject) -> u8 {
    match leanh::lean_obj_tag(v_x_1194_) {
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
    mut v_x_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1208_: u8 = 0;
    let mut v_r_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1208_ = l_Lean_Expr_ctorWeight(v_x_1207_);
    leanh::lean_dec_ref(v_x_1207_);
    v_r_1209_ = leanh::lean_box((v_res_1208_) as usize);
    return v_r_1209_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorIdx(
    mut v_x_1210_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1210_ {
        0 => {
            let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1211_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1211_;
        }
        1 => {
            let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1212_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1212_;
        }
        _ => {
            let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1213_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1213_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorIdx___boxed(
    mut v_x_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1215_: u8 = 0;
    let mut v_res_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1215_ = (leanh::lean_unbox(v_x_1214_) as u8);
    v_res_1216_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx(v_x_boxed_1215_);
    return v_res_1216_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(
    mut v_x_1217_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1218_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx(v_x_1217_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_toCtorIdx___boxed(
    mut v_x_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_1220_: u8 = 0;
    let mut v_res_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1220_ = (leanh::lean_unbox(v_x_1219_) as u8);
    v_res_1221_ = l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(v_x_4__boxed_1220_);
    return v_res_1221_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(
    mut v_k_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1222_);
    return v_k_1222_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg___boxed(
    mut v_k_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(v_k_1223_);
    leanh::lean_dec(v_k_1223_);
    return v_res_1224_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim(
    mut v_motive_1225_: *mut leanh::LeanObject,
    mut v_ctorIdx_1226_: *mut leanh::LeanObject,
    mut v_t_1227_: u8,
    mut v_h_1228_: *mut leanh::LeanObject,
    mut v_k_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1229_);
    return v_k_1229_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___boxed(
    mut v_motive_1230_: *mut leanh::LeanObject,
    mut v_ctorIdx_1231_: *mut leanh::LeanObject,
    mut v_t_1232_: *mut leanh::LeanObject,
    mut v_h_1233_: *mut leanh::LeanObject,
    mut v_k_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1235_: u8 = 0;
    let mut v_res_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1235_ = (leanh::lean_unbox(v_t_1232_) as u8);
    v_res_1236_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim(
        v_motive_1230_,
        v_ctorIdx_1231_,
        v_t_boxed_1235_,
        v_h_1233_,
        v_k_1234_,
    );
    leanh::lean_dec(v_k_1234_);
    leanh::lean_dec(v_ctorIdx_1231_);
    return v_res_1236_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(
    mut v_reduce_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_reduce_1237_);
    return v_reduce_1237_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg___boxed(
    mut v_reduce_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(v_reduce_1238_);
    leanh::lean_dec(v_reduce_1238_);
    return v_res_1239_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim(
    mut v_motive_1240_: *mut leanh::LeanObject,
    mut v_t_1241_: u8,
    mut v_h_1242_: *mut leanh::LeanObject,
    mut v_reduce_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_reduce_1243_);
    return v_reduce_1243_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___boxed(
    mut v_motive_1244_: *mut leanh::LeanObject,
    mut v_t_1245_: *mut leanh::LeanObject,
    mut v_h_1246_: *mut leanh::LeanObject,
    mut v_reduce_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1248_: u8 = 0;
    let mut v_res_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1248_ = (leanh::lean_unbox(v_t_1245_) as u8);
    v_res_1249_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim(
        v_motive_1244_,
        v_t_boxed_1248_,
        v_h_1246_,
        v_reduce_1247_,
    );
    leanh::lean_dec(v_reduce_1247_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(
    mut v_reduceSimpleOnly_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_reduceSimpleOnly_1250_);
    return v_reduceSimpleOnly_1250_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg___boxed(
    mut v_reduceSimpleOnly_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1252_ =
        l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(v_reduceSimpleOnly_1251_);
    leanh::lean_dec(v_reduceSimpleOnly_1251_);
    return v_res_1252_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(
    mut v_motive_1253_: *mut leanh::LeanObject,
    mut v_t_1254_: u8,
    mut v_h_1255_: *mut leanh::LeanObject,
    mut v_reduceSimpleOnly_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_reduceSimpleOnly_1256_);
    return v_reduceSimpleOnly_1256_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___boxed(
    mut v_motive_1257_: *mut leanh::LeanObject,
    mut v_t_1258_: *mut leanh::LeanObject,
    mut v_h_1259_: *mut leanh::LeanObject,
    mut v_reduceSimpleOnly_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1261_: u8 = 0;
    let mut v_res_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1261_ = (leanh::lean_unbox(v_t_1258_) as u8);
    v_res_1262_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(
        v_motive_1257_,
        v_t_boxed_1261_,
        v_h_1259_,
        v_reduceSimpleOnly_1260_,
    );
    leanh::lean_dec(v_reduceSimpleOnly_1260_);
    return v_res_1262_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(
    mut v_none_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_none_1263_);
    return v_none_1263_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg___boxed(
    mut v_none_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(v_none_1264_);
    leanh::lean_dec(v_none_1264_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim(
    mut v_motive_1266_: *mut leanh::LeanObject,
    mut v_t_1267_: u8,
    mut v_h_1268_: *mut leanh::LeanObject,
    mut v_none_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_none_1269_);
    return v_none_1269_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___boxed(
    mut v_motive_1270_: *mut leanh::LeanObject,
    mut v_t_1271_: *mut leanh::LeanObject,
    mut v_h_1272_: *mut leanh::LeanObject,
    mut v_none_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1274_: u8 = 0;
    let mut v_res_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1274_ = (leanh::lean_unbox(v_t_1271_) as u8);
    v_res_1275_ = l_Lean_Meta_ACLt_ReduceMode_none_elim(
        v_motive_1270_,
        v_t_boxed_1274_,
        v_h_1272_,
        v_none_1273_,
    );
    leanh::lean_dec(v_none_1273_);
    return v_res_1275_;
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0;
    v___x_1283_ = l_Lean_Meta_Config_toConfigWithKey(v___x_1282_);
    return v___x_1283_;
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config()
-> *mut leanh::LeanObject {
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = leanh::lean_obj_once(
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
    mut v_e_1286_: *mut leanh::LeanObject,
    mut v_a_1287_: *mut leanh::LeanObject,
    mut v_a_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1292_: u8 = 0;
    v___x_1292_ = l_Lean_Expr_hasLooseBVars(v_e_1286_);
    if v___x_1292_ == 0 {
        match v_mode_1285_ {
            0 => {
                let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1293_ = l_Lean_Meta_DiscrTree_reduce(
                    v_e_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_,
                );
                return v___x_1293_;
            }
            1 => {
                let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_config_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_trackZetaDelta_1296_: u8 = 0;
                let mut v_zetaDeltaSet_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_lctx_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_localInstances_1299_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_defEqCtx_x3f_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_synthPendingDepth_1301_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_canUnfold_x3f_1302_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_univApprox_1303_: u8 = 0;
                let mut v_inTypeClassResolution_1304_: u8 = 0;
                let mut v_cacheInferType_1305_: u8 = 0;
                let mut v___x_1306_: u64 = 0;
                let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1294_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
                v_config_1295_ = leanh::lean_ctor_get(v___x_1294_, 0);
                v_trackZetaDelta_1296_ = leanh::lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1297_ = leanh::lean_ctor_get(v_a_1287_, 1);
                v_lctx_1298_ = leanh::lean_ctor_get(v_a_1287_, 2);
                v_localInstances_1299_ = leanh::lean_ctor_get(v_a_1287_, 3);
                v_defEqCtx_x3f_1300_ = leanh::lean_ctor_get(v_a_1287_, 4);
                v_synthPendingDepth_1301_ = leanh::lean_ctor_get(v_a_1287_, 5);
                v_canUnfold_x3f_1302_ = leanh::lean_ctor_get(v_a_1287_, 6);
                v_univApprox_1303_ = leanh::lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1304_ = leanh::lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1305_ = leanh::lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1306_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1295_);
                leanh::lean_inc_ref(v_config_1295_);
                v___x_1307_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_1307_, 0, v_config_1295_);
                leanh::lean_ctor_set_uint64(
                    v___x_1307_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1306_,
                );
                leanh::lean_inc(v_canUnfold_x3f_1302_);
                leanh::lean_inc(v_synthPendingDepth_1301_);
                leanh::lean_inc(v_defEqCtx_x3f_1300_);
                leanh::lean_inc_ref(v_localInstances_1299_);
                leanh::lean_inc_ref(v_lctx_1298_);
                leanh::lean_inc(v_zetaDeltaSet_1297_);
                v___x_1308_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_1308_, 0, v___x_1307_);
                leanh::lean_ctor_set(v___x_1308_, 1, v_zetaDeltaSet_1297_);
                leanh::lean_ctor_set(v___x_1308_, 2, v_lctx_1298_);
                leanh::lean_ctor_set(v___x_1308_, 3, v_localInstances_1299_);
                leanh::lean_ctor_set(v___x_1308_, 4, v_defEqCtx_x3f_1300_);
                leanh::lean_ctor_set(v___x_1308_, 5, v_synthPendingDepth_1301_);
                leanh::lean_ctor_set(v___x_1308_, 6, v_canUnfold_x3f_1302_);
                leanh::lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1296_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1303_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1304_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1305_,
                );
                v___x_1309_ = l_Lean_Meta_DiscrTree_reduce(
                    v_e_1286_,
                    v___x_1308_,
                    v_a_1288_,
                    v_a_1289_,
                    v_a_1290_,
                );
                leanh::lean_dec_ref_known(v___x_1308_, 7);
                return v___x_1309_;
            }
            _ => {
                let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1310_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1310_, 0, v_e_1286_);
                return v___x_1310_;
            }
        }
    } else {
        let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1311_, 0, v_e_1286_);
        return v___x_1311_;
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(
    mut v_mode_1312_: *mut leanh::LeanObject,
    mut v_e_1313_: *mut leanh::LeanObject,
    mut v_a_1314_: *mut leanh::LeanObject,
    mut v_a_1315_: *mut leanh::LeanObject,
    mut v_a_1316_: *mut leanh::LeanObject,
    mut v_a_1317_: *mut leanh::LeanObject,
    mut v_a_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_1319_: u8 = 0;
    let mut v_res_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_1319_ = (leanh::lean_unbox(v_mode_1312_) as u8);
    v_res_1320_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(
        v_mode_boxed_1319_,
        v_e_1313_,
        v_a_1314_,
        v_a_1315_,
        v_a_1316_,
        v_a_1317_,
    );
    leanh::lean_dec(v_a_1317_);
    leanh::lean_dec_ref(v_a_1316_);
    leanh::lean_dec(v_a_1315_);
    leanh::lean_dec_ref(v_a_1314_);
    return v_res_1320_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
    mut v_f_1323_: *mut leanh::LeanObject,
    mut v_numArgs_1324_: *mut leanh::LeanObject,
    mut v_a_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
    mut v_a_1327_: *mut leanh::LeanObject,
    mut v_a_1328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1335_: u8 = 0;
    let mut v_paramInfo_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut v_a_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    if leanh::lean_obj_tag(v___x_1331_) == 0 {
                        v_a_1332_ = leanh::lean_ctor_get(v___x_1331_, 0);
                        v_isSharedCheck_1340_ =
                            (!leanh::lean_is_exclusive(v___x_1331_)) as u8;
                        if v_isSharedCheck_1340_ == 0 {
                            v___x_1334_ = v___x_1331_;
                            v_isShared_1335_ = v_isSharedCheck_1340_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1332_);
                            leanh::lean_dec(v___x_1331_);
                            v___x_1334_ = leanh::lean_box(0);
                            v_isShared_1335_ = v_isSharedCheck_1340_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1341_ = leanh::lean_ctor_get(v___x_1331_, 0);
                        v_isSharedCheck_1348_ =
                            (!leanh::lean_is_exclusive(v___x_1331_)) as u8;
                        if v_isSharedCheck_1348_ == 0 {
                            v___x_1343_ = v___x_1331_;
                            v_isShared_1344_ = v_isSharedCheck_1348_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1341_);
                            leanh::lean_dec(v___x_1331_);
                            v___x_1343_ = leanh::lean_box(0);
                            v_isShared_1344_ = v_isSharedCheck_1348_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_numArgs_1324_);
                    leanh::lean_dec_ref(v_f_1323_);
                    v___x_1349_ =
                        l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0;
                    v___x_1350_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1350_, 0, v___x_1349_);
                    return v___x_1350_;
                }
            }
            1 => {
                v_paramInfo_1336_ = leanh::lean_ctor_get(v_a_1332_, 0);
                leanh::lean_inc_ref(v_paramInfo_1336_);
                leanh::lean_dec(v_a_1332_);
                if v_isShared_1335_ == 0 {
                    leanh::lean_ctor_set(v___x_1334_, 0, v_paramInfo_1336_);
                    v___x_1338_ = v___x_1334_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_paramInfo_1336_);
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
                    v_reuseFailAlloc_1347_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
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
    mut v_f_1351_: *mut leanh::LeanObject,
    mut v_numArgs_1352_: *mut leanh::LeanObject,
    mut v_a_1353_: *mut leanh::LeanObject,
    mut v_a_1354_: *mut leanh::LeanObject,
    mut v_a_1355_: *mut leanh::LeanObject,
    mut v_a_1356_: *mut leanh::LeanObject,
    mut v_a_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
        v_f_1351_,
        v_numArgs_1352_,
        v_a_1353_,
        v_a_1354_,
        v_a_1355_,
        v_a_1356_,
    );
    leanh::lean_dec(v_a_1356_);
    leanh::lean_dec_ref(v_a_1355_);
    leanh::lean_dec(v_a_1354_);
    leanh::lean_dec_ref(v_a_1353_);
    return v_res_1358_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(
    mut v_msg_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
    mut v___y_1362_: *mut leanh::LeanObject,
    mut v___y_1363_: *mut leanh::LeanObject,
    mut v___y_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_16292__overap_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1366_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0;
    v___x_16292__overap_1367_ = lean_panic_fn_borrowed(v___f_1366_, v_msg_1360_);
    leanh::lean_inc(v___y_1364_);
    leanh::lean_inc_ref(v___y_1363_);
    leanh::lean_inc(v___y_1362_);
    leanh::lean_inc_ref(v___y_1361_);
    v___x_1368_ = leanh::lean_apply_5(
        v___x_16292__overap_1367_,
        v___y_1361_,
        v___y_1362_,
        v___y_1363_,
        v___y_1364_,
        leanh::lean_box(0),
    );
    return v___x_1368_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(
    mut v_msg_1369_: *mut leanh::LeanObject,
    mut v___y_1370_: *mut leanh::LeanObject,
    mut v___y_1371_: *mut leanh::LeanObject,
    mut v___y_1372_: *mut leanh::LeanObject,
    mut v___y_1373_: *mut leanh::LeanObject,
    mut v___y_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ =
        l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(
            v_msg_1369_,
            v___y_1370_,
            v___y_1371_,
            v___y_1372_,
            v___y_1373_,
        );
    leanh::lean_dec(v___y_1373_);
    leanh::lean_dec_ref(v___y_1372_);
    leanh::lean_dec(v___y_1371_);
    leanh::lean_dec_ref(v___y_1370_);
    return v_res_1375_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(
    mut v_msg_1376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lean_instInhabitedLocalDecl_default;
    v___x_1378_ = lean_panic_fn_borrowed(v___x_1377_, v_msg_1376_);
    return v___x_1378_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(
    mut v_mode_1380_: u8,
    mut v_a_u2081_1381_: *mut leanh::LeanObject,
    mut v_a_u2082_1382_: *mut leanh::LeanObject,
    mut v_b_u2081_1383_: *mut leanh::LeanObject,
    mut v_b_u2082_1384_: *mut leanh::LeanObject,
    mut v_a_1385_: *mut leanh::LeanObject,
    mut v_a_1386_: *mut leanh::LeanObject,
    mut v_a_1387_: *mut leanh::LeanObject,
    mut v_a_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_b_u2081_1383_);
                leanh::lean_inc_ref(v_a_u2081_1381_);
                v___x_1390_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_1380_,
                    v_a_u2081_1381_,
                    v_b_u2081_1383_,
                    v_a_1385_,
                    v_a_1386_,
                    v_a_1387_,
                    v_a_1388_,
                );
                if leanh::lean_obj_tag(v___x_1390_) == 0 {
                    v_a_1391_ = leanh::lean_ctor_get(v___x_1390_, 0);
                    leanh::lean_inc(v_a_1391_);
                    v___x_1392_ = (leanh::lean_unbox(v_a_1391_) as u8);
                    if v___x_1392_ == 0 {
                        leanh::lean_dec_ref_known(v___x_1390_, 1);
                        v___x_1393_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1380_,
                            v_b_u2081_1383_,
                            v_a_u2081_1381_,
                            v_a_1385_,
                            v_a_1386_,
                            v_a_1387_,
                            v_a_1388_,
                        );
                        if leanh::lean_obj_tag(v___x_1393_) == 0 {
                            v_a_1394_ = leanh::lean_ctor_get(v___x_1393_, 0);
                            v_isSharedCheck_1403_ =
                                (!leanh::lean_is_exclusive(v___x_1393_)) as u8;
                            if v_isSharedCheck_1403_ == 0 {
                                v___x_1396_ = v___x_1393_;
                                v_isShared_1397_ = v_isSharedCheck_1403_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1394_);
                                leanh::lean_dec(v___x_1393_);
                                v___x_1396_ = leanh::lean_box(0);
                                v_isShared_1397_ = v_isSharedCheck_1403_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1391_);
                            leanh::lean_dec_ref(v_b_u2082_1384_);
                            leanh::lean_dec_ref(v_a_u2082_1382_);
                            return v___x_1393_;
                        }
                    } else {
                        leanh::lean_dec(v_a_1391_);
                        leanh::lean_dec_ref(v_b_u2082_1384_);
                        leanh::lean_dec_ref(v_b_u2081_1383_);
                        leanh::lean_dec_ref(v_a_u2082_1382_);
                        leanh::lean_dec_ref(v_a_u2081_1381_);
                        return v___x_1390_;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_u2082_1384_);
                    leanh::lean_dec_ref(v_b_u2081_1383_);
                    leanh::lean_dec_ref(v_a_u2082_1382_);
                    leanh::lean_dec_ref(v_a_u2081_1381_);
                    return v___x_1390_;
                }
            }
            1 => {
                v___x_1398_ = (leanh::lean_unbox(v_a_1394_) as u8);
                leanh::lean_dec(v_a_1394_);
                if v___x_1398_ == 0 {
                    leanh::lean_del_object(v___x_1396_);
                    leanh::lean_dec(v_a_1391_);
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
                    leanh::lean_dec_ref(v_b_u2082_1384_);
                    leanh::lean_dec_ref(v_a_u2082_1382_);
                    if v_isShared_1397_ == 0 {
                        leanh::lean_ctor_set(v___x_1396_, 0, v_a_1391_);
                        v___x_1401_ = v___x_1396_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1402_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1391_);
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
-> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2;
    v___x_1408_ = leanh::lean_unsigned_to_nat(14);
    v___x_1409_ = leanh::lean_unsigned_to_nat(22);
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
-> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = leanh::lean_box(0);
    v_dummy_1414_ = l_Lean_Expr_sort___override(v___x_1413_);
    return v_dummy_1414_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(
    mut v_upperBound_1418_: *mut leanh::LeanObject,
    mut v_a_1419_: *mut leanh::LeanObject,
    mut v___x_1420_: *mut leanh::LeanObject,
    mut v___x_1421_: *mut leanh::LeanObject,
    mut v_mode_1422_: u8,
    mut v_a_1423_: *mut leanh::LeanObject,
    mut v_b_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
    mut v___y_1426_: *mut leanh::LeanObject,
    mut v___y_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_1439_: u8 = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_a_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1470_: u8 = 0;
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1476_: u8 = 0;
    let mut v_a_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1435_ = lean_nat_dec_lt(v_a_1423_, v_upperBound_1418_);
                if v___x_1435_ == 0 {
                    leanh::lean_dec(v_a_1423_);
                    v___x_1436_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1436_, 0, v_b_1424_);
                    return v___x_1436_;
                } else {
                    leanh::lean_dec_ref(v_b_1424_);
                    v___x_1437_ = l_Lean_Meta_instInhabitedParamInfo_default;
                    v___x_1438_ = lean_array_get_borrowed(v___x_1437_, v_a_1419_, v_a_1423_);
                    v_isInstance_1439_ = leanh::lean_ctor_get_uint8(
                        v___x_1438_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 4) as u32,
                    );
                    v___x_1440_ = leanh::lean_box(0);
                    v___x_1441_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    if v_isInstance_1439_ == 0 {
                        v___x_1442_ = l_Lean_instInhabitedExpr;
                        v___x_1443_ = lean_array_get_borrowed(v___x_1442_, v___x_1420_, v_a_1423_);
                        v___x_1444_ = lean_array_get_borrowed(v___x_1442_, v___x_1421_, v_a_1423_);
                        leanh::lean_inc(v___x_1444_);
                        leanh::lean_inc(v___x_1443_);
                        v___x_1445_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1422_,
                            v___x_1443_,
                            v___x_1444_,
                            v___y_1425_,
                            v___y_1426_,
                            v___y_1427_,
                            v___y_1428_,
                        );
                        if leanh::lean_obj_tag(v___x_1445_) == 0 {
                            v_a_1446_ = leanh::lean_ctor_get(v___x_1445_, 0);
                            v_isSharedCheck_1476_ =
                                (!leanh::lean_is_exclusive(v___x_1445_)) as u8;
                            if v_isSharedCheck_1476_ == 0 {
                                v___x_1448_ = v___x_1445_;
                                v_isShared_1449_ = v_isSharedCheck_1476_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1446_);
                                leanh::lean_dec(v___x_1445_);
                                v___x_1448_ = leanh::lean_box(0);
                                v_isShared_1449_ = v_isSharedCheck_1476_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1423_);
                            v_a_1477_ = leanh::lean_ctor_get(v___x_1445_, 0);
                            v_isSharedCheck_1484_ =
                                (!leanh::lean_is_exclusive(v___x_1445_)) as u8;
                            if v_isSharedCheck_1484_ == 0 {
                                v___x_1479_ = v___x_1445_;
                                v_isShared_1480_ = v_isSharedCheck_1484_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1477_);
                                leanh::lean_dec(v___x_1445_);
                                v___x_1479_ = leanh::lean_box(0);
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
                v___x_1432_ = leanh::lean_unsigned_to_nat(1);
                v___x_1433_ = lean_nat_add(v_a_1423_, v___x_1432_);
                leanh::lean_dec(v_a_1423_);
                leanh::lean_inc_ref(v_a_1431_);
                v_a_1423_ = v___x_1433_;
                v_b_1424_ = v_a_1431_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1450_ = (leanh::lean_unbox(v_a_1446_) as u8);
                if v___x_1450_ == 0 {
                    leanh::lean_del_object(v___x_1448_);
                    leanh::lean_inc(v___x_1443_);
                    leanh::lean_inc(v___x_1444_);
                    v___x_1451_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1422_,
                        v___x_1444_,
                        v___x_1443_,
                        v___y_1425_,
                        v___y_1426_,
                        v___y_1427_,
                        v___y_1428_,
                    );
                    if leanh::lean_obj_tag(v___x_1451_) == 0 {
                        v_a_1452_ = leanh::lean_ctor_get(v___x_1451_, 0);
                        v_isSharedCheck_1462_ =
                            (!leanh::lean_is_exclusive(v___x_1451_)) as u8;
                        if v_isSharedCheck_1462_ == 0 {
                            v___x_1454_ = v___x_1451_;
                            v_isShared_1455_ = v_isSharedCheck_1462_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1452_);
                            leanh::lean_dec(v___x_1451_);
                            v___x_1454_ = leanh::lean_box(0);
                            v_isShared_1455_ = v_isSharedCheck_1462_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1446_);
                        leanh::lean_dec(v_a_1423_);
                        v_a_1463_ = leanh::lean_ctor_get(v___x_1451_, 0);
                        v_isSharedCheck_1470_ =
                            (!leanh::lean_is_exclusive(v___x_1451_)) as u8;
                        if v_isSharedCheck_1470_ == 0 {
                            v___x_1465_ = v___x_1451_;
                            v_isShared_1466_ = v_isSharedCheck_1470_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1463_);
                            leanh::lean_dec(v___x_1451_);
                            v___x_1465_ = leanh::lean_box(0);
                            v_isShared_1466_ = v_isSharedCheck_1470_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1423_);
                    v___x_1471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1471_, 0, v_a_1446_);
                    v___x_1472_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                    leanh::lean_ctor_set(v___x_1472_, 1, v___x_1440_);
                    if v_isShared_1449_ == 0 {
                        leanh::lean_ctor_set(v___x_1448_, 0, v___x_1472_);
                        v___x_1474_ = v___x_1448_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1475_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
                        v___x_1474_ = v_reuseFailAlloc_1475_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1456_ = (leanh::lean_unbox(v_a_1452_) as u8);
                leanh::lean_dec(v_a_1452_);
                if v___x_1456_ == 0 {
                    leanh::lean_del_object(v___x_1454_);
                    leanh::lean_dec(v_a_1446_);
                    v_a_1431_ = v___x_1441_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_1423_);
                    v___x_1457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1457_, 0, v_a_1446_);
                    v___x_1458_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
                    leanh::lean_ctor_set(v___x_1458_, 1, v___x_1440_);
                    if v_isShared_1455_ == 0 {
                        leanh::lean_ctor_set(v___x_1454_, 0, v___x_1458_);
                        v___x_1460_ = v___x_1454_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1461_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
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
                    v_reuseFailAlloc_1469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
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
                    v_reuseFailAlloc_1483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
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
    mut v_upperBound_1485_: *mut leanh::LeanObject,
    mut v___x_1486_: *mut leanh::LeanObject,
    mut v___x_1487_: *mut leanh::LeanObject,
    mut v_mode_1488_: u8,
    mut v_a_1489_: *mut leanh::LeanObject,
    mut v_b_1490_: *mut leanh::LeanObject,
    mut v___y_1491_: *mut leanh::LeanObject,
    mut v___y_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
    mut v___y_1494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1496_: u8 = 0;
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1523_: u8 = 0;
    let mut v_a_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1537_: u8 = 0;
    let mut v_a_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1496_ = lean_nat_dec_lt(v_a_1489_, v_upperBound_1485_);
                if v___x_1496_ == 0 {
                    leanh::lean_dec(v_a_1489_);
                    v___x_1497_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1497_, 0, v_b_1490_);
                    return v___x_1497_;
                } else {
                    leanh::lean_dec_ref(v_b_1490_);
                    v___x_1498_ = l_Lean_instInhabitedExpr;
                    v___x_1499_ = lean_array_get_borrowed(v___x_1498_, v___x_1486_, v_a_1489_);
                    v___x_1500_ = lean_array_get_borrowed(v___x_1498_, v___x_1487_, v_a_1489_);
                    leanh::lean_inc(v___x_1500_);
                    leanh::lean_inc(v___x_1499_);
                    v___x_1501_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1488_,
                        v___x_1499_,
                        v___x_1500_,
                        v___y_1491_,
                        v___y_1492_,
                        v___y_1493_,
                        v___y_1494_,
                    );
                    if leanh::lean_obj_tag(v___x_1501_) == 0 {
                        v_a_1502_ = leanh::lean_ctor_get(v___x_1501_, 0);
                        v_isSharedCheck_1537_ =
                            (!leanh::lean_is_exclusive(v___x_1501_)) as u8;
                        if v_isSharedCheck_1537_ == 0 {
                            v___x_1504_ = v___x_1501_;
                            v_isShared_1505_ = v_isSharedCheck_1537_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1502_);
                            leanh::lean_dec(v___x_1501_);
                            v___x_1504_ = leanh::lean_box(0);
                            v_isShared_1505_ = v_isSharedCheck_1537_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1489_);
                        v_a_1538_ = leanh::lean_ctor_get(v___x_1501_, 0);
                        v_isSharedCheck_1545_ =
                            (!leanh::lean_is_exclusive(v___x_1501_)) as u8;
                        if v_isSharedCheck_1545_ == 0 {
                            v___x_1540_ = v___x_1501_;
                            v_isShared_1541_ = v_isSharedCheck_1545_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1538_);
                            leanh::lean_dec(v___x_1501_);
                            v___x_1540_ = leanh::lean_box(0);
                            v_isShared_1541_ = v_isSharedCheck_1545_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1506_ = leanh::lean_box(0);
                v___x_1507_ = (leanh::lean_unbox(v_a_1502_) as u8);
                if v___x_1507_ == 0 {
                    leanh::lean_del_object(v___x_1504_);
                    leanh::lean_inc(v___x_1499_);
                    leanh::lean_inc(v___x_1500_);
                    v___x_1508_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1488_,
                        v___x_1500_,
                        v___x_1499_,
                        v___y_1491_,
                        v___y_1492_,
                        v___y_1493_,
                        v___y_1494_,
                    );
                    if leanh::lean_obj_tag(v___x_1508_) == 0 {
                        v_a_1509_ = leanh::lean_ctor_get(v___x_1508_, 0);
                        v_isSharedCheck_1523_ =
                            (!leanh::lean_is_exclusive(v___x_1508_)) as u8;
                        if v_isSharedCheck_1523_ == 0 {
                            v___x_1511_ = v___x_1508_;
                            v_isShared_1512_ = v_isSharedCheck_1523_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1509_);
                            leanh::lean_dec(v___x_1508_);
                            v___x_1511_ = leanh::lean_box(0);
                            v_isShared_1512_ = v_isSharedCheck_1523_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1502_);
                        leanh::lean_dec(v_a_1489_);
                        v_a_1524_ = leanh::lean_ctor_get(v___x_1508_, 0);
                        v_isSharedCheck_1531_ =
                            (!leanh::lean_is_exclusive(v___x_1508_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1526_ = v___x_1508_;
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1524_);
                            leanh::lean_dec(v___x_1508_);
                            v___x_1526_ = leanh::lean_box(0);
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1489_);
                    v___x_1532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1532_, 0, v_a_1502_);
                    v___x_1533_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1533_, 0, v___x_1532_);
                    leanh::lean_ctor_set(v___x_1533_, 1, v___x_1506_);
                    if v_isShared_1505_ == 0 {
                        leanh::lean_ctor_set(v___x_1504_, 0, v___x_1533_);
                        v___x_1535_ = v___x_1504_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
                        v___x_1535_ = v_reuseFailAlloc_1536_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1513_ = (leanh::lean_unbox(v_a_1509_) as u8);
                leanh::lean_dec(v_a_1509_);
                if v___x_1513_ == 0 {
                    leanh::lean_del_object(v___x_1511_);
                    leanh::lean_dec(v_a_1502_);
                    v___x_1514_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    v___x_1515_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1516_ = lean_nat_add(v_a_1489_, v___x_1515_);
                    leanh::lean_dec(v_a_1489_);
                    v_a_1489_ = v___x_1516_;
                    v_b_1490_ = v___x_1514_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_1489_);
                    v___x_1518_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1518_, 0, v_a_1502_);
                    v___x_1519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1519_, 0, v___x_1518_);
                    leanh::lean_ctor_set(v___x_1519_, 1, v___x_1506_);
                    if v_isShared_1512_ == 0 {
                        leanh::lean_ctor_set(v___x_1511_, 0, v___x_1519_);
                        v___x_1521_ = v___x_1511_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1522_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
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
                    v_reuseFailAlloc_1530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
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
                    v_reuseFailAlloc_1544_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
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
    mut v_a_1547_: *mut leanh::LeanObject,
    mut v_b_1548_: *mut leanh::LeanObject,
    mut v_a_1549_: *mut leanh::LeanObject,
    mut v_a_1550_: *mut leanh::LeanObject,
    mut v_a_1551_: *mut leanh::LeanObject,
    mut v_a_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_aFn_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bFn_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v_dummy_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v_fst_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1595_: u8 = 0;
    let mut v_fst_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut v_a_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_val_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1617_: u8 = 0;
    let mut v_a_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_a_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1636_: u8 = 0;
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut v_unused_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1649_: u8 = 0;
    let mut v_unused_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aFn_1554_ = l_Lean_Expr_getAppFn(v_a_1547_);
                v_bFn_1555_ = l_Lean_Expr_getAppFn(v_b_1548_);
                leanh::lean_inc_ref(v_bFn_1555_);
                leanh::lean_inc_ref(v_aFn_1554_);
                v___x_1556_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_1546_,
                    v_aFn_1554_,
                    v_bFn_1555_,
                    v_a_1549_,
                    v_a_1550_,
                    v_a_1551_,
                    v_a_1552_,
                );
                if leanh::lean_obj_tag(v___x_1556_) == 0 {
                    v_a_1557_ = leanh::lean_ctor_get(v___x_1556_, 0);
                    v_isSharedCheck_1655_ = (!leanh::lean_is_exclusive(v___x_1556_)) as u8;
                    if v_isSharedCheck_1655_ == 0 {
                        v___x_1559_ = v___x_1556_;
                        v_isShared_1560_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1557_);
                        leanh::lean_dec(v___x_1556_);
                        v___x_1559_ = leanh::lean_box(0);
                        v_isShared_1560_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_bFn_1555_);
                    leanh::lean_dec_ref(v_aFn_1554_);
                    leanh::lean_dec_ref(v_b_1548_);
                    leanh::lean_dec_ref(v_a_1547_);
                    return v___x_1556_;
                }
            }
            1 => {
                v___x_1561_ = 1;
                v___x_1562_ = (leanh::lean_unbox(v_a_1557_) as u8);
                if v___x_1562_ == 0 {
                    leanh::lean_del_object(v___x_1559_);
                    leanh::lean_inc_ref(v_aFn_1554_);
                    v___x_1563_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1546_,
                        v_bFn_1555_,
                        v_aFn_1554_,
                        v_a_1549_,
                        v_a_1550_,
                        v_a_1551_,
                        v_a_1552_,
                    );
                    if leanh::lean_obj_tag(v___x_1563_) == 0 {
                        v_a_1564_ = leanh::lean_ctor_get(v___x_1563_, 0);
                        leanh::lean_inc(v_a_1564_);
                        v___x_1565_ = (leanh::lean_unbox(v_a_1564_) as u8);
                        if v___x_1565_ == 0 {
                            leanh::lean_dec(v_a_1557_);
                            v_dummy_1566_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
                            v_nargs_1567_ = l_Lean_Expr_getAppNumArgs(v_a_1547_);
                            leanh::lean_inc(v_nargs_1567_);
                            v___x_1568_ = lean_mk_array(v_nargs_1567_, v_dummy_1566_);
                            v___x_1569_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1570_ = lean_nat_sub(v_nargs_1567_, v___x_1569_);
                            leanh::lean_dec(v_nargs_1567_);
                            v___x_1571_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_a_1547_,
                                v___x_1568_,
                                v___x_1570_,
                            );
                            v_nargs_1572_ = l_Lean_Expr_getAppNumArgs(v_b_1548_);
                            leanh::lean_inc(v_nargs_1572_);
                            v___x_1573_ = lean_mk_array(v_nargs_1572_, v_dummy_1566_);
                            v___x_1574_ = lean_nat_sub(v_nargs_1572_, v___x_1569_);
                            leanh::lean_dec(v_nargs_1572_);
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
                                    leanh::lean_dec_ref_known(v___x_1563_, 1);
                                    v___x_1580_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_1554_, v___x_1576_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                                    if leanh::lean_obj_tag(v___x_1580_) == 0 {
                                        v_a_1581_ = leanh::lean_ctor_get(v___x_1580_, 0);
                                        leanh::lean_inc(v_a_1581_);
                                        leanh::lean_dec_ref_known(v___x_1580_, 1);
                                        v___x_1582_ = lean_array_get_size(v_a_1581_);
                                        v___x_1583_ = leanh::lean_unsigned_to_nat(0);
                                        v___x_1584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                                        v___x_1585_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_1582_, v_a_1581_, v___x_1571_, v___x_1575_, v_mode_1546_, v___x_1583_, v___x_1584_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                                        leanh::lean_dec(v_a_1581_);
                                        if leanh::lean_obj_tag(v___x_1585_) == 0 {
                                            v_a_1586_ = leanh::lean_ctor_get(v___x_1585_, 0);
                                            v_isSharedCheck_1617_ =
                                                (!leanh::lean_is_exclusive(v___x_1585_))
                                                    as u8;
                                            if v_isSharedCheck_1617_ == 0 {
                                                v___x_1588_ = v___x_1585_;
                                                v_isShared_1589_ = v_isSharedCheck_1617_;
                                                state = 2;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1586_);
                                                leanh::lean_dec(v___x_1585_);
                                                v___x_1588_ = leanh::lean_box(0);
                                                v_isShared_1589_ = v_isSharedCheck_1617_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_1575_);
                                            leanh::lean_dec_ref(v___x_1571_);
                                            leanh::lean_dec(v_a_1564_);
                                            v_a_1618_ = leanh::lean_ctor_get(v___x_1585_, 0);
                                            v_isSharedCheck_1625_ =
                                                (!leanh::lean_is_exclusive(v___x_1585_))
                                                    as u8;
                                            if v_isSharedCheck_1625_ == 0 {
                                                v___x_1620_ = v___x_1585_;
                                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                                state = 9;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1618_);
                                                leanh::lean_dec(v___x_1585_);
                                                v___x_1620_ = leanh::lean_box(0);
                                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_1575_);
                                        leanh::lean_dec_ref(v___x_1571_);
                                        leanh::lean_dec(v_a_1564_);
                                        v_a_1626_ = leanh::lean_ctor_get(v___x_1580_, 0);
                                        v_isSharedCheck_1633_ =
                                            (!leanh::lean_is_exclusive(v___x_1580_)) as u8;
                                        if v_isSharedCheck_1633_ == 0 {
                                            v___x_1628_ = v___x_1580_;
                                            v_isShared_1629_ = v_isSharedCheck_1633_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1626_);
                                            leanh::lean_dec(v___x_1580_);
                                            v___x_1628_ = leanh::lean_box(0);
                                            v_isShared_1629_ = v_isSharedCheck_1633_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_1575_);
                                    leanh::lean_dec_ref(v___x_1571_);
                                    leanh::lean_dec(v_a_1564_);
                                    leanh::lean_dec_ref(v_aFn_1554_);
                                    return v___x_1563_;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1575_);
                                leanh::lean_dec_ref(v___x_1571_);
                                leanh::lean_dec(v_a_1564_);
                                leanh::lean_dec_ref(v_aFn_1554_);
                                v_isSharedCheck_1641_ =
                                    (!leanh::lean_is_exclusive(v___x_1563_)) as u8;
                                if v_isSharedCheck_1641_ == 0 {
                                    v_unused_1642_ = leanh::lean_ctor_get(v___x_1563_, 0);
                                    leanh::lean_dec(v_unused_1642_);
                                    v___x_1635_ = v___x_1563_;
                                    v_isShared_1636_ = v_isSharedCheck_1641_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1563_);
                                    v___x_1635_ = leanh::lean_box(0);
                                    v_isShared_1636_ = v_isSharedCheck_1641_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1564_);
                            leanh::lean_dec_ref(v_aFn_1554_);
                            leanh::lean_dec_ref(v_b_1548_);
                            leanh::lean_dec_ref(v_a_1547_);
                            v_isSharedCheck_1649_ =
                                (!leanh::lean_is_exclusive(v___x_1563_)) as u8;
                            if v_isSharedCheck_1649_ == 0 {
                                v_unused_1650_ = leanh::lean_ctor_get(v___x_1563_, 0);
                                leanh::lean_dec(v_unused_1650_);
                                v___x_1644_ = v___x_1563_;
                                v_isShared_1645_ = v_isSharedCheck_1649_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1563_);
                                v___x_1644_ = leanh::lean_box(0);
                                v_isShared_1645_ = v_isSharedCheck_1649_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1557_);
                        leanh::lean_dec_ref(v_aFn_1554_);
                        leanh::lean_dec_ref(v_b_1548_);
                        leanh::lean_dec_ref(v_a_1547_);
                        return v___x_1563_;
                    }
                } else {
                    leanh::lean_dec(v_a_1557_);
                    leanh::lean_dec_ref(v_bFn_1555_);
                    leanh::lean_dec_ref(v_aFn_1554_);
                    leanh::lean_dec_ref(v_b_1548_);
                    leanh::lean_dec_ref(v_a_1547_);
                    v___x_1651_ = leanh::lean_box((v___x_1561_) as usize);
                    if v_isShared_1560_ == 0 {
                        leanh::lean_ctor_set(v___x_1559_, 0, v___x_1651_);
                        v___x_1653_ = v___x_1559_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1654_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
                        v___x_1653_ = v_reuseFailAlloc_1654_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1590_ = leanh::lean_ctor_get(v_a_1586_, 0);
                leanh::lean_inc(v_fst_1590_);
                leanh::lean_dec(v_a_1586_);
                if leanh::lean_obj_tag(v_fst_1590_) == 0 {
                    leanh::lean_del_object(v___x_1588_);
                    v___x_1591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_1576_, v___x_1571_, v___x_1575_, v_mode_1546_, v___x_1582_, v___x_1584_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                    leanh::lean_dec_ref(v___x_1575_);
                    leanh::lean_dec_ref(v___x_1571_);
                    if leanh::lean_obj_tag(v___x_1591_) == 0 {
                        v_a_1592_ = leanh::lean_ctor_get(v___x_1591_, 0);
                        v_isSharedCheck_1604_ =
                            (!leanh::lean_is_exclusive(v___x_1591_)) as u8;
                        if v_isSharedCheck_1604_ == 0 {
                            v___x_1594_ = v___x_1591_;
                            v_isShared_1595_ = v_isSharedCheck_1604_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1592_);
                            leanh::lean_dec(v___x_1591_);
                            v___x_1594_ = leanh::lean_box(0);
                            v_isShared_1595_ = v_isSharedCheck_1604_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1564_);
                        v_a_1605_ = leanh::lean_ctor_get(v___x_1591_, 0);
                        v_isSharedCheck_1612_ =
                            (!leanh::lean_is_exclusive(v___x_1591_)) as u8;
                        if v_isSharedCheck_1612_ == 0 {
                            v___x_1607_ = v___x_1591_;
                            v_isShared_1608_ = v_isSharedCheck_1612_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1605_);
                            leanh::lean_dec(v___x_1591_);
                            v___x_1607_ = leanh::lean_box(0);
                            v_isShared_1608_ = v_isSharedCheck_1612_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1575_);
                    leanh::lean_dec_ref(v___x_1571_);
                    leanh::lean_dec(v_a_1564_);
                    v_val_1613_ = leanh::lean_ctor_get(v_fst_1590_, 0);
                    leanh::lean_inc(v_val_1613_);
                    leanh::lean_dec_ref_known(v_fst_1590_, 1);
                    if v_isShared_1589_ == 0 {
                        leanh::lean_ctor_set(v___x_1588_, 0, v_val_1613_);
                        v___x_1615_ = v___x_1588_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1616_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_val_1613_);
                        v___x_1615_ = v_reuseFailAlloc_1616_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_1596_ = leanh::lean_ctor_get(v_a_1592_, 0);
                leanh::lean_inc(v_fst_1596_);
                leanh::lean_dec(v_a_1592_);
                if leanh::lean_obj_tag(v_fst_1596_) == 0 {
                    if v_isShared_1595_ == 0 {
                        leanh::lean_ctor_set(v___x_1594_, 0, v_a_1564_);
                        v___x_1598_ = v___x_1594_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1564_);
                        v___x_1598_ = v_reuseFailAlloc_1599_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1564_);
                    v_val_1600_ = leanh::lean_ctor_get(v_fst_1596_, 0);
                    leanh::lean_inc(v_val_1600_);
                    leanh::lean_dec_ref_known(v_fst_1596_, 1);
                    if v_isShared_1595_ == 0 {
                        leanh::lean_ctor_set(v___x_1594_, 0, v_val_1600_);
                        v___x_1602_ = v___x_1594_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1603_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
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
                    v_reuseFailAlloc_1611_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
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
                    v_reuseFailAlloc_1624_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
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
                    v_reuseFailAlloc_1632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
                    v___x_1631_ = v_reuseFailAlloc_1632_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1631_;
            }
            13 => {
                v___x_1637_ = leanh::lean_box((v___x_1561_) as usize);
                if v_isShared_1636_ == 0 {
                    leanh::lean_ctor_set(v___x_1635_, 0, v___x_1637_);
                    v___x_1639_ = v___x_1635_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
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
                    leanh::lean_ctor_set(v___x_1644_, 0, v_a_1557_);
                    v___x_1647_ = v___x_1644_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1648_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1557_);
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
-> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6;
    v___x_1660_ = leanh::lean_unsigned_to_nat(27);
    v___x_1661_ = leanh::lean_unsigned_to_nat(152);
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
    mut v_a_1666_: *mut leanh::LeanObject,
    mut v_b_1667_: *mut leanh::LeanObject,
    mut v_a_1668_: *mut leanh::LeanObject,
    mut v_a_1669_: *mut leanh::LeanObject,
    mut v_a_1670_: *mut leanh::LeanObject,
    mut v_a_1671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___y_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut v_a_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut v_mvarId_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_1666_) {
                0 => {
                    v_deBruijnIndex_1683_ = leanh::lean_ctor_get(v_a_1666_, 0);
                    leanh::lean_inc(v_deBruijnIndex_1683_);
                    leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1684_ = l_Lean_Expr_bvarIdx_x21(v_b_1667_);
                    leanh::lean_dec_ref(v_b_1667_);
                    v___x_1685_ = lean_nat_dec_lt(v_deBruijnIndex_1683_, v___x_1684_);
                    leanh::lean_dec(v___x_1684_);
                    leanh::lean_dec(v_deBruijnIndex_1683_);
                    v___x_1686_ = leanh::lean_box((v___x_1685_) as usize);
                    v___x_1687_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1687_, 0, v___x_1686_);
                    return v___x_1687_;
                }
                1 => {
                    v_fvarId_1688_ = leanh::lean_ctor_get(v_a_1666_, 0);
                    leanh::lean_inc(v_fvarId_1688_);
                    leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1689_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_1688_, v_a_1668_);
                    if leanh::lean_obj_tag(v___x_1689_) == 0 {
                        v_a_1690_ = leanh::lean_ctor_get(v___x_1689_, 0);
                        leanh::lean_inc(v_a_1690_);
                        leanh::lean_dec_ref_known(v___x_1689_, 1);
                        v___x_1691_ = l_Lean_Expr_fvarId_x21(v_b_1667_);
                        leanh::lean_dec_ref(v_b_1667_);
                        v___x_1692_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_1691_, v_a_1668_);
                        if leanh::lean_obj_tag(v___x_1692_) == 0 {
                            v_a_1693_ = leanh::lean_ctor_get(v___x_1692_, 0);
                            v_isSharedCheck_1715_ =
                                (!leanh::lean_is_exclusive(v___x_1692_)) as u8;
                            if v_isSharedCheck_1715_ == 0 {
                                v___x_1695_ = v___x_1692_;
                                v_isShared_1696_ = v_isSharedCheck_1715_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1693_);
                                leanh::lean_dec(v___x_1692_);
                                v___x_1695_ = leanh::lean_box(0);
                                v_isShared_1696_ = v_isSharedCheck_1715_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1690_);
                            v_a_1716_ = leanh::lean_ctor_get(v___x_1692_, 0);
                            v_isSharedCheck_1723_ =
                                (!leanh::lean_is_exclusive(v___x_1692_)) as u8;
                            if v_isSharedCheck_1723_ == 0 {
                                v___x_1718_ = v___x_1692_;
                                v_isShared_1719_ = v_isSharedCheck_1723_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1716_);
                                leanh::lean_dec(v___x_1692_);
                                v___x_1718_ = leanh::lean_box(0);
                                v_isShared_1719_ = v_isSharedCheck_1723_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_1667_);
                        v_a_1724_ = leanh::lean_ctor_get(v___x_1689_, 0);
                        v_isSharedCheck_1731_ =
                            (!leanh::lean_is_exclusive(v___x_1689_)) as u8;
                        if v_isSharedCheck_1731_ == 0 {
                            v___x_1726_ = v___x_1689_;
                            v_isShared_1727_ = v_isSharedCheck_1731_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1724_);
                            leanh::lean_dec(v___x_1689_);
                            v___x_1726_ = leanh::lean_box(0);
                            v_isShared_1727_ = v_isSharedCheck_1731_;
                            state = 8;
                            continue;
                        }
                    }
                }
                2 => {
                    v_mvarId_1732_ = leanh::lean_ctor_get(v_a_1666_, 0);
                    leanh::lean_inc(v_mvarId_1732_);
                    leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1733_ = l_Lean_Expr_mvarId_x21(v_b_1667_);
                    leanh::lean_dec_ref(v_b_1667_);
                    v___x_1734_ = l_Lean_Name_lt(v_mvarId_1732_, v___x_1733_);
                    leanh::lean_dec(v___x_1733_);
                    leanh::lean_dec(v_mvarId_1732_);
                    v___x_1735_ = leanh::lean_box((v___x_1734_) as usize);
                    v___x_1736_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1736_, 0, v___x_1735_);
                    return v___x_1736_;
                }
                3 => {
                    v_u_1737_ = leanh::lean_ctor_get(v_a_1666_, 0);
                    leanh::lean_inc(v_u_1737_);
                    leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1738_ = l_Lean_Expr_sortLevel_x21(v_b_1667_);
                    leanh::lean_dec_ref(v_b_1667_);
                    v___x_1739_ = l_Lean_Level_normLt(v_u_1737_, v___x_1738_);
                    leanh::lean_dec(v___x_1738_);
                    leanh::lean_dec(v_u_1737_);
                    v___x_1740_ = leanh::lean_box((v___x_1739_) as usize);
                    v___x_1741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1741_, 0, v___x_1740_);
                    return v___x_1741_;
                }
                4 => {
                    v_declName_1742_ = leanh::lean_ctor_get(v_a_1666_, 0);
                    leanh::lean_inc(v_declName_1742_);
                    leanh::lean_dec_ref_known(v_a_1666_, 2);
                    v___x_1743_ = l_Lean_Expr_constName_x21(v_b_1667_);
                    leanh::lean_dec_ref(v_b_1667_);
                    v___x_1744_ = l_Lean_Name_lt(v_declName_1742_, v___x_1743_);
                    leanh::lean_dec(v___x_1743_);
                    leanh::lean_dec(v_declName_1742_);
                    v___x_1745_ = leanh::lean_box((v___x_1744_) as usize);
                    v___x_1746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1746_, 0, v___x_1745_);
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
                    v_value_1748_ = leanh::lean_ctor_get(v_a_1666_, 2);
                    leanh::lean_inc_ref(v_value_1748_);
                    v_body_1749_ = leanh::lean_ctor_get(v_a_1666_, 3);
                    leanh::lean_inc_ref(v_body_1749_);
                    leanh::lean_dec_ref_known(v_a_1666_, 4);
                    v___x_1750_ = l_Lean_Expr_letValue_x21(v_b_1667_);
                    v___x_1751_ = l_Lean_Expr_letBody_x21(v_b_1667_);
                    leanh::lean_dec_ref(v_b_1667_);
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
                    v_a_1753_ = leanh::lean_ctor_get(v_a_1666_, 0);
                    leanh::lean_inc_ref(v_a_1753_);
                    leanh::lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1754_ = l_Lean_Expr_litValue_x21(v_b_1667_);
                    leanh::lean_dec_ref(v_b_1667_);
                    v___x_1755_ = l_Lean_Literal_lt(v_a_1753_, v___x_1754_);
                    leanh::lean_dec_ref(v___x_1754_);
                    leanh::lean_dec_ref(v_a_1753_);
                    v___x_1756_ = leanh::lean_box((v___x_1755_) as usize);
                    v___x_1757_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1757_, 0, v___x_1756_);
                    return v___x_1757_;
                }
                10 => {
                    leanh::lean_dec_ref_known(v_a_1666_, 2);
                    leanh::lean_dec_ref(v_b_1667_);
                    v___x_1758_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
                    v___x_1759_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_1758_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
                    return v___x_1759_;
                }
                11 => {
                    v_idx_1760_ = leanh::lean_ctor_get(v_a_1666_, 1);
                    leanh::lean_inc(v_idx_1760_);
                    v_struct_1761_ = leanh::lean_ctor_get(v_a_1666_, 2);
                    leanh::lean_inc_ref(v_struct_1761_);
                    leanh::lean_dec_ref_known(v_a_1666_, 3);
                    v___x_1762_ = l_Lean_Expr_projIdx_x21(v_b_1667_);
                    v___x_1763_ = lean_nat_dec_eq(v_idx_1760_, v___x_1762_);
                    if v___x_1763_ == 0 {
                        leanh::lean_dec_ref(v_struct_1761_);
                        leanh::lean_dec_ref(v_b_1667_);
                        v___x_1764_ = lean_nat_dec_lt(v_idx_1760_, v___x_1762_);
                        leanh::lean_dec(v___x_1762_);
                        leanh::lean_dec(v_idx_1760_);
                        v___x_1765_ = leanh::lean_box((v___x_1764_) as usize);
                        v___x_1766_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1766_, 0, v___x_1765_);
                        return v___x_1766_;
                    } else {
                        leanh::lean_dec(v___x_1762_);
                        leanh::lean_dec(v_idx_1760_);
                        v___x_1767_ = l_Lean_Expr_projExpr_x21(v_b_1667_);
                        leanh::lean_dec_ref(v_b_1667_);
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
                    v_binderType_1769_ = leanh::lean_ctor_get(v_a_1666_, 1);
                    leanh::lean_inc_ref(v_binderType_1769_);
                    v_body_1770_ = leanh::lean_ctor_get(v_a_1666_, 2);
                    leanh::lean_inc_ref(v_body_1770_);
                    leanh::lean_dec_ref(v_a_1666_);
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
                leanh::lean_dec_ref(v_b_1667_);
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
                if leanh::lean_obj_tag(v_a_1690_) == 0 {
                    v___x_1712_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
                    v___x_1713_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_1712_);
                    v___y_1707_ = v___x_1713_;
                    state = 5;
                    continue;
                } else {
                    v_val_1714_ = leanh::lean_ctor_get(v_a_1690_, 0);
                    leanh::lean_inc(v_val_1714_);
                    leanh::lean_dec_ref_known(v_a_1690_, 1);
                    v___y_1707_ = v_val_1714_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_1700_ = l_Lean_LocalDecl_index(v___y_1699_);
                leanh::lean_dec_ref(v___y_1699_);
                v___x_1701_ = lean_nat_dec_lt(v___y_1698_, v___x_1700_);
                leanh::lean_dec(v___x_1700_);
                leanh::lean_dec(v___y_1698_);
                v___x_1702_ = leanh::lean_box((v___x_1701_) as usize);
                if v_isShared_1696_ == 0 {
                    leanh::lean_ctor_set(v___x_1695_, 0, v___x_1702_);
                    v___x_1704_ = v___x_1695_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
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
                leanh::lean_dec_ref(v___y_1707_);
                if leanh::lean_obj_tag(v_a_1693_) == 0 {
                    v___x_1709_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
                    v___x_1710_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_1709_);
                    v___y_1698_ = v___x_1708_;
                    v___y_1699_ = v___x_1710_;
                    state = 3;
                    continue;
                } else {
                    v_val_1711_ = leanh::lean_ctor_get(v_a_1693_, 0);
                    leanh::lean_inc(v_val_1711_);
                    leanh::lean_dec_ref_known(v_a_1693_, 1);
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
                    v_reuseFailAlloc_1722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
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
                    v_reuseFailAlloc_1730_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
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
    mut v_a_1772_: *mut leanh::LeanObject,
    mut v_b_1773_: *mut leanh::LeanObject,
    mut v_a_1774_: *mut leanh::LeanObject,
    mut v_a_1775_: *mut leanh::LeanObject,
    mut v_a_1776_: *mut leanh::LeanObject,
    mut v_a_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1811_: u8 = 0;
    let mut v_unused_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1779_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0;
                v___x_1780_ = l_Lean_Core_checkSystem(v___x_1779_, v_a_1776_, v_a_1777_);
                if leanh::lean_obj_tag(v___x_1780_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1780_, 1);
                    leanh::lean_inc_ref(v_a_1772_);
                    leanh::lean_inc_ref(v_b_1773_);
                    v___x_1781_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
                        v_mode_1771_,
                        v_b_1773_,
                        v_a_1772_,
                        v_a_1774_,
                        v_a_1775_,
                        v_a_1776_,
                        v_a_1777_,
                    );
                    if leanh::lean_obj_tag(v___x_1781_) == 0 {
                        v_a_1782_ = leanh::lean_ctor_get(v___x_1781_, 0);
                        leanh::lean_inc(v_a_1782_);
                        v___x_1783_ = 1;
                        v___x_1784_ = (leanh::lean_unbox(v_a_1782_) as u8);
                        if v___x_1784_ == 0 {
                            v___x_1785_ = l_Lean_Expr_ctorWeight(v_b_1773_);
                            v___x_1786_ = l_Lean_Expr_ctorWeight(v_a_1772_);
                            v___x_1787_ = lean_uint8_dec_lt(v___x_1785_, v___x_1786_);
                            if v___x_1787_ == 0 {
                                leanh::lean_dec_ref_known(v___x_1781_, 1);
                                leanh::lean_inc_ref(v_b_1773_);
                                leanh::lean_inc_ref(v_a_1772_);
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
                                if leanh::lean_obj_tag(v___x_1788_) == 0 {
                                    v_a_1789_ = leanh::lean_ctor_get(v___x_1788_, 0);
                                    v_isSharedCheck_1803_ =
                                        (!leanh::lean_is_exclusive(v___x_1788_)) as u8;
                                    if v_isSharedCheck_1803_ == 0 {
                                        v___x_1791_ = v___x_1788_;
                                        v_isShared_1792_ = v_isSharedCheck_1803_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1789_);
                                        leanh::lean_dec(v___x_1788_);
                                        v___x_1791_ = leanh::lean_box(0);
                                        v_isShared_1792_ = v_isSharedCheck_1803_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1782_);
                                    leanh::lean_dec_ref(v_b_1773_);
                                    leanh::lean_dec_ref(v_a_1772_);
                                    return v___x_1788_;
                                }
                            } else {
                                leanh::lean_dec(v_a_1782_);
                                leanh::lean_dec_ref(v_b_1773_);
                                leanh::lean_dec_ref(v_a_1772_);
                                return v___x_1781_;
                            }
                        } else {
                            leanh::lean_dec(v_a_1782_);
                            leanh::lean_dec_ref(v_b_1773_);
                            leanh::lean_dec_ref(v_a_1772_);
                            v_isSharedCheck_1811_ =
                                (!leanh::lean_is_exclusive(v___x_1781_)) as u8;
                            if v_isSharedCheck_1811_ == 0 {
                                v_unused_1812_ = leanh::lean_ctor_get(v___x_1781_, 0);
                                leanh::lean_dec(v_unused_1812_);
                                v___x_1805_ = v___x_1781_;
                                v_isShared_1806_ = v_isSharedCheck_1811_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1781_);
                                v___x_1805_ = leanh::lean_box(0);
                                v_isShared_1806_ = v_isSharedCheck_1811_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_1773_);
                        leanh::lean_dec_ref(v_a_1772_);
                        return v___x_1781_;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_1773_);
                    leanh::lean_dec_ref(v_a_1772_);
                    v_a_1813_ = leanh::lean_ctor_get(v___x_1780_, 0);
                    v_isSharedCheck_1820_ = (!leanh::lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1815_ = v___x_1780_;
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1813_);
                        leanh::lean_dec(v___x_1780_);
                        v___x_1815_ = leanh::lean_box(0);
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1793_ = (leanh::lean_unbox(v_a_1789_) as u8);
                leanh::lean_dec(v_a_1789_);
                if v___x_1793_ == 0 {
                    leanh::lean_dec_ref(v_b_1773_);
                    leanh::lean_dec_ref(v_a_1772_);
                    if v_isShared_1792_ == 0 {
                        leanh::lean_ctor_set(v___x_1791_, 0, v_a_1782_);
                        v___x_1795_ = v___x_1791_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1796_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1782_);
                        v___x_1795_ = v_reuseFailAlloc_1796_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1782_);
                    v___x_1797_ = lean_uint8_dec_lt(v___x_1786_, v___x_1785_);
                    if v___x_1797_ == 0 {
                        leanh::lean_del_object(v___x_1791_);
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
                        leanh::lean_dec_ref(v_b_1773_);
                        leanh::lean_dec_ref(v_a_1772_);
                        v___x_1799_ = leanh::lean_box((v___x_1783_) as usize);
                        if v_isShared_1792_ == 0 {
                            leanh::lean_ctor_set(v___x_1791_, 0, v___x_1799_);
                            v___x_1801_ = v___x_1791_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1802_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
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
                v___x_1807_ = leanh::lean_box((v___x_1783_) as usize);
                if v_isShared_1806_ == 0 {
                    leanh::lean_ctor_set(v___x_1805_, 0, v___x_1807_);
                    v___x_1809_ = v___x_1805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1810_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
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
                    v_reuseFailAlloc_1819_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
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
    mut v_a_1822_: *mut leanh::LeanObject,
    mut v_b_1823_: *mut leanh::LeanObject,
    mut v_a_1824_: *mut leanh::LeanObject,
    mut v_a_1825_: *mut leanh::LeanObject,
    mut v_a_1826_: *mut leanh::LeanObject,
    mut v_a_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_a_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1852_: u8 = 0;
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                            if leanh::lean_obj_tag(v___x_1832_) == 0 {
                                v_a_1833_ = leanh::lean_ctor_get(v___x_1832_, 0);
                                leanh::lean_inc(v_a_1833_);
                                leanh::lean_dec_ref_known(v___x_1832_, 1);
                                v___x_1834_ =
                                    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(
                                        v_mode_1821_,
                                        v_b_1823_,
                                        v_a_1824_,
                                        v_a_1825_,
                                        v_a_1826_,
                                        v_a_1827_,
                                    );
                                if leanh::lean_obj_tag(v___x_1834_) == 0 {
                                    v_a_1835_ = leanh::lean_ctor_get(v___x_1834_, 0);
                                    leanh::lean_inc(v_a_1835_);
                                    leanh::lean_dec_ref_known(v___x_1834_, 1);
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
                                    leanh::lean_dec(v_a_1833_);
                                    v_a_1837_ = leanh::lean_ctor_get(v___x_1834_, 0);
                                    v_isSharedCheck_1844_ =
                                        (!leanh::lean_is_exclusive(v___x_1834_)) as u8;
                                    if v_isSharedCheck_1844_ == 0 {
                                        v___x_1839_ = v___x_1834_;
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1837_);
                                        leanh::lean_dec(v___x_1834_);
                                        v___x_1839_ = leanh::lean_box(0);
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_1823_);
                                v_a_1845_ = leanh::lean_ctor_get(v___x_1832_, 0);
                                v_isSharedCheck_1852_ =
                                    (!leanh::lean_is_exclusive(v___x_1832_)) as u8;
                                if v_isSharedCheck_1852_ == 0 {
                                    v___x_1847_ = v___x_1832_;
                                    v_isShared_1848_ = v_isSharedCheck_1852_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1845_);
                                    leanh::lean_dec(v___x_1832_);
                                    v___x_1847_ = leanh::lean_box(0);
                                    v_isShared_1848_ = v_isSharedCheck_1852_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_1853_ = l_Lean_Expr_mdataExpr_x21(v_b_1823_);
                            leanh::lean_dec_ref(v_b_1823_);
                            v_b_1823_ = v___x_1853_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1855_ = l_Lean_Expr_mdataExpr_x21(v_a_1822_);
                        leanh::lean_dec_ref(v_a_1822_);
                        v_a_1822_ = v___x_1855_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_1823_);
                    leanh::lean_dec_ref(v_a_1822_);
                    v___x_1857_ = 0;
                    v___x_1858_ = leanh::lean_box((v___x_1857_) as usize);
                    v___x_1859_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1859_, 0, v___x_1858_);
                    return v___x_1859_;
                }
            }
            1 => {
                if v_isShared_1840_ == 0 {
                    v___x_1842_ = v___x_1839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
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
                    v_reuseFailAlloc_1851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
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
    mut v_upperBound_1860_: *mut leanh::LeanObject,
    mut v_a_1861_: *mut leanh::LeanObject,
    mut v_args_1862_: *mut leanh::LeanObject,
    mut v_mode_1863_: u8,
    mut v_b_1864_: *mut leanh::LeanObject,
    mut v_a_1865_: *mut leanh::LeanObject,
    mut v_b_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
    mut v___y_1870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_1881_: u8 = 0;
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1891_: u8 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_a_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1877_ = lean_nat_dec_lt(v_a_1865_, v_upperBound_1860_);
                if v___x_1877_ == 0 {
                    leanh::lean_dec(v_a_1865_);
                    leanh::lean_dec_ref(v_b_1864_);
                    v___x_1878_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1878_, 0, v_b_1866_);
                    return v___x_1878_;
                } else {
                    leanh::lean_dec_ref(v_b_1866_);
                    v___x_1879_ = l_Lean_Meta_instInhabitedParamInfo_default;
                    v___x_1880_ = lean_array_get_borrowed(v___x_1879_, v_a_1861_, v_a_1865_);
                    v_isInstance_1881_ = leanh::lean_ctor_get_uint8(
                        v___x_1880_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 4) as u32,
                    );
                    v___x_1882_ = leanh::lean_box(0);
                    v___x_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    if v_isInstance_1881_ == 0 {
                        v___x_1884_ = l_Lean_instInhabitedExpr;
                        v___x_1885_ = lean_array_get_borrowed(v___x_1884_, v_args_1862_, v_a_1865_);
                        leanh::lean_inc_ref(v_b_1864_);
                        leanh::lean_inc(v___x_1885_);
                        v___x_1886_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1863_,
                            v___x_1885_,
                            v_b_1864_,
                            v___y_1867_,
                            v___y_1868_,
                            v___y_1869_,
                            v___y_1870_,
                        );
                        if leanh::lean_obj_tag(v___x_1886_) == 0 {
                            v_a_1887_ = leanh::lean_ctor_get(v___x_1886_, 0);
                            v_isSharedCheck_1897_ =
                                (!leanh::lean_is_exclusive(v___x_1886_)) as u8;
                            if v_isSharedCheck_1897_ == 0 {
                                v___x_1889_ = v___x_1886_;
                                v_isShared_1890_ = v_isSharedCheck_1897_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1887_);
                                leanh::lean_dec(v___x_1886_);
                                v___x_1889_ = leanh::lean_box(0);
                                v_isShared_1890_ = v_isSharedCheck_1897_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1865_);
                            leanh::lean_dec_ref(v_b_1864_);
                            v_a_1898_ = leanh::lean_ctor_get(v___x_1886_, 0);
                            v_isSharedCheck_1905_ =
                                (!leanh::lean_is_exclusive(v___x_1886_)) as u8;
                            if v_isSharedCheck_1905_ == 0 {
                                v___x_1900_ = v___x_1886_;
                                v_isShared_1901_ = v_isSharedCheck_1905_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1898_);
                                leanh::lean_dec(v___x_1886_);
                                v___x_1900_ = leanh::lean_box(0);
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
                v___x_1874_ = leanh::lean_unsigned_to_nat(1);
                v___x_1875_ = lean_nat_add(v_a_1865_, v___x_1874_);
                leanh::lean_dec(v_a_1865_);
                leanh::lean_inc_ref(v_a_1873_);
                v_a_1865_ = v___x_1875_;
                v_b_1866_ = v_a_1873_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1891_ = (leanh::lean_unbox(v_a_1887_) as u8);
                if v___x_1891_ == 0 {
                    leanh::lean_dec(v_a_1865_);
                    leanh::lean_dec_ref(v_b_1864_);
                    v___x_1892_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1892_, 0, v_a_1887_);
                    v___x_1893_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1893_, 0, v___x_1892_);
                    leanh::lean_ctor_set(v___x_1893_, 1, v___x_1882_);
                    if v_isShared_1890_ == 0 {
                        leanh::lean_ctor_set(v___x_1889_, 0, v___x_1893_);
                        v___x_1895_ = v___x_1889_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1896_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
                        v___x_1895_ = v_reuseFailAlloc_1896_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1889_);
                    leanh::lean_dec(v_a_1887_);
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
                    v_reuseFailAlloc_1904_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
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
    mut v_upperBound_1906_: *mut leanh::LeanObject,
    mut v_args_1907_: *mut leanh::LeanObject,
    mut v_mode_1908_: u8,
    mut v_b_1909_: *mut leanh::LeanObject,
    mut v_a_1910_: *mut leanh::LeanObject,
    mut v_b_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
    mut v___y_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v_a_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ = lean_nat_dec_lt(v_a_1910_, v_upperBound_1906_);
                if v___x_1917_ == 0 {
                    leanh::lean_dec(v_a_1910_);
                    leanh::lean_dec_ref(v_b_1909_);
                    v___x_1918_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1918_, 0, v_b_1911_);
                    return v___x_1918_;
                } else {
                    leanh::lean_dec_ref(v_b_1911_);
                    v___x_1919_ = lean_array_fget_borrowed(v_args_1907_, v_a_1910_);
                    leanh::lean_inc_ref(v_b_1909_);
                    leanh::lean_inc(v___x_1919_);
                    v___x_1920_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1908_,
                        v___x_1919_,
                        v_b_1909_,
                        v___y_1912_,
                        v___y_1913_,
                        v___y_1914_,
                        v___y_1915_,
                    );
                    if leanh::lean_obj_tag(v___x_1920_) == 0 {
                        v_a_1921_ = leanh::lean_ctor_get(v___x_1920_, 0);
                        v_isSharedCheck_1936_ =
                            (!leanh::lean_is_exclusive(v___x_1920_)) as u8;
                        if v_isSharedCheck_1936_ == 0 {
                            v___x_1923_ = v___x_1920_;
                            v_isShared_1924_ = v_isSharedCheck_1936_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1921_);
                            leanh::lean_dec(v___x_1920_);
                            v___x_1923_ = leanh::lean_box(0);
                            v_isShared_1924_ = v_isSharedCheck_1936_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1910_);
                        leanh::lean_dec_ref(v_b_1909_);
                        v_a_1937_ = leanh::lean_ctor_get(v___x_1920_, 0);
                        v_isSharedCheck_1944_ =
                            (!leanh::lean_is_exclusive(v___x_1920_)) as u8;
                        if v_isSharedCheck_1944_ == 0 {
                            v___x_1939_ = v___x_1920_;
                            v_isShared_1940_ = v_isSharedCheck_1944_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1937_);
                            leanh::lean_dec(v___x_1920_);
                            v___x_1939_ = leanh::lean_box(0);
                            v_isShared_1940_ = v_isSharedCheck_1944_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1925_ = leanh::lean_box(0);
                v___x_1926_ = (leanh::lean_unbox(v_a_1921_) as u8);
                if v___x_1926_ == 0 {
                    leanh::lean_dec(v_a_1910_);
                    leanh::lean_dec_ref(v_b_1909_);
                    v___x_1927_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1927_, 0, v_a_1921_);
                    v___x_1928_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1928_, 0, v___x_1927_);
                    leanh::lean_ctor_set(v___x_1928_, 1, v___x_1925_);
                    if v_isShared_1924_ == 0 {
                        leanh::lean_ctor_set(v___x_1923_, 0, v___x_1928_);
                        v___x_1930_ = v___x_1923_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1931_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                        v___x_1930_ = v_reuseFailAlloc_1931_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1923_);
                    leanh::lean_dec(v_a_1921_);
                    v___x_1932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    v___x_1933_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1934_ = lean_nat_add(v_a_1910_, v___x_1933_);
                    leanh::lean_dec(v_a_1910_);
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
                    v_reuseFailAlloc_1943_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
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
    mut v_b_1946_: *mut leanh::LeanObject,
    mut v_x_1947_: *mut leanh::LeanObject,
    mut v_x_1948_: *mut leanh::LeanObject,
    mut v_x_1949_: *mut leanh::LeanObject,
    mut v___y_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v_fst_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v_fst_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut v_a_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut v_val_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_a_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1947_) == 5 {
                    v_fn_1955_ = leanh::lean_ctor_get(v_x_1947_, 0);
                    leanh::lean_inc_ref(v_fn_1955_);
                    v_arg_1956_ = leanh::lean_ctor_get(v_x_1947_, 1);
                    leanh::lean_inc_ref(v_arg_1956_);
                    leanh::lean_dec_ref_known(v_x_1947_, 2);
                    v___x_1957_ = lean_array_set(v_x_1948_, v_x_1949_, v_arg_1956_);
                    v___x_1958_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1959_ = lean_nat_sub(v_x_1949_, v___x_1958_);
                    leanh::lean_dec(v_x_1949_);
                    v_x_1947_ = v_fn_1955_;
                    v_x_1948_ = v___x_1957_;
                    v_x_1949_ = v___x_1959_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_1949_);
                    v___x_1961_ = lean_array_get_size(v_x_1948_);
                    v___x_1962_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
                        v_x_1947_,
                        v___x_1961_,
                        v___y_1950_,
                        v___y_1951_,
                        v___y_1952_,
                        v___y_1953_,
                    );
                    if leanh::lean_obj_tag(v___x_1962_) == 0 {
                        v_a_1963_ = leanh::lean_ctor_get(v___x_1962_, 0);
                        leanh::lean_inc(v_a_1963_);
                        leanh::lean_dec_ref_known(v___x_1962_, 1);
                        v___x_1964_ = lean_array_get_size(v_a_1963_);
                        v___x_1965_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1966_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                        leanh::lean_inc_ref(v_b_1946_);
                        v___x_1967_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_1964_, v_a_1963_, v_x_1948_, v_mode_1945_, v_b_1946_, v___x_1965_, v___x_1966_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
                        leanh::lean_dec(v_a_1963_);
                        if leanh::lean_obj_tag(v___x_1967_) == 0 {
                            v_a_1968_ = leanh::lean_ctor_get(v___x_1967_, 0);
                            v_isSharedCheck_2001_ =
                                (!leanh::lean_is_exclusive(v___x_1967_)) as u8;
                            if v_isSharedCheck_2001_ == 0 {
                                v___x_1970_ = v___x_1967_;
                                v_isShared_1971_ = v_isSharedCheck_2001_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1968_);
                                leanh::lean_dec(v___x_1967_);
                                v___x_1970_ = leanh::lean_box(0);
                                v_isShared_1971_ = v_isSharedCheck_2001_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_x_1948_);
                            leanh::lean_dec_ref(v_b_1946_);
                            v_a_2002_ = leanh::lean_ctor_get(v___x_1967_, 0);
                            v_isSharedCheck_2009_ =
                                (!leanh::lean_is_exclusive(v___x_1967_)) as u8;
                            if v_isSharedCheck_2009_ == 0 {
                                v___x_2004_ = v___x_1967_;
                                v_isShared_2005_ = v_isSharedCheck_2009_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2002_);
                                leanh::lean_dec(v___x_1967_);
                                v___x_2004_ = leanh::lean_box(0);
                                v_isShared_2005_ = v_isSharedCheck_2009_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_1948_);
                        leanh::lean_dec_ref(v_b_1946_);
                        v_a_2010_ = leanh::lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_2017_ =
                            (!leanh::lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_2017_ == 0 {
                            v___x_2012_ = v___x_1962_;
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2010_);
                            leanh::lean_dec(v___x_1962_);
                            v___x_2012_ = leanh::lean_box(0);
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1972_ = leanh::lean_ctor_get(v_a_1968_, 0);
                leanh::lean_inc(v_fst_1972_);
                leanh::lean_dec(v_a_1968_);
                if leanh::lean_obj_tag(v_fst_1972_) == 0 {
                    leanh::lean_del_object(v___x_1970_);
                    v___x_1973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_1961_, v_x_1948_, v_mode_1945_, v_b_1946_, v___x_1964_, v___x_1966_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
                    leanh::lean_dec_ref(v_x_1948_);
                    if leanh::lean_obj_tag(v___x_1973_) == 0 {
                        v_a_1974_ = leanh::lean_ctor_get(v___x_1973_, 0);
                        v_isSharedCheck_1988_ =
                            (!leanh::lean_is_exclusive(v___x_1973_)) as u8;
                        if v_isSharedCheck_1988_ == 0 {
                            v___x_1976_ = v___x_1973_;
                            v_isShared_1977_ = v_isSharedCheck_1988_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1974_);
                            leanh::lean_dec(v___x_1973_);
                            v___x_1976_ = leanh::lean_box(0);
                            v_isShared_1977_ = v_isSharedCheck_1988_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1989_ = leanh::lean_ctor_get(v___x_1973_, 0);
                        v_isSharedCheck_1996_ =
                            (!leanh::lean_is_exclusive(v___x_1973_)) as u8;
                        if v_isSharedCheck_1996_ == 0 {
                            v___x_1991_ = v___x_1973_;
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1989_);
                            leanh::lean_dec(v___x_1973_);
                            v___x_1991_ = leanh::lean_box(0);
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1948_);
                    leanh::lean_dec_ref(v_b_1946_);
                    v_val_1997_ = leanh::lean_ctor_get(v_fst_1972_, 0);
                    leanh::lean_inc(v_val_1997_);
                    leanh::lean_dec_ref_known(v_fst_1972_, 1);
                    if v_isShared_1971_ == 0 {
                        leanh::lean_ctor_set(v___x_1970_, 0, v_val_1997_);
                        v___x_1999_ = v___x_1970_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1997_);
                        v___x_1999_ = v_reuseFailAlloc_2000_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1978_ = leanh::lean_ctor_get(v_a_1974_, 0);
                leanh::lean_inc(v_fst_1978_);
                leanh::lean_dec(v_a_1974_);
                if leanh::lean_obj_tag(v_fst_1978_) == 0 {
                    v___x_1979_ = 1;
                    v___x_1980_ = leanh::lean_box((v___x_1979_) as usize);
                    if v_isShared_1977_ == 0 {
                        leanh::lean_ctor_set(v___x_1976_, 0, v___x_1980_);
                        v___x_1982_ = v___x_1976_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1983_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
                        v___x_1982_ = v_reuseFailAlloc_1983_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1984_ = leanh::lean_ctor_get(v_fst_1978_, 0);
                    leanh::lean_inc(v_val_1984_);
                    leanh::lean_dec_ref_known(v_fst_1978_, 1);
                    if v_isShared_1977_ == 0 {
                        leanh::lean_ctor_set(v___x_1976_, 0, v_val_1984_);
                        v___x_1986_ = v___x_1976_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_val_1984_);
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
                    v_reuseFailAlloc_1995_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
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
                    v_reuseFailAlloc_2008_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
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
                    v_reuseFailAlloc_2016_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
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
    mut v_a_2019_: *mut leanh::LeanObject,
    mut v_b_2020_: *mut leanh::LeanObject,
    mut v_a_2021_: *mut leanh::LeanObject,
    mut v_a_2022_: *mut leanh::LeanObject,
    mut v_a_2023_: *mut leanh::LeanObject,
    mut v_a_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_2019_) {
                11 => {
                    v_struct_2037_ = leanh::lean_ctor_get(v_a_2019_, 2);
                    leanh::lean_inc_ref(v_struct_2037_);
                    leanh::lean_dec_ref_known(v_a_2019_, 3);
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
                    v_dummy_2039_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
                    v_nargs_2040_ = l_Lean_Expr_getAppNumArgs(v_a_2019_);
                    leanh::lean_inc(v_nargs_2040_);
                    v___x_2041_ = lean_mk_array(v_nargs_2040_, v_dummy_2039_);
                    v___x_2042_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2043_ = lean_nat_sub(v_nargs_2040_, v___x_2042_);
                    leanh::lean_dec(v_nargs_2040_);
                    v___x_2044_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_2018_, v_b_2020_, v_a_2019_, v___x_2041_, v___x_2043_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
                    return v___x_2044_;
                }
                6 => {
                    v_binderType_2045_ = leanh::lean_ctor_get(v_a_2019_, 1);
                    leanh::lean_inc_ref(v_binderType_2045_);
                    v_body_2046_ = leanh::lean_ctor_get(v_a_2019_, 2);
                    leanh::lean_inc_ref(v_body_2046_);
                    leanh::lean_dec_ref_known(v_a_2019_, 3);
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
                    v_binderType_2047_ = leanh::lean_ctor_get(v_a_2019_, 1);
                    leanh::lean_inc_ref(v_binderType_2047_);
                    v_body_2048_ = leanh::lean_ctor_get(v_a_2019_, 2);
                    leanh::lean_inc_ref(v_body_2048_);
                    leanh::lean_dec_ref_known(v_a_2019_, 3);
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
                    v_value_2049_ = leanh::lean_ctor_get(v_a_2019_, 2);
                    leanh::lean_inc_ref(v_value_2049_);
                    v_body_2050_ = leanh::lean_ctor_get(v_a_2019_, 3);
                    leanh::lean_inc_ref(v_body_2050_);
                    leanh::lean_dec_ref_known(v_a_2019_, 4);
                    leanh::lean_inc_ref(v_b_2020_);
                    v___x_2051_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_2018_,
                        v_value_2049_,
                        v_b_2020_,
                        v_a_2021_,
                        v_a_2022_,
                        v_a_2023_,
                        v_a_2024_,
                    );
                    if leanh::lean_obj_tag(v___x_2051_) == 0 {
                        v_a_2052_ = leanh::lean_ctor_get(v___x_2051_, 0);
                        leanh::lean_inc(v_a_2052_);
                        v___x_2053_ = (leanh::lean_unbox(v_a_2052_) as u8);
                        leanh::lean_dec(v_a_2052_);
                        if v___x_2053_ == 0 {
                            leanh::lean_dec_ref(v_body_2050_);
                            leanh::lean_dec_ref(v_b_2020_);
                            return v___x_2051_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2051_, 1);
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
                        leanh::lean_dec_ref(v_body_2050_);
                        leanh::lean_dec_ref(v_b_2020_);
                        return v___x_2051_;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_b_2020_);
                    leanh::lean_dec_ref(v_a_2019_);
                    v___x_2055_ = 1;
                    v___x_2056_ = leanh::lean_box((v___x_2055_) as usize);
                    v___x_2057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2057_, 0, v___x_2056_);
                    return v___x_2057_;
                }
            },
            1 => {
                leanh::lean_inc_ref(v_b_2020_);
                v___x_2033_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_2018_,
                    v_d_2027_,
                    v_b_2020_,
                    v___y_2029_,
                    v___y_2030_,
                    v___y_2031_,
                    v___y_2032_,
                );
                if leanh::lean_obj_tag(v___x_2033_) == 0 {
                    v_a_2034_ = leanh::lean_ctor_get(v___x_2033_, 0);
                    leanh::lean_inc(v_a_2034_);
                    v___x_2035_ = (leanh::lean_unbox(v_a_2034_) as u8);
                    leanh::lean_dec(v_a_2034_);
                    if v___x_2035_ == 0 {
                        leanh::lean_dec_ref(v_e_2028_);
                        leanh::lean_dec_ref(v_b_2020_);
                        return v___x_2033_;
                    } else {
                        leanh::lean_dec_ref_known(v___x_2033_, 1);
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
                    leanh::lean_dec_ref(v_e_2028_);
                    leanh::lean_dec_ref(v_b_2020_);
                    return v___x_2033_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
    mut v_mode_2058_: u8,
    mut v_a_2059_: *mut leanh::LeanObject,
    mut v_b_2060_: *mut leanh::LeanObject,
    mut v_a_2061_: *mut leanh::LeanObject,
    mut v_a_2062_: *mut leanh::LeanObject,
    mut v_a_2063_: *mut leanh::LeanObject,
    mut v_a_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2066_) == 0 {
                    v_a_2067_ = leanh::lean_ctor_get(v___x_2066_, 0);
                    v_isSharedCheck_2082_ = (!leanh::lean_is_exclusive(v___x_2066_)) as u8;
                    if v_isSharedCheck_2082_ == 0 {
                        v___x_2069_ = v___x_2066_;
                        v_isShared_2070_ = v_isSharedCheck_2082_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2067_);
                        leanh::lean_dec(v___x_2066_);
                        v___x_2069_ = leanh::lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2082_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2066_;
                }
            }
            1 => {
                v___x_2071_ = (leanh::lean_unbox(v_a_2067_) as u8);
                leanh::lean_dec(v_a_2067_);
                if v___x_2071_ == 0 {
                    v___x_2072_ = 1;
                    v___x_2073_ = leanh::lean_box((v___x_2072_) as usize);
                    if v_isShared_2070_ == 0 {
                        leanh::lean_ctor_set(v___x_2069_, 0, v___x_2073_);
                        v___x_2075_ = v___x_2069_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
                        v___x_2075_ = v_reuseFailAlloc_2076_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2077_ = 0;
                    v___x_2078_ = leanh::lean_box((v___x_2077_) as usize);
                    if v_isShared_2070_ == 0 {
                        leanh::lean_ctor_set(v___x_2069_, 0, v___x_2078_);
                        v___x_2080_ = v___x_2069_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2081_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
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
    mut v_mode_2083_: *mut leanh::LeanObject,
    mut v_a_2084_: *mut leanh::LeanObject,
    mut v_b_2085_: *mut leanh::LeanObject,
    mut v_a_2086_: *mut leanh::LeanObject,
    mut v_a_2087_: *mut leanh::LeanObject,
    mut v_a_2088_: *mut leanh::LeanObject,
    mut v_a_2089_: *mut leanh::LeanObject,
    mut v_a_2090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2091_: u8 = 0;
    let mut v_res_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2091_ = (leanh::lean_unbox(v_mode_2083_) as u8);
    v_res_2092_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
        v_mode_boxed_2091_,
        v_a_2084_,
        v_b_2085_,
        v_a_2086_,
        v_a_2087_,
        v_a_2088_,
        v_a_2089_,
    );
    leanh::lean_dec(v_a_2089_);
    leanh::lean_dec_ref(v_a_2088_);
    leanh::lean_dec(v_a_2087_);
    leanh::lean_dec_ref(v_a_2086_);
    return v_res_2092_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(
    mut v_mode_2093_: *mut leanh::LeanObject,
    mut v_a_u2081_2094_: *mut leanh::LeanObject,
    mut v_a_u2082_2095_: *mut leanh::LeanObject,
    mut v_b_u2081_2096_: *mut leanh::LeanObject,
    mut v_b_u2082_2097_: *mut leanh::LeanObject,
    mut v_a_2098_: *mut leanh::LeanObject,
    mut v_a_2099_: *mut leanh::LeanObject,
    mut v_a_2100_: *mut leanh::LeanObject,
    mut v_a_2101_: *mut leanh::LeanObject,
    mut v_a_2102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2103_: u8 = 0;
    let mut v_res_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2103_ = (leanh::lean_unbox(v_mode_2093_) as u8);
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
    leanh::lean_dec(v_a_2101_);
    leanh::lean_dec_ref(v_a_2100_);
    leanh::lean_dec(v_a_2099_);
    leanh::lean_dec_ref(v_a_2098_);
    return v_res_2104_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(
    mut v_upperBound_2105_: *mut leanh::LeanObject,
    mut v_args_2106_: *mut leanh::LeanObject,
    mut v_mode_2107_: *mut leanh::LeanObject,
    mut v_b_2108_: *mut leanh::LeanObject,
    mut v_a_2109_: *mut leanh::LeanObject,
    mut v_b_2110_: *mut leanh::LeanObject,
    mut v___y_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
    mut v___y_2114_: *mut leanh::LeanObject,
    mut v___y_2115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2116_: u8 = 0;
    let mut v_res_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2116_ = (leanh::lean_unbox(v_mode_2107_) as u8);
    v_res_2117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_2105_, v_args_2106_, v_mode_boxed_2116_, v_b_2108_, v_a_2109_, v_b_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
    leanh::lean_dec(v___y_2114_);
    leanh::lean_dec_ref(v___y_2113_);
    leanh::lean_dec(v___y_2112_);
    leanh::lean_dec_ref(v___y_2111_);
    leanh::lean_dec_ref(v_args_2106_);
    leanh::lean_dec(v_upperBound_2105_);
    return v_res_2117_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(
    mut v_mode_2118_: *mut leanh::LeanObject,
    mut v_a_2119_: *mut leanh::LeanObject,
    mut v_b_2120_: *mut leanh::LeanObject,
    mut v_a_2121_: *mut leanh::LeanObject,
    mut v_a_2122_: *mut leanh::LeanObject,
    mut v_a_2123_: *mut leanh::LeanObject,
    mut v_a_2124_: *mut leanh::LeanObject,
    mut v_a_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2126_: u8 = 0;
    let mut v_res_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2126_ = (leanh::lean_unbox(v_mode_2118_) as u8);
    v_res_2127_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
        v_mode_boxed_2126_,
        v_a_2119_,
        v_b_2120_,
        v_a_2121_,
        v_a_2122_,
        v_a_2123_,
        v_a_2124_,
    );
    leanh::lean_dec(v_a_2124_);
    leanh::lean_dec_ref(v_a_2123_);
    leanh::lean_dec(v_a_2122_);
    leanh::lean_dec_ref(v_a_2121_);
    return v_res_2127_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(
    mut v_upperBound_2128_: *mut leanh::LeanObject,
    mut v_a_2129_: *mut leanh::LeanObject,
    mut v_args_2130_: *mut leanh::LeanObject,
    mut v_mode_2131_: *mut leanh::LeanObject,
    mut v_b_2132_: *mut leanh::LeanObject,
    mut v_a_2133_: *mut leanh::LeanObject,
    mut v_b_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
    mut v___y_2136_: *mut leanh::LeanObject,
    mut v___y_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2140_: u8 = 0;
    let mut v_res_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2140_ = (leanh::lean_unbox(v_mode_2131_) as u8);
    v_res_2141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_2128_, v_a_2129_, v_args_2130_, v_mode_boxed_2140_, v_b_2132_, v_a_2133_, v_b_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
    leanh::lean_dec(v___y_2138_);
    leanh::lean_dec_ref(v___y_2137_);
    leanh::lean_dec(v___y_2136_);
    leanh::lean_dec_ref(v___y_2135_);
    leanh::lean_dec_ref(v_args_2130_);
    leanh::lean_dec_ref(v_a_2129_);
    leanh::lean_dec(v_upperBound_2128_);
    return v_res_2141_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(
    mut v_mode_2142_: *mut leanh::LeanObject,
    mut v_a_2143_: *mut leanh::LeanObject,
    mut v_b_2144_: *mut leanh::LeanObject,
    mut v_a_2145_: *mut leanh::LeanObject,
    mut v_a_2146_: *mut leanh::LeanObject,
    mut v_a_2147_: *mut leanh::LeanObject,
    mut v_a_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2150_: u8 = 0;
    let mut v_res_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2150_ = (leanh::lean_unbox(v_mode_2142_) as u8);
    v_res_2151_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(
        v_mode_boxed_2150_,
        v_a_2143_,
        v_b_2144_,
        v_a_2145_,
        v_a_2146_,
        v_a_2147_,
        v_a_2148_,
    );
    leanh::lean_dec(v_a_2148_);
    leanh::lean_dec_ref(v_a_2147_);
    leanh::lean_dec(v_a_2146_);
    leanh::lean_dec_ref(v_a_2145_);
    return v_res_2151_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(
    mut v_mode_2152_: *mut leanh::LeanObject,
    mut v_a_2153_: *mut leanh::LeanObject,
    mut v_b_2154_: *mut leanh::LeanObject,
    mut v_a_2155_: *mut leanh::LeanObject,
    mut v_a_2156_: *mut leanh::LeanObject,
    mut v_a_2157_: *mut leanh::LeanObject,
    mut v_a_2158_: *mut leanh::LeanObject,
    mut v_a_2159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2160_: u8 = 0;
    let mut v_res_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2160_ = (leanh::lean_unbox(v_mode_2152_) as u8);
    v_res_2161_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(
        v_mode_boxed_2160_,
        v_a_2153_,
        v_b_2154_,
        v_a_2155_,
        v_a_2156_,
        v_a_2157_,
        v_a_2158_,
    );
    leanh::lean_dec(v_a_2158_);
    leanh::lean_dec_ref(v_a_2157_);
    leanh::lean_dec(v_a_2156_);
    leanh::lean_dec_ref(v_a_2155_);
    return v_res_2161_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(
    mut v_upperBound_2162_: *mut leanh::LeanObject,
    mut v___x_2163_: *mut leanh::LeanObject,
    mut v___x_2164_: *mut leanh::LeanObject,
    mut v_mode_2165_: *mut leanh::LeanObject,
    mut v_a_2166_: *mut leanh::LeanObject,
    mut v_b_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
    mut v___y_2169_: *mut leanh::LeanObject,
    mut v___y_2170_: *mut leanh::LeanObject,
    mut v___y_2171_: *mut leanh::LeanObject,
    mut v___y_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2173_: u8 = 0;
    let mut v_res_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2173_ = (leanh::lean_unbox(v_mode_2165_) as u8);
    v_res_2174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_2162_, v___x_2163_, v___x_2164_, v_mode_boxed_2173_, v_a_2166_, v_b_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
    leanh::lean_dec(v___y_2171_);
    leanh::lean_dec_ref(v___y_2170_);
    leanh::lean_dec(v___y_2169_);
    leanh::lean_dec_ref(v___y_2168_);
    leanh::lean_dec_ref(v___x_2164_);
    leanh::lean_dec_ref(v___x_2163_);
    leanh::lean_dec(v_upperBound_2162_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(
    mut v_mode_2175_: *mut leanh::LeanObject,
    mut v_b_2176_: *mut leanh::LeanObject,
    mut v_x_2177_: *mut leanh::LeanObject,
    mut v_x_2178_: *mut leanh::LeanObject,
    mut v_x_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
    mut v___y_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
    mut v___y_2184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2185_: u8 = 0;
    let mut v_res_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2185_ = (leanh::lean_unbox(v_mode_2175_) as u8);
    v_res_2186_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_2185_, v_b_2176_, v_x_2177_, v_x_2178_, v_x_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
    leanh::lean_dec(v___y_2183_);
    leanh::lean_dec_ref(v___y_2182_);
    leanh::lean_dec(v___y_2181_);
    leanh::lean_dec_ref(v___y_2180_);
    return v_res_2186_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(
    mut v_upperBound_2187_: *mut leanh::LeanObject,
    mut v_a_2188_: *mut leanh::LeanObject,
    mut v___x_2189_: *mut leanh::LeanObject,
    mut v___x_2190_: *mut leanh::LeanObject,
    mut v_mode_2191_: *mut leanh::LeanObject,
    mut v_a_2192_: *mut leanh::LeanObject,
    mut v_b_2193_: *mut leanh::LeanObject,
    mut v___y_2194_: *mut leanh::LeanObject,
    mut v___y_2195_: *mut leanh::LeanObject,
    mut v___y_2196_: *mut leanh::LeanObject,
    mut v___y_2197_: *mut leanh::LeanObject,
    mut v___y_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2199_: u8 = 0;
    let mut v_res_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2199_ = (leanh::lean_unbox(v_mode_2191_) as u8);
    v_res_2200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_2187_, v_a_2188_, v___x_2189_, v___x_2190_, v_mode_boxed_2199_, v_a_2192_, v_b_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
    leanh::lean_dec(v___y_2197_);
    leanh::lean_dec_ref(v___y_2196_);
    leanh::lean_dec(v___y_2195_);
    leanh::lean_dec_ref(v___y_2194_);
    leanh::lean_dec_ref(v___x_2190_);
    leanh::lean_dec_ref(v___x_2189_);
    leanh::lean_dec_ref(v_a_2188_);
    leanh::lean_dec(v_upperBound_2187_);
    return v_res_2200_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(
    mut v_mode_2201_: *mut leanh::LeanObject,
    mut v_a_2202_: *mut leanh::LeanObject,
    mut v_b_2203_: *mut leanh::LeanObject,
    mut v_a_2204_: *mut leanh::LeanObject,
    mut v_a_2205_: *mut leanh::LeanObject,
    mut v_a_2206_: *mut leanh::LeanObject,
    mut v_a_2207_: *mut leanh::LeanObject,
    mut v_a_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2209_: u8 = 0;
    let mut v_res_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2209_ = (leanh::lean_unbox(v_mode_2201_) as u8);
    v_res_2210_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(
        v_mode_boxed_2209_,
        v_a_2202_,
        v_b_2203_,
        v_a_2204_,
        v_a_2205_,
        v_a_2206_,
        v_a_2207_,
    );
    leanh::lean_dec(v_a_2207_);
    leanh::lean_dec_ref(v_a_2206_);
    leanh::lean_dec(v_a_2205_);
    leanh::lean_dec_ref(v_a_2204_);
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(
    mut v_mode_2211_: *mut leanh::LeanObject,
    mut v_a_2212_: *mut leanh::LeanObject,
    mut v_b_2213_: *mut leanh::LeanObject,
    mut v_a_2214_: *mut leanh::LeanObject,
    mut v_a_2215_: *mut leanh::LeanObject,
    mut v_a_2216_: *mut leanh::LeanObject,
    mut v_a_2217_: *mut leanh::LeanObject,
    mut v_a_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2219_: u8 = 0;
    let mut v_res_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2219_ = (leanh::lean_unbox(v_mode_2211_) as u8);
    v_res_2220_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(
        v_mode_boxed_2219_,
        v_a_2212_,
        v_b_2213_,
        v_a_2214_,
        v_a_2215_,
        v_a_2216_,
        v_a_2217_,
    );
    leanh::lean_dec(v_a_2217_);
    leanh::lean_dec_ref(v_a_2216_);
    leanh::lean_dec(v_a_2215_);
    leanh::lean_dec_ref(v_a_2214_);
    return v_res_2220_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(
    mut v_upperBound_2221_: *mut leanh::LeanObject,
    mut v___x_2222_: *mut leanh::LeanObject,
    mut v___x_2223_: *mut leanh::LeanObject,
    mut v_mode_2224_: u8,
    mut v_inst_2225_: *mut leanh::LeanObject,
    mut v_R_2226_: *mut leanh::LeanObject,
    mut v_a_2227_: *mut leanh::LeanObject,
    mut v_b_2228_: *mut leanh::LeanObject,
    mut v_c_2229_: *mut leanh::LeanObject,
    mut v___y_2230_: *mut leanh::LeanObject,
    mut v___y_2231_: *mut leanh::LeanObject,
    mut v___y_2232_: *mut leanh::LeanObject,
    mut v___y_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_2221_, v___x_2222_, v___x_2223_, v_mode_2224_, v_a_2227_, v_b_2228_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
    return v___x_2235_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(
    mut v_upperBound_2236_: *mut leanh::LeanObject,
    mut v___x_2237_: *mut leanh::LeanObject,
    mut v___x_2238_: *mut leanh::LeanObject,
    mut v_mode_2239_: *mut leanh::LeanObject,
    mut v_inst_2240_: *mut leanh::LeanObject,
    mut v_R_2241_: *mut leanh::LeanObject,
    mut v_a_2242_: *mut leanh::LeanObject,
    mut v_b_2243_: *mut leanh::LeanObject,
    mut v_c_2244_: *mut leanh::LeanObject,
    mut v___y_2245_: *mut leanh::LeanObject,
    mut v___y_2246_: *mut leanh::LeanObject,
    mut v___y_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2250_: u8 = 0;
    let mut v_res_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2250_ = (leanh::lean_unbox(v_mode_2239_) as u8);
    v_res_2251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_2236_, v___x_2237_, v___x_2238_, v_mode_boxed_2250_, v_inst_2240_, v_R_2241_, v_a_2242_, v_b_2243_, v_c_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
    leanh::lean_dec(v___y_2248_);
    leanh::lean_dec_ref(v___y_2247_);
    leanh::lean_dec(v___y_2246_);
    leanh::lean_dec_ref(v___y_2245_);
    leanh::lean_dec_ref(v___x_2238_);
    leanh::lean_dec_ref(v___x_2237_);
    leanh::lean_dec(v_upperBound_2236_);
    return v_res_2251_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(
    mut v_upperBound_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
    mut v___x_2254_: *mut leanh::LeanObject,
    mut v___x_2255_: *mut leanh::LeanObject,
    mut v_mode_2256_: u8,
    mut v_inst_2257_: *mut leanh::LeanObject,
    mut v_R_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: *mut leanh::LeanObject,
    mut v_b_2260_: *mut leanh::LeanObject,
    mut v_c_2261_: *mut leanh::LeanObject,
    mut v___y_2262_: *mut leanh::LeanObject,
    mut v___y_2263_: *mut leanh::LeanObject,
    mut v___y_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_2252_, v_a_2253_, v___x_2254_, v___x_2255_, v_mode_2256_, v_a_2259_, v_b_2260_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
    return v___x_2267_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(
    mut v_upperBound_2268_: *mut leanh::LeanObject,
    mut v_a_2269_: *mut leanh::LeanObject,
    mut v___x_2270_: *mut leanh::LeanObject,
    mut v___x_2271_: *mut leanh::LeanObject,
    mut v_mode_2272_: *mut leanh::LeanObject,
    mut v_inst_2273_: *mut leanh::LeanObject,
    mut v_R_2274_: *mut leanh::LeanObject,
    mut v_a_2275_: *mut leanh::LeanObject,
    mut v_b_2276_: *mut leanh::LeanObject,
    mut v_c_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2283_: u8 = 0;
    let mut v_res_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2283_ = (leanh::lean_unbox(v_mode_2272_) as u8);
    v_res_2284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_2268_, v_a_2269_, v___x_2270_, v___x_2271_, v_mode_boxed_2283_, v_inst_2273_, v_R_2274_, v_a_2275_, v_b_2276_, v_c_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
    leanh::lean_dec(v___y_2281_);
    leanh::lean_dec_ref(v___y_2280_);
    leanh::lean_dec(v___y_2279_);
    leanh::lean_dec_ref(v___y_2278_);
    leanh::lean_dec_ref(v___x_2271_);
    leanh::lean_dec_ref(v___x_2270_);
    leanh::lean_dec_ref(v_a_2269_);
    leanh::lean_dec(v_upperBound_2268_);
    return v_res_2284_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(
    mut v_upperBound_2285_: *mut leanh::LeanObject,
    mut v_args_2286_: *mut leanh::LeanObject,
    mut v_mode_2287_: u8,
    mut v_b_2288_: *mut leanh::LeanObject,
    mut v_inst_2289_: *mut leanh::LeanObject,
    mut v_R_2290_: *mut leanh::LeanObject,
    mut v_a_2291_: *mut leanh::LeanObject,
    mut v_b_2292_: *mut leanh::LeanObject,
    mut v_c_2293_: *mut leanh::LeanObject,
    mut v___y_2294_: *mut leanh::LeanObject,
    mut v___y_2295_: *mut leanh::LeanObject,
    mut v___y_2296_: *mut leanh::LeanObject,
    mut v___y_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_2285_, v_args_2286_, v_mode_2287_, v_b_2288_, v_a_2291_, v_b_2292_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
    return v___x_2299_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(
    mut v_upperBound_2300_: *mut leanh::LeanObject,
    mut v_args_2301_: *mut leanh::LeanObject,
    mut v_mode_2302_: *mut leanh::LeanObject,
    mut v_b_2303_: *mut leanh::LeanObject,
    mut v_inst_2304_: *mut leanh::LeanObject,
    mut v_R_2305_: *mut leanh::LeanObject,
    mut v_a_2306_: *mut leanh::LeanObject,
    mut v_b_2307_: *mut leanh::LeanObject,
    mut v_c_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2314_: u8 = 0;
    let mut v_res_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2314_ = (leanh::lean_unbox(v_mode_2302_) as u8);
    v_res_2315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_2300_, v_args_2301_, v_mode_boxed_2314_, v_b_2303_, v_inst_2304_, v_R_2305_, v_a_2306_, v_b_2307_, v_c_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    leanh::lean_dec(v___y_2312_);
    leanh::lean_dec_ref(v___y_2311_);
    leanh::lean_dec(v___y_2310_);
    leanh::lean_dec_ref(v___y_2309_);
    leanh::lean_dec_ref(v_args_2301_);
    leanh::lean_dec(v_upperBound_2300_);
    return v_res_2315_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(
    mut v_upperBound_2316_: *mut leanh::LeanObject,
    mut v_a_2317_: *mut leanh::LeanObject,
    mut v_args_2318_: *mut leanh::LeanObject,
    mut v_mode_2319_: u8,
    mut v_b_2320_: *mut leanh::LeanObject,
    mut v_inst_2321_: *mut leanh::LeanObject,
    mut v_R_2322_: *mut leanh::LeanObject,
    mut v_a_2323_: *mut leanh::LeanObject,
    mut v_b_2324_: *mut leanh::LeanObject,
    mut v_c_2325_: *mut leanh::LeanObject,
    mut v___y_2326_: *mut leanh::LeanObject,
    mut v___y_2327_: *mut leanh::LeanObject,
    mut v___y_2328_: *mut leanh::LeanObject,
    mut v___y_2329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2331_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_2316_, v_a_2317_, v_args_2318_, v_mode_2319_, v_b_2320_, v_a_2323_, v_b_2324_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
    return v___x_2331_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(
    mut v_upperBound_2332_: *mut leanh::LeanObject,
    mut v_a_2333_: *mut leanh::LeanObject,
    mut v_args_2334_: *mut leanh::LeanObject,
    mut v_mode_2335_: *mut leanh::LeanObject,
    mut v_b_2336_: *mut leanh::LeanObject,
    mut v_inst_2337_: *mut leanh::LeanObject,
    mut v_R_2338_: *mut leanh::LeanObject,
    mut v_a_2339_: *mut leanh::LeanObject,
    mut v_b_2340_: *mut leanh::LeanObject,
    mut v_c_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2347_: u8 = 0;
    let mut v_res_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2347_ = (leanh::lean_unbox(v_mode_2335_) as u8);
    v_res_2348_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_2332_, v_a_2333_, v_args_2334_, v_mode_boxed_2347_, v_b_2336_, v_inst_2337_, v_R_2338_, v_a_2339_, v_b_2340_, v_c_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
    leanh::lean_dec(v___y_2345_);
    leanh::lean_dec_ref(v___y_2344_);
    leanh::lean_dec(v___y_2343_);
    leanh::lean_dec_ref(v___y_2342_);
    leanh::lean_dec_ref(v_args_2334_);
    leanh::lean_dec_ref(v_a_2333_);
    leanh::lean_dec(v_upperBound_2332_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_Meta_ACLt_main(
    mut v_a_2349_: *mut leanh::LeanObject,
    mut v_b_2350_: *mut leanh::LeanObject,
    mut v_mode_2351_: u8,
    mut v_a_2352_: *mut leanh::LeanObject,
    mut v_a_2353_: *mut leanh::LeanObject,
    mut v_a_2354_: *mut leanh::LeanObject,
    mut v_a_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_2358_: *mut leanh::LeanObject,
    mut v_b_2359_: *mut leanh::LeanObject,
    mut v_mode_2360_: *mut leanh::LeanObject,
    mut v_a_2361_: *mut leanh::LeanObject,
    mut v_a_2362_: *mut leanh::LeanObject,
    mut v_a_2363_: *mut leanh::LeanObject,
    mut v_a_2364_: *mut leanh::LeanObject,
    mut v_a_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2366_: u8 = 0;
    let mut v_res_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2366_ = (leanh::lean_unbox(v_mode_2360_) as u8);
    v_res_2367_ = l_Lean_Meta_ACLt_main(
        v_a_2358_,
        v_b_2359_,
        v_mode_boxed_2366_,
        v_a_2361_,
        v_a_2362_,
        v_a_2363_,
        v_a_2364_,
    );
    leanh::lean_dec(v_a_2364_);
    leanh::lean_dec_ref(v_a_2363_);
    leanh::lean_dec(v_a_2362_);
    leanh::lean_dec_ref(v_a_2361_);
    return v_res_2367_;
}
pub unsafe fn l_Lean_Meta_acLt(
    mut v_a_2368_: *mut leanh::LeanObject,
    mut v_b_2369_: *mut leanh::LeanObject,
    mut v_mode_2370_: u8,
    mut v_a_2371_: *mut leanh::LeanObject,
    mut v_a_2372_: *mut leanh::LeanObject,
    mut v_a_2373_: *mut leanh::LeanObject,
    mut v_a_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_2377_: *mut leanh::LeanObject,
    mut v_b_2378_: *mut leanh::LeanObject,
    mut v_mode_2379_: *mut leanh::LeanObject,
    mut v_a_2380_: *mut leanh::LeanObject,
    mut v_a_2381_: *mut leanh::LeanObject,
    mut v_a_2382_: *mut leanh::LeanObject,
    mut v_a_2383_: *mut leanh::LeanObject,
    mut v_a_2384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mode_boxed_2385_: u8 = 0;
    let mut v_res_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mode_boxed_2385_ = (leanh::lean_unbox(v_mode_2379_) as u8);
    v_res_2386_ = l_Lean_Meta_acLt(
        v_a_2377_,
        v_b_2378_,
        v_mode_boxed_2385_,
        v_a_2380_,
        v_a_2381_,
        v_a_2382_,
        v_a_2383_,
    );
    leanh::lean_dec(v_a_2383_);
    leanh::lean_dec_ref(v_a_2382_);
    leanh::lean_dec(v_a_2381_);
    leanh::lean_dec_ref(v_a_2380_);
    return v_res_2386_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ACLt(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_DiscrTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config =
        _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config();
    leanh::lean_mark_persistent(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ACLt(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ACLt(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_DiscrTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ACLt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ACLt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_ACLt(builtin);
}