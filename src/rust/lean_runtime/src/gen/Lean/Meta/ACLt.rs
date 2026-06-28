// Lean compiler output
// Module: Lean.Meta.ACLt
// Imports: Lean.Meta.DiscrTree.Main Init.Data.Range.Polymorphic.Iterators Lean.Meta.FunInfo
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub, lean_panic_fn_borrowed, lean_uint8_dec_lt,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_5, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut LeanObject,
        72058693566333441 as *mut LeanObject,
        65793 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0_value)
        as *mut LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0_value
) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6_value:
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
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5_value:
    LeanStringObject<58> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Expr_ctorWeight(mut v_x_1194_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_x_1194_) {
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
pub unsafe fn l_Lean_Expr_ctorWeight___boxed(mut v_x_1207_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1208_: u8 = 0;
    let mut v_r_1209_: *mut LeanObject = core::ptr::null_mut();
    v_res_1208_ = l_Lean_Expr_ctorWeight(v_x_1207_);
    lean_dec_ref(v_x_1207_);
    v_r_1209_ = lean_box((v_res_1208_) as usize);
    return v_r_1209_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorIdx(mut v_x_1210_: u8) -> *mut LeanObject {
    match v_x_1210_ {
        0 => {
            let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
            v___x_1211_ = lean_unsigned_to_nat(0);
            return v___x_1211_;
        }
        1 => {
            let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
            v___x_1212_ = lean_unsigned_to_nat(1);
            return v___x_1212_;
        }
        _ => {
            let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
            v___x_1213_ = lean_unsigned_to_nat(2);
            return v___x_1213_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorIdx___boxed(
    mut v_x_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1215_: u8 = 0;
    let mut v_res_1216_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1215_ = (lean_unbox(v_x_1214_) as u8);
    v_res_1216_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx(v_x_boxed_1215_);
    return v_res_1216_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(mut v_x_1217_: u8) -> *mut LeanObject {
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    v___x_1218_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx(v_x_1217_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_toCtorIdx___boxed(
    mut v_x_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1220_: u8 = 0;
    let mut v_res_1221_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1220_ = (lean_unbox(v_x_1219_) as u8);
    v_res_1221_ = l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(v_x_4__boxed_1220_);
    return v_res_1221_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(
    mut v_k_1222_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1222_);
    return v_k_1222_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg___boxed(
    mut v_k_1223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1224_: *mut LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(v_k_1223_);
    lean_dec(v_k_1223_);
    return v_res_1224_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim(
    mut v_motive_1225_: *mut LeanObject,
    mut v_ctorIdx_1226_: *mut LeanObject,
    mut v_t_1227_: u8,
    mut v_h_1228_: *mut LeanObject,
    mut v_k_1229_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1229_);
    return v_k_1229_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_ctorElim___boxed(
    mut v_motive_1230_: *mut LeanObject,
    mut v_ctorIdx_1231_: *mut LeanObject,
    mut v_t_1232_: *mut LeanObject,
    mut v_h_1233_: *mut LeanObject,
    mut v_k_1234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1235_: u8 = 0;
    let mut v_res_1236_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1235_ = (lean_unbox(v_t_1232_) as u8);
    v_res_1236_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim(
        v_motive_1230_,
        v_ctorIdx_1231_,
        v_t_boxed_1235_,
        v_h_1233_,
        v_k_1234_,
    );
    lean_dec(v_k_1234_);
    lean_dec(v_ctorIdx_1231_);
    return v_res_1236_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(
    mut v_reduce_1237_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_reduce_1237_);
    return v_reduce_1237_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg___boxed(
    mut v_reduce_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1239_: *mut LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(v_reduce_1238_);
    lean_dec(v_reduce_1238_);
    return v_res_1239_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim(
    mut v_motive_1240_: *mut LeanObject,
    mut v_t_1241_: u8,
    mut v_h_1242_: *mut LeanObject,
    mut v_reduce_1243_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_reduce_1243_);
    return v_reduce_1243_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduce_elim___boxed(
    mut v_motive_1244_: *mut LeanObject,
    mut v_t_1245_: *mut LeanObject,
    mut v_h_1246_: *mut LeanObject,
    mut v_reduce_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1248_: u8 = 0;
    let mut v_res_1249_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1248_ = (lean_unbox(v_t_1245_) as u8);
    v_res_1249_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim(
        v_motive_1244_,
        v_t_boxed_1248_,
        v_h_1246_,
        v_reduce_1247_,
    );
    lean_dec(v_reduce_1247_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(
    mut v_reduceSimpleOnly_1250_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_reduceSimpleOnly_1250_);
    return v_reduceSimpleOnly_1250_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg___boxed(
    mut v_reduceSimpleOnly_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1252_: *mut LeanObject = core::ptr::null_mut();
    v_res_1252_ =
        l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(v_reduceSimpleOnly_1251_);
    lean_dec(v_reduceSimpleOnly_1251_);
    return v_res_1252_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(
    mut v_motive_1253_: *mut LeanObject,
    mut v_t_1254_: u8,
    mut v_h_1255_: *mut LeanObject,
    mut v_reduceSimpleOnly_1256_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_reduceSimpleOnly_1256_);
    return v_reduceSimpleOnly_1256_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___boxed(
    mut v_motive_1257_: *mut LeanObject,
    mut v_t_1258_: *mut LeanObject,
    mut v_h_1259_: *mut LeanObject,
    mut v_reduceSimpleOnly_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1261_: u8 = 0;
    let mut v_res_1262_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1261_ = (lean_unbox(v_t_1258_) as u8);
    v_res_1262_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(
        v_motive_1257_,
        v_t_boxed_1261_,
        v_h_1259_,
        v_reduceSimpleOnly_1260_,
    );
    lean_dec(v_reduceSimpleOnly_1260_);
    return v_res_1262_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(
    mut v_none_1263_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_none_1263_);
    return v_none_1263_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg___boxed(
    mut v_none_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1265_: *mut LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(v_none_1264_);
    lean_dec(v_none_1264_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim(
    mut v_motive_1266_: *mut LeanObject,
    mut v_t_1267_: u8,
    mut v_h_1268_: *mut LeanObject,
    mut v_none_1269_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_none_1269_);
    return v_none_1269_;
}
pub unsafe fn l_Lean_Meta_ACLt_ReduceMode_none_elim___boxed(
    mut v_motive_1270_: *mut LeanObject,
    mut v_t_1271_: *mut LeanObject,
    mut v_h_1272_: *mut LeanObject,
    mut v_none_1273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1274_: u8 = 0;
    let mut v_res_1275_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1274_ = (lean_unbox(v_t_1271_) as u8);
    v_res_1275_ = l_Lean_Meta_ACLt_ReduceMode_none_elim(
        v_motive_1270_,
        v_t_boxed_1274_,
        v_h_1272_,
        v_none_1273_,
    );
    lean_dec(v_none_1273_);
    return v_res_1275_;
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1()
-> *mut LeanObject {
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    v___x_1282_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0;
    v___x_1283_ = l_Lean_Meta_Config_toConfigWithKey(v___x_1282_);
    return v___x_1283_;
}
pub unsafe fn _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config() -> *mut LeanObject {
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    v___x_1284_ = lean_obj_once(
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
    mut v_e_1286_: *mut LeanObject,
    mut v_a_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
    mut v_a_1289_: *mut LeanObject,
    mut v_a_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1292_: u8 = 0;
    v___x_1292_ = l_Lean_Expr_hasLooseBVars(v_e_1286_);
    if v___x_1292_ == 0 {
        match v_mode_1285_ {
            0 => {
                let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
                v___x_1293_ = l_Lean_Meta_DiscrTree_reduce(
                    v_e_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_,
                );
                return v___x_1293_;
            }
            1 => {
                let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
                let mut v_config_1295_: *mut LeanObject = core::ptr::null_mut();
                let mut v_trackZetaDelta_1296_: u8 = 0;
                let mut v_zetaDeltaSet_1297_: *mut LeanObject = core::ptr::null_mut();
                let mut v_lctx_1298_: *mut LeanObject = core::ptr::null_mut();
                let mut v_localInstances_1299_: *mut LeanObject = core::ptr::null_mut();
                let mut v_defEqCtx_x3f_1300_: *mut LeanObject = core::ptr::null_mut();
                let mut v_synthPendingDepth_1301_: *mut LeanObject = core::ptr::null_mut();
                let mut v_canUnfold_x3f_1302_: *mut LeanObject = core::ptr::null_mut();
                let mut v_univApprox_1303_: u8 = 0;
                let mut v_inTypeClassResolution_1304_: u8 = 0;
                let mut v_cacheInferType_1305_: u8 = 0;
                let mut v___x_1306_: u64 = 0;
                let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
                v___x_1294_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
                v_config_1295_ = lean_ctor_get(v___x_1294_, 0);
                v_trackZetaDelta_1296_ = lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1297_ = lean_ctor_get(v_a_1287_, 1);
                v_lctx_1298_ = lean_ctor_get(v_a_1287_, 2);
                v_localInstances_1299_ = lean_ctor_get(v_a_1287_, 3);
                v_defEqCtx_x3f_1300_ = lean_ctor_get(v_a_1287_, 4);
                v_synthPendingDepth_1301_ = lean_ctor_get(v_a_1287_, 5);
                v_canUnfold_x3f_1302_ = lean_ctor_get(v_a_1287_, 6);
                v_univApprox_1303_ = lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1304_ = lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1305_ = lean_ctor_get_uint8(
                    v_a_1287_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_1306_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1295_);
                lean_inc_ref(v_config_1295_);
                v___x_1307_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_1307_, 0, v_config_1295_);
                lean_ctor_set_uint64(
                    v___x_1307_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1306_,
                );
                lean_inc(v_canUnfold_x3f_1302_);
                lean_inc(v_synthPendingDepth_1301_);
                lean_inc(v_defEqCtx_x3f_1300_);
                lean_inc_ref(v_localInstances_1299_);
                lean_inc_ref(v_lctx_1298_);
                lean_inc(v_zetaDeltaSet_1297_);
                v___x_1308_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_1308_, 0, v___x_1307_);
                lean_ctor_set(v___x_1308_, 1, v_zetaDeltaSet_1297_);
                lean_ctor_set(v___x_1308_, 2, v_lctx_1298_);
                lean_ctor_set(v___x_1308_, 3, v_localInstances_1299_);
                lean_ctor_set(v___x_1308_, 4, v_defEqCtx_x3f_1300_);
                lean_ctor_set(v___x_1308_, 5, v_synthPendingDepth_1301_);
                lean_ctor_set(v___x_1308_, 6, v_canUnfold_x3f_1302_);
                lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1296_,
                );
                lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1303_,
                );
                lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1304_,
                );
                lean_ctor_set_uint8(
                    v___x_1308_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1305_,
                );
                v___x_1309_ = l_Lean_Meta_DiscrTree_reduce(
                    v_e_1286_,
                    v___x_1308_,
                    v_a_1288_,
                    v_a_1289_,
                    v_a_1290_,
                );
                lean_dec_ref_known(v___x_1308_, 7);
                return v___x_1309_;
            }
            _ => {
                let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
                v___x_1310_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1310_, 0, v_e_1286_);
                return v___x_1310_;
            }
        }
    } else {
        let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
        v___x_1311_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1311_, 0, v_e_1286_);
        return v___x_1311_;
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(
    mut v_mode_1312_: *mut LeanObject,
    mut v_e_1313_: *mut LeanObject,
    mut v_a_1314_: *mut LeanObject,
    mut v_a_1315_: *mut LeanObject,
    mut v_a_1316_: *mut LeanObject,
    mut v_a_1317_: *mut LeanObject,
    mut v_a_1318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_1319_: u8 = 0;
    let mut v_res_1320_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_1319_ = (lean_unbox(v_mode_1312_) as u8);
    v_res_1320_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(
        v_mode_boxed_1319_,
        v_e_1313_,
        v_a_1314_,
        v_a_1315_,
        v_a_1316_,
        v_a_1317_,
    );
    lean_dec(v_a_1317_);
    lean_dec_ref(v_a_1316_);
    lean_dec(v_a_1315_);
    lean_dec_ref(v_a_1314_);
    return v_res_1320_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
    mut v_f_1323_: *mut LeanObject,
    mut v_numArgs_1324_: *mut LeanObject,
    mut v_a_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
    mut v_a_1327_: *mut LeanObject,
    mut v_a_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1335_: u8 = 0;
    let mut v_paramInfo_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut v_a_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
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
                    if lean_obj_tag(v___x_1331_) == 0 {
                        v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
                        v_isSharedCheck_1340_ = (!lean_is_exclusive(v___x_1331_)) as u8;
                        if v_isSharedCheck_1340_ == 0 {
                            v___x_1334_ = v___x_1331_;
                            v_isShared_1335_ = v_isSharedCheck_1340_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1332_);
                            lean_dec(v___x_1331_);
                            v___x_1334_ = lean_box(0);
                            v_isShared_1335_ = v_isSharedCheck_1340_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1341_ = lean_ctor_get(v___x_1331_, 0);
                        v_isSharedCheck_1348_ = (!lean_is_exclusive(v___x_1331_)) as u8;
                        if v_isSharedCheck_1348_ == 0 {
                            v___x_1343_ = v___x_1331_;
                            v_isShared_1344_ = v_isSharedCheck_1348_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1341_);
                            lean_dec(v___x_1331_);
                            v___x_1343_ = lean_box(0);
                            v_isShared_1344_ = v_isSharedCheck_1348_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_numArgs_1324_);
                    lean_dec_ref(v_f_1323_);
                    v___x_1349_ =
                        l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0;
                    v___x_1350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1350_, 0, v___x_1349_);
                    return v___x_1350_;
                }
            }
            1 => {
                v_paramInfo_1336_ = lean_ctor_get(v_a_1332_, 0);
                lean_inc_ref(v_paramInfo_1336_);
                lean_dec(v_a_1332_);
                if v_isShared_1335_ == 0 {
                    lean_ctor_set(v___x_1334_, 0, v_paramInfo_1336_);
                    v___x_1338_ = v___x_1334_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_paramInfo_1336_);
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
                    v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
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
    mut v_f_1351_: *mut LeanObject,
    mut v_numArgs_1352_: *mut LeanObject,
    mut v_a_1353_: *mut LeanObject,
    mut v_a_1354_: *mut LeanObject,
    mut v_a_1355_: *mut LeanObject,
    mut v_a_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1358_: *mut LeanObject = core::ptr::null_mut();
    v_res_1358_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
        v_f_1351_,
        v_numArgs_1352_,
        v_a_1353_,
        v_a_1354_,
        v_a_1355_,
        v_a_1356_,
    );
    lean_dec(v_a_1356_);
    lean_dec_ref(v_a_1355_);
    lean_dec(v_a_1354_);
    lean_dec_ref(v_a_1353_);
    return v_res_1358_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(
    mut v_msg_1360_: *mut LeanObject,
    mut v___y_1361_: *mut LeanObject,
    mut v___y_1362_: *mut LeanObject,
    mut v___y_1363_: *mut LeanObject,
    mut v___y_1364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_16292__overap_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    v___f_1366_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0;
    v___x_16292__overap_1367_ = lean_panic_fn_borrowed(v___f_1366_, v_msg_1360_);
    lean_inc(v___y_1364_);
    lean_inc_ref(v___y_1363_);
    lean_inc(v___y_1362_);
    lean_inc_ref(v___y_1361_);
    v___x_1368_ = lean_apply_5(
        v___x_16292__overap_1367_,
        v___y_1361_,
        v___y_1362_,
        v___y_1363_,
        v___y_1364_,
        lean_box(0),
    );
    return v___x_1368_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(
    mut v_msg_1369_: *mut LeanObject,
    mut v___y_1370_: *mut LeanObject,
    mut v___y_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
    mut v___y_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_res_1375_ =
        l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(
            v_msg_1369_,
            v___y_1370_,
            v___y_1371_,
            v___y_1372_,
            v___y_1373_,
        );
    lean_dec(v___y_1373_);
    lean_dec_ref(v___y_1372_);
    lean_dec(v___y_1371_);
    lean_dec_ref(v___y_1370_);
    return v_res_1375_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(
    mut v_msg_1376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lean_instInhabitedLocalDecl_default;
    v___x_1378_ = lean_panic_fn_borrowed(v___x_1377_, v_msg_1376_);
    return v___x_1378_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(
    mut v_mode_1380_: u8,
    mut v_a_u2081_1381_: *mut LeanObject,
    mut v_a_u2082_1382_: *mut LeanObject,
    mut v_b_u2081_1383_: *mut LeanObject,
    mut v_b_u2082_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_b_u2081_1383_);
                lean_inc_ref(v_a_u2081_1381_);
                v___x_1390_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_1380_,
                    v_a_u2081_1381_,
                    v_b_u2081_1383_,
                    v_a_1385_,
                    v_a_1386_,
                    v_a_1387_,
                    v_a_1388_,
                );
                if lean_obj_tag(v___x_1390_) == 0 {
                    v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
                    lean_inc(v_a_1391_);
                    v___x_1392_ = (lean_unbox(v_a_1391_) as u8);
                    if v___x_1392_ == 0 {
                        lean_dec_ref_known(v___x_1390_, 1);
                        v___x_1393_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1380_,
                            v_b_u2081_1383_,
                            v_a_u2081_1381_,
                            v_a_1385_,
                            v_a_1386_,
                            v_a_1387_,
                            v_a_1388_,
                        );
                        if lean_obj_tag(v___x_1393_) == 0 {
                            v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
                            v_isSharedCheck_1403_ = (!lean_is_exclusive(v___x_1393_)) as u8;
                            if v_isSharedCheck_1403_ == 0 {
                                v___x_1396_ = v___x_1393_;
                                v_isShared_1397_ = v_isSharedCheck_1403_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1394_);
                                lean_dec(v___x_1393_);
                                v___x_1396_ = lean_box(0);
                                v_isShared_1397_ = v_isSharedCheck_1403_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1391_);
                            lean_dec_ref(v_b_u2082_1384_);
                            lean_dec_ref(v_a_u2082_1382_);
                            return v___x_1393_;
                        }
                    } else {
                        lean_dec(v_a_1391_);
                        lean_dec_ref(v_b_u2082_1384_);
                        lean_dec_ref(v_b_u2081_1383_);
                        lean_dec_ref(v_a_u2082_1382_);
                        lean_dec_ref(v_a_u2081_1381_);
                        return v___x_1390_;
                    }
                } else {
                    lean_dec_ref(v_b_u2082_1384_);
                    lean_dec_ref(v_b_u2081_1383_);
                    lean_dec_ref(v_a_u2082_1382_);
                    lean_dec_ref(v_a_u2081_1381_);
                    return v___x_1390_;
                }
            }
            1 => {
                v___x_1398_ = (lean_unbox(v_a_1394_) as u8);
                lean_dec(v_a_1394_);
                if v___x_1398_ == 0 {
                    lean_del_object(v___x_1396_);
                    lean_dec(v_a_1391_);
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
                    lean_dec_ref(v_b_u2082_1384_);
                    lean_dec_ref(v_a_u2082_1382_);
                    if v_isShared_1397_ == 0 {
                        lean_ctor_set(v___x_1396_, 0, v_a_1391_);
                        v___x_1401_ = v___x_1396_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1391_);
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
-> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2;
    v___x_1408_ = lean_unsigned_to_nat(14);
    v___x_1409_ = lean_unsigned_to_nat(22);
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
-> *mut LeanObject {
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1414_: *mut LeanObject = core::ptr::null_mut();
    v___x_1413_ = lean_box(0);
    v_dummy_1414_ = l_Lean_Expr_sort___override(v___x_1413_);
    return v_dummy_1414_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(
    mut v_upperBound_1418_: *mut LeanObject,
    mut v_a_1419_: *mut LeanObject,
    mut v___x_1420_: *mut LeanObject,
    mut v___x_1421_: *mut LeanObject,
    mut v_mode_1422_: u8,
    mut v_a_1423_: *mut LeanObject,
    mut v_b_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
    mut v___y_1426_: *mut LeanObject,
    mut v___y_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInstance_1439_: u8 = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_a_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1470_: u8 = 0;
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1476_: u8 = 0;
    let mut v_a_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1435_ = lean_nat_dec_lt(v_a_1423_, v_upperBound_1418_);
                if v___x_1435_ == 0 {
                    lean_dec(v_a_1423_);
                    v___x_1436_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1436_, 0, v_b_1424_);
                    return v___x_1436_;
                } else {
                    lean_dec_ref(v_b_1424_);
                    v___x_1437_ = l_Lean_Meta_instInhabitedParamInfo_default;
                    v___x_1438_ = lean_array_get_borrowed(v___x_1437_, v_a_1419_, v_a_1423_);
                    v_isInstance_1439_ = lean_ctor_get_uint8(
                        v___x_1438_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                    );
                    v___x_1440_ = lean_box(0);
                    v___x_1441_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    if v_isInstance_1439_ == 0 {
                        v___x_1442_ = l_Lean_instInhabitedExpr;
                        v___x_1443_ = lean_array_get_borrowed(v___x_1442_, v___x_1420_, v_a_1423_);
                        v___x_1444_ = lean_array_get_borrowed(v___x_1442_, v___x_1421_, v_a_1423_);
                        lean_inc(v___x_1444_);
                        lean_inc(v___x_1443_);
                        v___x_1445_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1422_,
                            v___x_1443_,
                            v___x_1444_,
                            v___y_1425_,
                            v___y_1426_,
                            v___y_1427_,
                            v___y_1428_,
                        );
                        if lean_obj_tag(v___x_1445_) == 0 {
                            v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
                            v_isSharedCheck_1476_ = (!lean_is_exclusive(v___x_1445_)) as u8;
                            if v_isSharedCheck_1476_ == 0 {
                                v___x_1448_ = v___x_1445_;
                                v_isShared_1449_ = v_isSharedCheck_1476_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1446_);
                                lean_dec(v___x_1445_);
                                v___x_1448_ = lean_box(0);
                                v_isShared_1449_ = v_isSharedCheck_1476_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1423_);
                            v_a_1477_ = lean_ctor_get(v___x_1445_, 0);
                            v_isSharedCheck_1484_ = (!lean_is_exclusive(v___x_1445_)) as u8;
                            if v_isSharedCheck_1484_ == 0 {
                                v___x_1479_ = v___x_1445_;
                                v_isShared_1480_ = v_isSharedCheck_1484_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_1477_);
                                lean_dec(v___x_1445_);
                                v___x_1479_ = lean_box(0);
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
                v___x_1432_ = lean_unsigned_to_nat(1);
                v___x_1433_ = lean_nat_add(v_a_1423_, v___x_1432_);
                lean_dec(v_a_1423_);
                lean_inc_ref(v_a_1431_);
                v_a_1423_ = v___x_1433_;
                v_b_1424_ = v_a_1431_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1450_ = (lean_unbox(v_a_1446_) as u8);
                if v___x_1450_ == 0 {
                    lean_del_object(v___x_1448_);
                    lean_inc(v___x_1443_);
                    lean_inc(v___x_1444_);
                    v___x_1451_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1422_,
                        v___x_1444_,
                        v___x_1443_,
                        v___y_1425_,
                        v___y_1426_,
                        v___y_1427_,
                        v___y_1428_,
                    );
                    if lean_obj_tag(v___x_1451_) == 0 {
                        v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
                        v_isSharedCheck_1462_ = (!lean_is_exclusive(v___x_1451_)) as u8;
                        if v_isSharedCheck_1462_ == 0 {
                            v___x_1454_ = v___x_1451_;
                            v_isShared_1455_ = v_isSharedCheck_1462_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1452_);
                            lean_dec(v___x_1451_);
                            v___x_1454_ = lean_box(0);
                            v_isShared_1455_ = v_isSharedCheck_1462_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1446_);
                        lean_dec(v_a_1423_);
                        v_a_1463_ = lean_ctor_get(v___x_1451_, 0);
                        v_isSharedCheck_1470_ = (!lean_is_exclusive(v___x_1451_)) as u8;
                        if v_isSharedCheck_1470_ == 0 {
                            v___x_1465_ = v___x_1451_;
                            v_isShared_1466_ = v_isSharedCheck_1470_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1463_);
                            lean_dec(v___x_1451_);
                            v___x_1465_ = lean_box(0);
                            v_isShared_1466_ = v_isSharedCheck_1470_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1423_);
                    v___x_1471_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1471_, 0, v_a_1446_);
                    v___x_1472_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                    lean_ctor_set(v___x_1472_, 1, v___x_1440_);
                    if v_isShared_1449_ == 0 {
                        lean_ctor_set(v___x_1448_, 0, v___x_1472_);
                        v___x_1474_ = v___x_1448_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
                        v___x_1474_ = v_reuseFailAlloc_1475_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1456_ = (lean_unbox(v_a_1452_) as u8);
                lean_dec(v_a_1452_);
                if v___x_1456_ == 0 {
                    lean_del_object(v___x_1454_);
                    lean_dec(v_a_1446_);
                    v_a_1431_ = v___x_1441_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_a_1423_);
                    v___x_1457_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1457_, 0, v_a_1446_);
                    v___x_1458_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1458_, 0, v___x_1457_);
                    lean_ctor_set(v___x_1458_, 1, v___x_1440_);
                    if v_isShared_1455_ == 0 {
                        lean_ctor_set(v___x_1454_, 0, v___x_1458_);
                        v___x_1460_ = v___x_1454_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
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
                    v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
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
                    v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
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
    mut v_upperBound_1485_: *mut LeanObject,
    mut v___x_1486_: *mut LeanObject,
    mut v___x_1487_: *mut LeanObject,
    mut v_mode_1488_: u8,
    mut v_a_1489_: *mut LeanObject,
    mut v_b_1490_: *mut LeanObject,
    mut v___y_1491_: *mut LeanObject,
    mut v___y_1492_: *mut LeanObject,
    mut v___y_1493_: *mut LeanObject,
    mut v___y_1494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1496_: u8 = 0;
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1523_: u8 = 0;
    let mut v_a_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1537_: u8 = 0;
    let mut v_a_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1496_ = lean_nat_dec_lt(v_a_1489_, v_upperBound_1485_);
                if v___x_1496_ == 0 {
                    lean_dec(v_a_1489_);
                    v___x_1497_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1497_, 0, v_b_1490_);
                    return v___x_1497_;
                } else {
                    lean_dec_ref(v_b_1490_);
                    v___x_1498_ = l_Lean_instInhabitedExpr;
                    v___x_1499_ = lean_array_get_borrowed(v___x_1498_, v___x_1486_, v_a_1489_);
                    v___x_1500_ = lean_array_get_borrowed(v___x_1498_, v___x_1487_, v_a_1489_);
                    lean_inc(v___x_1500_);
                    lean_inc(v___x_1499_);
                    v___x_1501_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1488_,
                        v___x_1499_,
                        v___x_1500_,
                        v___y_1491_,
                        v___y_1492_,
                        v___y_1493_,
                        v___y_1494_,
                    );
                    if lean_obj_tag(v___x_1501_) == 0 {
                        v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
                        v_isSharedCheck_1537_ = (!lean_is_exclusive(v___x_1501_)) as u8;
                        if v_isSharedCheck_1537_ == 0 {
                            v___x_1504_ = v___x_1501_;
                            v_isShared_1505_ = v_isSharedCheck_1537_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1502_);
                            lean_dec(v___x_1501_);
                            v___x_1504_ = lean_box(0);
                            v_isShared_1505_ = v_isSharedCheck_1537_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1489_);
                        v_a_1538_ = lean_ctor_get(v___x_1501_, 0);
                        v_isSharedCheck_1545_ = (!lean_is_exclusive(v___x_1501_)) as u8;
                        if v_isSharedCheck_1545_ == 0 {
                            v___x_1540_ = v___x_1501_;
                            v_isShared_1541_ = v_isSharedCheck_1545_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1538_);
                            lean_dec(v___x_1501_);
                            v___x_1540_ = lean_box(0);
                            v_isShared_1541_ = v_isSharedCheck_1545_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1506_ = lean_box(0);
                v___x_1507_ = (lean_unbox(v_a_1502_) as u8);
                if v___x_1507_ == 0 {
                    lean_del_object(v___x_1504_);
                    lean_inc(v___x_1499_);
                    lean_inc(v___x_1500_);
                    v___x_1508_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1488_,
                        v___x_1500_,
                        v___x_1499_,
                        v___y_1491_,
                        v___y_1492_,
                        v___y_1493_,
                        v___y_1494_,
                    );
                    if lean_obj_tag(v___x_1508_) == 0 {
                        v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
                        v_isSharedCheck_1523_ = (!lean_is_exclusive(v___x_1508_)) as u8;
                        if v_isSharedCheck_1523_ == 0 {
                            v___x_1511_ = v___x_1508_;
                            v_isShared_1512_ = v_isSharedCheck_1523_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1509_);
                            lean_dec(v___x_1508_);
                            v___x_1511_ = lean_box(0);
                            v_isShared_1512_ = v_isSharedCheck_1523_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1502_);
                        lean_dec(v_a_1489_);
                        v_a_1524_ = lean_ctor_get(v___x_1508_, 0);
                        v_isSharedCheck_1531_ = (!lean_is_exclusive(v___x_1508_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1526_ = v___x_1508_;
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1524_);
                            lean_dec(v___x_1508_);
                            v___x_1526_ = lean_box(0);
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1489_);
                    v___x_1532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1532_, 0, v_a_1502_);
                    v___x_1533_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1533_, 0, v___x_1532_);
                    lean_ctor_set(v___x_1533_, 1, v___x_1506_);
                    if v_isShared_1505_ == 0 {
                        lean_ctor_set(v___x_1504_, 0, v___x_1533_);
                        v___x_1535_ = v___x_1504_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
                        v___x_1535_ = v_reuseFailAlloc_1536_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1513_ = (lean_unbox(v_a_1509_) as u8);
                lean_dec(v_a_1509_);
                if v___x_1513_ == 0 {
                    lean_del_object(v___x_1511_);
                    lean_dec(v_a_1502_);
                    v___x_1514_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    v___x_1515_ = lean_unsigned_to_nat(1);
                    v___x_1516_ = lean_nat_add(v_a_1489_, v___x_1515_);
                    lean_dec(v_a_1489_);
                    v_a_1489_ = v___x_1516_;
                    v_b_1490_ = v___x_1514_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_1489_);
                    v___x_1518_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1518_, 0, v_a_1502_);
                    v___x_1519_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1519_, 0, v___x_1518_);
                    lean_ctor_set(v___x_1519_, 1, v___x_1506_);
                    if v_isShared_1512_ == 0 {
                        lean_ctor_set(v___x_1511_, 0, v___x_1519_);
                        v___x_1521_ = v___x_1511_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
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
                    v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
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
                    v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
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
    mut v_a_1547_: *mut LeanObject,
    mut v_b_1548_: *mut LeanObject,
    mut v_a_1549_: *mut LeanObject,
    mut v_a_1550_: *mut LeanObject,
    mut v_a_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_aFn_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bFn_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v_dummy_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v_fst_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1595_: u8 = 0;
    let mut v_fst_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut v_a_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_val_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1617_: u8 = 0;
    let mut v_a_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_a_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1636_: u8 = 0;
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut v_unused_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1649_: u8 = 0;
    let mut v_unused_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aFn_1554_ = l_Lean_Expr_getAppFn(v_a_1547_);
                v_bFn_1555_ = l_Lean_Expr_getAppFn(v_b_1548_);
                lean_inc_ref(v_bFn_1555_);
                lean_inc_ref(v_aFn_1554_);
                v___x_1556_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_1546_,
                    v_aFn_1554_,
                    v_bFn_1555_,
                    v_a_1549_,
                    v_a_1550_,
                    v_a_1551_,
                    v_a_1552_,
                );
                if lean_obj_tag(v___x_1556_) == 0 {
                    v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
                    v_isSharedCheck_1655_ = (!lean_is_exclusive(v___x_1556_)) as u8;
                    if v_isSharedCheck_1655_ == 0 {
                        v___x_1559_ = v___x_1556_;
                        v_isShared_1560_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1557_);
                        lean_dec(v___x_1556_);
                        v___x_1559_ = lean_box(0);
                        v_isShared_1560_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_bFn_1555_);
                    lean_dec_ref(v_aFn_1554_);
                    lean_dec_ref(v_b_1548_);
                    lean_dec_ref(v_a_1547_);
                    return v___x_1556_;
                }
            }
            1 => {
                v___x_1561_ = 1;
                v___x_1562_ = (lean_unbox(v_a_1557_) as u8);
                if v___x_1562_ == 0 {
                    lean_del_object(v___x_1559_);
                    lean_inc_ref(v_aFn_1554_);
                    v___x_1563_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1546_,
                        v_bFn_1555_,
                        v_aFn_1554_,
                        v_a_1549_,
                        v_a_1550_,
                        v_a_1551_,
                        v_a_1552_,
                    );
                    if lean_obj_tag(v___x_1563_) == 0 {
                        v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
                        lean_inc(v_a_1564_);
                        v___x_1565_ = (lean_unbox(v_a_1564_) as u8);
                        if v___x_1565_ == 0 {
                            lean_dec(v_a_1557_);
                            v_dummy_1566_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
                            v_nargs_1567_ = l_Lean_Expr_getAppNumArgs(v_a_1547_);
                            lean_inc(v_nargs_1567_);
                            v___x_1568_ = lean_mk_array(v_nargs_1567_, v_dummy_1566_);
                            v___x_1569_ = lean_unsigned_to_nat(1);
                            v___x_1570_ = lean_nat_sub(v_nargs_1567_, v___x_1569_);
                            lean_dec(v_nargs_1567_);
                            v___x_1571_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_a_1547_,
                                v___x_1568_,
                                v___x_1570_,
                            );
                            v_nargs_1572_ = l_Lean_Expr_getAppNumArgs(v_b_1548_);
                            lean_inc(v_nargs_1572_);
                            v___x_1573_ = lean_mk_array(v_nargs_1572_, v_dummy_1566_);
                            v___x_1574_ = lean_nat_sub(v_nargs_1572_, v___x_1569_);
                            lean_dec(v_nargs_1572_);
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
                                    lean_dec_ref_known(v___x_1563_, 1);
                                    v___x_1580_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_1554_, v___x_1576_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                                    if lean_obj_tag(v___x_1580_) == 0 {
                                        v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
                                        lean_inc(v_a_1581_);
                                        lean_dec_ref_known(v___x_1580_, 1);
                                        v___x_1582_ = lean_array_get_size(v_a_1581_);
                                        v___x_1583_ = lean_unsigned_to_nat(0);
                                        v___x_1584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                                        v___x_1585_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_1582_, v_a_1581_, v___x_1571_, v___x_1575_, v_mode_1546_, v___x_1583_, v___x_1584_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                                        lean_dec(v_a_1581_);
                                        if lean_obj_tag(v___x_1585_) == 0 {
                                            v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
                                            v_isSharedCheck_1617_ =
                                                (!lean_is_exclusive(v___x_1585_)) as u8;
                                            if v_isSharedCheck_1617_ == 0 {
                                                v___x_1588_ = v___x_1585_;
                                                v_isShared_1589_ = v_isSharedCheck_1617_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1586_);
                                                lean_dec(v___x_1585_);
                                                v___x_1588_ = lean_box(0);
                                                v_isShared_1589_ = v_isSharedCheck_1617_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_1575_);
                                            lean_dec_ref(v___x_1571_);
                                            lean_dec(v_a_1564_);
                                            v_a_1618_ = lean_ctor_get(v___x_1585_, 0);
                                            v_isSharedCheck_1625_ =
                                                (!lean_is_exclusive(v___x_1585_)) as u8;
                                            if v_isSharedCheck_1625_ == 0 {
                                                v___x_1620_ = v___x_1585_;
                                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                                state = 9;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1618_);
                                                lean_dec(v___x_1585_);
                                                v___x_1620_ = lean_box(0);
                                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_1575_);
                                        lean_dec_ref(v___x_1571_);
                                        lean_dec(v_a_1564_);
                                        v_a_1626_ = lean_ctor_get(v___x_1580_, 0);
                                        v_isSharedCheck_1633_ =
                                            (!lean_is_exclusive(v___x_1580_)) as u8;
                                        if v_isSharedCheck_1633_ == 0 {
                                            v___x_1628_ = v___x_1580_;
                                            v_isShared_1629_ = v_isSharedCheck_1633_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1626_);
                                            lean_dec(v___x_1580_);
                                            v___x_1628_ = lean_box(0);
                                            v_isShared_1629_ = v_isSharedCheck_1633_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_1575_);
                                    lean_dec_ref(v___x_1571_);
                                    lean_dec(v_a_1564_);
                                    lean_dec_ref(v_aFn_1554_);
                                    return v___x_1563_;
                                }
                            } else {
                                lean_dec_ref(v___x_1575_);
                                lean_dec_ref(v___x_1571_);
                                lean_dec(v_a_1564_);
                                lean_dec_ref(v_aFn_1554_);
                                v_isSharedCheck_1641_ = (!lean_is_exclusive(v___x_1563_)) as u8;
                                if v_isSharedCheck_1641_ == 0 {
                                    v_unused_1642_ = lean_ctor_get(v___x_1563_, 0);
                                    lean_dec(v_unused_1642_);
                                    v___x_1635_ = v___x_1563_;
                                    v_isShared_1636_ = v_isSharedCheck_1641_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_dec(v___x_1563_);
                                    v___x_1635_ = lean_box(0);
                                    v_isShared_1636_ = v_isSharedCheck_1641_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_1564_);
                            lean_dec_ref(v_aFn_1554_);
                            lean_dec_ref(v_b_1548_);
                            lean_dec_ref(v_a_1547_);
                            v_isSharedCheck_1649_ = (!lean_is_exclusive(v___x_1563_)) as u8;
                            if v_isSharedCheck_1649_ == 0 {
                                v_unused_1650_ = lean_ctor_get(v___x_1563_, 0);
                                lean_dec(v_unused_1650_);
                                v___x_1644_ = v___x_1563_;
                                v_isShared_1645_ = v_isSharedCheck_1649_;
                                state = 15;
                                continue;
                            } else {
                                lean_dec(v___x_1563_);
                                v___x_1644_ = lean_box(0);
                                v_isShared_1645_ = v_isSharedCheck_1649_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1557_);
                        lean_dec_ref(v_aFn_1554_);
                        lean_dec_ref(v_b_1548_);
                        lean_dec_ref(v_a_1547_);
                        return v___x_1563_;
                    }
                } else {
                    lean_dec(v_a_1557_);
                    lean_dec_ref(v_bFn_1555_);
                    lean_dec_ref(v_aFn_1554_);
                    lean_dec_ref(v_b_1548_);
                    lean_dec_ref(v_a_1547_);
                    v___x_1651_ = lean_box((v___x_1561_) as usize);
                    if v_isShared_1560_ == 0 {
                        lean_ctor_set(v___x_1559_, 0, v___x_1651_);
                        v___x_1653_ = v___x_1559_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
                        v___x_1653_ = v_reuseFailAlloc_1654_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1590_ = lean_ctor_get(v_a_1586_, 0);
                lean_inc(v_fst_1590_);
                lean_dec(v_a_1586_);
                if lean_obj_tag(v_fst_1590_) == 0 {
                    lean_del_object(v___x_1588_);
                    v___x_1591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_1576_, v___x_1571_, v___x_1575_, v_mode_1546_, v___x_1582_, v___x_1584_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
                    lean_dec_ref(v___x_1575_);
                    lean_dec_ref(v___x_1571_);
                    if lean_obj_tag(v___x_1591_) == 0 {
                        v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
                        v_isSharedCheck_1604_ = (!lean_is_exclusive(v___x_1591_)) as u8;
                        if v_isSharedCheck_1604_ == 0 {
                            v___x_1594_ = v___x_1591_;
                            v_isShared_1595_ = v_isSharedCheck_1604_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1592_);
                            lean_dec(v___x_1591_);
                            v___x_1594_ = lean_box(0);
                            v_isShared_1595_ = v_isSharedCheck_1604_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1564_);
                        v_a_1605_ = lean_ctor_get(v___x_1591_, 0);
                        v_isSharedCheck_1612_ = (!lean_is_exclusive(v___x_1591_)) as u8;
                        if v_isSharedCheck_1612_ == 0 {
                            v___x_1607_ = v___x_1591_;
                            v_isShared_1608_ = v_isSharedCheck_1612_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1605_);
                            lean_dec(v___x_1591_);
                            v___x_1607_ = lean_box(0);
                            v_isShared_1608_ = v_isSharedCheck_1612_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1575_);
                    lean_dec_ref(v___x_1571_);
                    lean_dec(v_a_1564_);
                    v_val_1613_ = lean_ctor_get(v_fst_1590_, 0);
                    lean_inc(v_val_1613_);
                    lean_dec_ref_known(v_fst_1590_, 1);
                    if v_isShared_1589_ == 0 {
                        lean_ctor_set(v___x_1588_, 0, v_val_1613_);
                        v___x_1615_ = v___x_1588_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_val_1613_);
                        v___x_1615_ = v_reuseFailAlloc_1616_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_1596_ = lean_ctor_get(v_a_1592_, 0);
                lean_inc(v_fst_1596_);
                lean_dec(v_a_1592_);
                if lean_obj_tag(v_fst_1596_) == 0 {
                    if v_isShared_1595_ == 0 {
                        lean_ctor_set(v___x_1594_, 0, v_a_1564_);
                        v___x_1598_ = v___x_1594_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1564_);
                        v___x_1598_ = v_reuseFailAlloc_1599_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1564_);
                    v_val_1600_ = lean_ctor_get(v_fst_1596_, 0);
                    lean_inc(v_val_1600_);
                    lean_dec_ref_known(v_fst_1596_, 1);
                    if v_isShared_1595_ == 0 {
                        lean_ctor_set(v___x_1594_, 0, v_val_1600_);
                        v___x_1602_ = v___x_1594_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
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
                    v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
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
                    v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
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
                    v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
                    v___x_1631_ = v_reuseFailAlloc_1632_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1631_;
            }
            13 => {
                v___x_1637_ = lean_box((v___x_1561_) as usize);
                if v_isShared_1636_ == 0 {
                    lean_ctor_set(v___x_1635_, 0, v___x_1637_);
                    v___x_1639_ = v___x_1635_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
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
                    lean_ctor_set(v___x_1644_, 0, v_a_1557_);
                    v___x_1647_ = v___x_1644_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1557_);
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
-> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6;
    v___x_1660_ = lean_unsigned_to_nat(27);
    v___x_1661_ = lean_unsigned_to_nat(152);
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
    mut v_a_1666_: *mut LeanObject,
    mut v_b_1667_: *mut LeanObject,
    mut v_a_1668_: *mut LeanObject,
    mut v_a_1669_: *mut LeanObject,
    mut v_a_1670_: *mut LeanObject,
    mut v_a_1671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___y_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut v_a_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut v_mvarId_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_1666_) {
                0 => {
                    v_deBruijnIndex_1683_ = lean_ctor_get(v_a_1666_, 0);
                    lean_inc(v_deBruijnIndex_1683_);
                    lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1684_ = l_Lean_Expr_bvarIdx_x21(v_b_1667_);
                    lean_dec_ref(v_b_1667_);
                    v___x_1685_ = lean_nat_dec_lt(v_deBruijnIndex_1683_, v___x_1684_);
                    lean_dec(v___x_1684_);
                    lean_dec(v_deBruijnIndex_1683_);
                    v___x_1686_ = lean_box((v___x_1685_) as usize);
                    v___x_1687_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1687_, 0, v___x_1686_);
                    return v___x_1687_;
                }
                1 => {
                    v_fvarId_1688_ = lean_ctor_get(v_a_1666_, 0);
                    lean_inc(v_fvarId_1688_);
                    lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1689_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_1688_, v_a_1668_);
                    if lean_obj_tag(v___x_1689_) == 0 {
                        v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
                        lean_inc(v_a_1690_);
                        lean_dec_ref_known(v___x_1689_, 1);
                        v___x_1691_ = l_Lean_Expr_fvarId_x21(v_b_1667_);
                        lean_dec_ref(v_b_1667_);
                        v___x_1692_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_1691_, v_a_1668_);
                        if lean_obj_tag(v___x_1692_) == 0 {
                            v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
                            v_isSharedCheck_1715_ = (!lean_is_exclusive(v___x_1692_)) as u8;
                            if v_isSharedCheck_1715_ == 0 {
                                v___x_1695_ = v___x_1692_;
                                v_isShared_1696_ = v_isSharedCheck_1715_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1693_);
                                lean_dec(v___x_1692_);
                                v___x_1695_ = lean_box(0);
                                v_isShared_1696_ = v_isSharedCheck_1715_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1690_);
                            v_a_1716_ = lean_ctor_get(v___x_1692_, 0);
                            v_isSharedCheck_1723_ = (!lean_is_exclusive(v___x_1692_)) as u8;
                            if v_isSharedCheck_1723_ == 0 {
                                v___x_1718_ = v___x_1692_;
                                v_isShared_1719_ = v_isSharedCheck_1723_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1716_);
                                lean_dec(v___x_1692_);
                                v___x_1718_ = lean_box(0);
                                v_isShared_1719_ = v_isSharedCheck_1723_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_1667_);
                        v_a_1724_ = lean_ctor_get(v___x_1689_, 0);
                        v_isSharedCheck_1731_ = (!lean_is_exclusive(v___x_1689_)) as u8;
                        if v_isSharedCheck_1731_ == 0 {
                            v___x_1726_ = v___x_1689_;
                            v_isShared_1727_ = v_isSharedCheck_1731_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1724_);
                            lean_dec(v___x_1689_);
                            v___x_1726_ = lean_box(0);
                            v_isShared_1727_ = v_isSharedCheck_1731_;
                            state = 8;
                            continue;
                        }
                    }
                }
                2 => {
                    v_mvarId_1732_ = lean_ctor_get(v_a_1666_, 0);
                    lean_inc(v_mvarId_1732_);
                    lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1733_ = l_Lean_Expr_mvarId_x21(v_b_1667_);
                    lean_dec_ref(v_b_1667_);
                    v___x_1734_ = l_Lean_Name_lt(v_mvarId_1732_, v___x_1733_);
                    lean_dec(v___x_1733_);
                    lean_dec(v_mvarId_1732_);
                    v___x_1735_ = lean_box((v___x_1734_) as usize);
                    v___x_1736_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1736_, 0, v___x_1735_);
                    return v___x_1736_;
                }
                3 => {
                    v_u_1737_ = lean_ctor_get(v_a_1666_, 0);
                    lean_inc(v_u_1737_);
                    lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1738_ = l_Lean_Expr_sortLevel_x21(v_b_1667_);
                    lean_dec_ref(v_b_1667_);
                    v___x_1739_ = l_Lean_Level_normLt(v_u_1737_, v___x_1738_);
                    lean_dec(v___x_1738_);
                    lean_dec(v_u_1737_);
                    v___x_1740_ = lean_box((v___x_1739_) as usize);
                    v___x_1741_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1741_, 0, v___x_1740_);
                    return v___x_1741_;
                }
                4 => {
                    v_declName_1742_ = lean_ctor_get(v_a_1666_, 0);
                    lean_inc(v_declName_1742_);
                    lean_dec_ref_known(v_a_1666_, 2);
                    v___x_1743_ = l_Lean_Expr_constName_x21(v_b_1667_);
                    lean_dec_ref(v_b_1667_);
                    v___x_1744_ = l_Lean_Name_lt(v_declName_1742_, v___x_1743_);
                    lean_dec(v___x_1743_);
                    lean_dec(v_declName_1742_);
                    v___x_1745_ = lean_box((v___x_1744_) as usize);
                    v___x_1746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1746_, 0, v___x_1745_);
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
                    v_value_1748_ = lean_ctor_get(v_a_1666_, 2);
                    lean_inc_ref(v_value_1748_);
                    v_body_1749_ = lean_ctor_get(v_a_1666_, 3);
                    lean_inc_ref(v_body_1749_);
                    lean_dec_ref_known(v_a_1666_, 4);
                    v___x_1750_ = l_Lean_Expr_letValue_x21(v_b_1667_);
                    v___x_1751_ = l_Lean_Expr_letBody_x21(v_b_1667_);
                    lean_dec_ref(v_b_1667_);
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
                    v_a_1753_ = lean_ctor_get(v_a_1666_, 0);
                    lean_inc_ref(v_a_1753_);
                    lean_dec_ref_known(v_a_1666_, 1);
                    v___x_1754_ = l_Lean_Expr_litValue_x21(v_b_1667_);
                    lean_dec_ref(v_b_1667_);
                    v___x_1755_ = l_Lean_Literal_lt(v_a_1753_, v___x_1754_);
                    lean_dec_ref(v___x_1754_);
                    lean_dec_ref(v_a_1753_);
                    v___x_1756_ = lean_box((v___x_1755_) as usize);
                    v___x_1757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1757_, 0, v___x_1756_);
                    return v___x_1757_;
                }
                10 => {
                    lean_dec_ref_known(v_a_1666_, 2);
                    lean_dec_ref(v_b_1667_);
                    v___x_1758_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
                    v___x_1759_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_1758_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
                    return v___x_1759_;
                }
                11 => {
                    v_idx_1760_ = lean_ctor_get(v_a_1666_, 1);
                    lean_inc(v_idx_1760_);
                    v_struct_1761_ = lean_ctor_get(v_a_1666_, 2);
                    lean_inc_ref(v_struct_1761_);
                    lean_dec_ref_known(v_a_1666_, 3);
                    v___x_1762_ = l_Lean_Expr_projIdx_x21(v_b_1667_);
                    v___x_1763_ = lean_nat_dec_eq(v_idx_1760_, v___x_1762_);
                    if v___x_1763_ == 0 {
                        lean_dec_ref(v_struct_1761_);
                        lean_dec_ref(v_b_1667_);
                        v___x_1764_ = lean_nat_dec_lt(v_idx_1760_, v___x_1762_);
                        lean_dec(v___x_1762_);
                        lean_dec(v_idx_1760_);
                        v___x_1765_ = lean_box((v___x_1764_) as usize);
                        v___x_1766_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1766_, 0, v___x_1765_);
                        return v___x_1766_;
                    } else {
                        lean_dec(v___x_1762_);
                        lean_dec(v_idx_1760_);
                        v___x_1767_ = l_Lean_Expr_projExpr_x21(v_b_1667_);
                        lean_dec_ref(v_b_1667_);
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
                    v_binderType_1769_ = lean_ctor_get(v_a_1666_, 1);
                    lean_inc_ref(v_binderType_1769_);
                    v_body_1770_ = lean_ctor_get(v_a_1666_, 2);
                    lean_inc_ref(v_body_1770_);
                    lean_dec_ref(v_a_1666_);
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
                lean_dec_ref(v_b_1667_);
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
                if lean_obj_tag(v_a_1690_) == 0 {
                    v___x_1712_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
                    v___x_1713_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_1712_);
                    v___y_1707_ = v___x_1713_;
                    state = 5;
                    continue;
                } else {
                    v_val_1714_ = lean_ctor_get(v_a_1690_, 0);
                    lean_inc(v_val_1714_);
                    lean_dec_ref_known(v_a_1690_, 1);
                    v___y_1707_ = v_val_1714_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_1700_ = l_Lean_LocalDecl_index(v___y_1699_);
                lean_dec_ref(v___y_1699_);
                v___x_1701_ = lean_nat_dec_lt(v___y_1698_, v___x_1700_);
                lean_dec(v___x_1700_);
                lean_dec(v___y_1698_);
                v___x_1702_ = lean_box((v___x_1701_) as usize);
                if v_isShared_1696_ == 0 {
                    lean_ctor_set(v___x_1695_, 0, v___x_1702_);
                    v___x_1704_ = v___x_1695_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
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
                lean_dec_ref(v___y_1707_);
                if lean_obj_tag(v_a_1693_) == 0 {
                    v___x_1709_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
                    v___x_1710_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_1709_);
                    v___y_1698_ = v___x_1708_;
                    v___y_1699_ = v___x_1710_;
                    state = 3;
                    continue;
                } else {
                    v_val_1711_ = lean_ctor_get(v_a_1693_, 0);
                    lean_inc(v_val_1711_);
                    lean_dec_ref_known(v_a_1693_, 1);
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
                    v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
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
                    v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
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
    mut v_a_1772_: *mut LeanObject,
    mut v_b_1773_: *mut LeanObject,
    mut v_a_1774_: *mut LeanObject,
    mut v_a_1775_: *mut LeanObject,
    mut v_a_1776_: *mut LeanObject,
    mut v_a_1777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1811_: u8 = 0;
    let mut v_unused_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1779_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0;
                v___x_1780_ = l_Lean_Core_checkSystem(v___x_1779_, v_a_1776_, v_a_1777_);
                if lean_obj_tag(v___x_1780_) == 0 {
                    lean_dec_ref_known(v___x_1780_, 1);
                    lean_inc_ref(v_a_1772_);
                    lean_inc_ref(v_b_1773_);
                    v___x_1781_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
                        v_mode_1771_,
                        v_b_1773_,
                        v_a_1772_,
                        v_a_1774_,
                        v_a_1775_,
                        v_a_1776_,
                        v_a_1777_,
                    );
                    if lean_obj_tag(v___x_1781_) == 0 {
                        v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
                        lean_inc(v_a_1782_);
                        v___x_1783_ = 1;
                        v___x_1784_ = (lean_unbox(v_a_1782_) as u8);
                        if v___x_1784_ == 0 {
                            v___x_1785_ = l_Lean_Expr_ctorWeight(v_b_1773_);
                            v___x_1786_ = l_Lean_Expr_ctorWeight(v_a_1772_);
                            v___x_1787_ = lean_uint8_dec_lt(v___x_1785_, v___x_1786_);
                            if v___x_1787_ == 0 {
                                lean_dec_ref_known(v___x_1781_, 1);
                                lean_inc_ref(v_b_1773_);
                                lean_inc_ref(v_a_1772_);
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
                                if lean_obj_tag(v___x_1788_) == 0 {
                                    v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
                                    v_isSharedCheck_1803_ = (!lean_is_exclusive(v___x_1788_)) as u8;
                                    if v_isSharedCheck_1803_ == 0 {
                                        v___x_1791_ = v___x_1788_;
                                        v_isShared_1792_ = v_isSharedCheck_1803_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1789_);
                                        lean_dec(v___x_1788_);
                                        v___x_1791_ = lean_box(0);
                                        v_isShared_1792_ = v_isSharedCheck_1803_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1782_);
                                    lean_dec_ref(v_b_1773_);
                                    lean_dec_ref(v_a_1772_);
                                    return v___x_1788_;
                                }
                            } else {
                                lean_dec(v_a_1782_);
                                lean_dec_ref(v_b_1773_);
                                lean_dec_ref(v_a_1772_);
                                return v___x_1781_;
                            }
                        } else {
                            lean_dec(v_a_1782_);
                            lean_dec_ref(v_b_1773_);
                            lean_dec_ref(v_a_1772_);
                            v_isSharedCheck_1811_ = (!lean_is_exclusive(v___x_1781_)) as u8;
                            if v_isSharedCheck_1811_ == 0 {
                                v_unused_1812_ = lean_ctor_get(v___x_1781_, 0);
                                lean_dec(v_unused_1812_);
                                v___x_1805_ = v___x_1781_;
                                v_isShared_1806_ = v_isSharedCheck_1811_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v___x_1781_);
                                v___x_1805_ = lean_box(0);
                                v_isShared_1806_ = v_isSharedCheck_1811_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_1773_);
                        lean_dec_ref(v_a_1772_);
                        return v___x_1781_;
                    }
                } else {
                    lean_dec_ref(v_b_1773_);
                    lean_dec_ref(v_a_1772_);
                    v_a_1813_ = lean_ctor_get(v___x_1780_, 0);
                    v_isSharedCheck_1820_ = (!lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1815_ = v___x_1780_;
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1813_);
                        lean_dec(v___x_1780_);
                        v___x_1815_ = lean_box(0);
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1793_ = (lean_unbox(v_a_1789_) as u8);
                lean_dec(v_a_1789_);
                if v___x_1793_ == 0 {
                    lean_dec_ref(v_b_1773_);
                    lean_dec_ref(v_a_1772_);
                    if v_isShared_1792_ == 0 {
                        lean_ctor_set(v___x_1791_, 0, v_a_1782_);
                        v___x_1795_ = v___x_1791_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1782_);
                        v___x_1795_ = v_reuseFailAlloc_1796_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1782_);
                    v___x_1797_ = lean_uint8_dec_lt(v___x_1786_, v___x_1785_);
                    if v___x_1797_ == 0 {
                        lean_del_object(v___x_1791_);
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
                        lean_dec_ref(v_b_1773_);
                        lean_dec_ref(v_a_1772_);
                        v___x_1799_ = lean_box((v___x_1783_) as usize);
                        if v_isShared_1792_ == 0 {
                            lean_ctor_set(v___x_1791_, 0, v___x_1799_);
                            v___x_1801_ = v___x_1791_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
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
                v___x_1807_ = lean_box((v___x_1783_) as usize);
                if v_isShared_1806_ == 0 {
                    lean_ctor_set(v___x_1805_, 0, v___x_1807_);
                    v___x_1809_ = v___x_1805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
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
                    v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
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
    mut v_a_1822_: *mut LeanObject,
    mut v_b_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_a_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1852_: u8 = 0;
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
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
                            if lean_obj_tag(v___x_1832_) == 0 {
                                v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
                                lean_inc(v_a_1833_);
                                lean_dec_ref_known(v___x_1832_, 1);
                                v___x_1834_ =
                                    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(
                                        v_mode_1821_,
                                        v_b_1823_,
                                        v_a_1824_,
                                        v_a_1825_,
                                        v_a_1826_,
                                        v_a_1827_,
                                    );
                                if lean_obj_tag(v___x_1834_) == 0 {
                                    v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
                                    lean_inc(v_a_1835_);
                                    lean_dec_ref_known(v___x_1834_, 1);
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
                                    lean_dec(v_a_1833_);
                                    v_a_1837_ = lean_ctor_get(v___x_1834_, 0);
                                    v_isSharedCheck_1844_ = (!lean_is_exclusive(v___x_1834_)) as u8;
                                    if v_isSharedCheck_1844_ == 0 {
                                        v___x_1839_ = v___x_1834_;
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1837_);
                                        lean_dec(v___x_1834_);
                                        v___x_1839_ = lean_box(0);
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_b_1823_);
                                v_a_1845_ = lean_ctor_get(v___x_1832_, 0);
                                v_isSharedCheck_1852_ = (!lean_is_exclusive(v___x_1832_)) as u8;
                                if v_isSharedCheck_1852_ == 0 {
                                    v___x_1847_ = v___x_1832_;
                                    v_isShared_1848_ = v_isSharedCheck_1852_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1845_);
                                    lean_dec(v___x_1832_);
                                    v___x_1847_ = lean_box(0);
                                    v_isShared_1848_ = v_isSharedCheck_1852_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_1853_ = l_Lean_Expr_mdataExpr_x21(v_b_1823_);
                            lean_dec_ref(v_b_1823_);
                            v_b_1823_ = v___x_1853_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1855_ = l_Lean_Expr_mdataExpr_x21(v_a_1822_);
                        lean_dec_ref(v_a_1822_);
                        v_a_1822_ = v___x_1855_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_b_1823_);
                    lean_dec_ref(v_a_1822_);
                    v___x_1857_ = 0;
                    v___x_1858_ = lean_box((v___x_1857_) as usize);
                    v___x_1859_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1859_, 0, v___x_1858_);
                    return v___x_1859_;
                }
            }
            1 => {
                if v_isShared_1840_ == 0 {
                    v___x_1842_ = v___x_1839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
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
                    v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
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
    mut v_upperBound_1860_: *mut LeanObject,
    mut v_a_1861_: *mut LeanObject,
    mut v_args_1862_: *mut LeanObject,
    mut v_mode_1863_: u8,
    mut v_b_1864_: *mut LeanObject,
    mut v_a_1865_: *mut LeanObject,
    mut v_b_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInstance_1881_: u8 = 0;
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1891_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_a_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1877_ = lean_nat_dec_lt(v_a_1865_, v_upperBound_1860_);
                if v___x_1877_ == 0 {
                    lean_dec(v_a_1865_);
                    lean_dec_ref(v_b_1864_);
                    v___x_1878_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1878_, 0, v_b_1866_);
                    return v___x_1878_;
                } else {
                    lean_dec_ref(v_b_1866_);
                    v___x_1879_ = l_Lean_Meta_instInhabitedParamInfo_default;
                    v___x_1880_ = lean_array_get_borrowed(v___x_1879_, v_a_1861_, v_a_1865_);
                    v_isInstance_1881_ = lean_ctor_get_uint8(
                        v___x_1880_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                    );
                    v___x_1882_ = lean_box(0);
                    v___x_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    if v_isInstance_1881_ == 0 {
                        v___x_1884_ = l_Lean_instInhabitedExpr;
                        v___x_1885_ = lean_array_get_borrowed(v___x_1884_, v_args_1862_, v_a_1865_);
                        lean_inc_ref(v_b_1864_);
                        lean_inc(v___x_1885_);
                        v___x_1886_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                            v_mode_1863_,
                            v___x_1885_,
                            v_b_1864_,
                            v___y_1867_,
                            v___y_1868_,
                            v___y_1869_,
                            v___y_1870_,
                        );
                        if lean_obj_tag(v___x_1886_) == 0 {
                            v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
                            v_isSharedCheck_1897_ = (!lean_is_exclusive(v___x_1886_)) as u8;
                            if v_isSharedCheck_1897_ == 0 {
                                v___x_1889_ = v___x_1886_;
                                v_isShared_1890_ = v_isSharedCheck_1897_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1887_);
                                lean_dec(v___x_1886_);
                                v___x_1889_ = lean_box(0);
                                v_isShared_1890_ = v_isSharedCheck_1897_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1865_);
                            lean_dec_ref(v_b_1864_);
                            v_a_1898_ = lean_ctor_get(v___x_1886_, 0);
                            v_isSharedCheck_1905_ = (!lean_is_exclusive(v___x_1886_)) as u8;
                            if v_isSharedCheck_1905_ == 0 {
                                v___x_1900_ = v___x_1886_;
                                v_isShared_1901_ = v_isSharedCheck_1905_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1898_);
                                lean_dec(v___x_1886_);
                                v___x_1900_ = lean_box(0);
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
                v___x_1874_ = lean_unsigned_to_nat(1);
                v___x_1875_ = lean_nat_add(v_a_1865_, v___x_1874_);
                lean_dec(v_a_1865_);
                lean_inc_ref(v_a_1873_);
                v_a_1865_ = v___x_1875_;
                v_b_1866_ = v_a_1873_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1891_ = (lean_unbox(v_a_1887_) as u8);
                if v___x_1891_ == 0 {
                    lean_dec(v_a_1865_);
                    lean_dec_ref(v_b_1864_);
                    v___x_1892_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1892_, 0, v_a_1887_);
                    v___x_1893_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1893_, 0, v___x_1892_);
                    lean_ctor_set(v___x_1893_, 1, v___x_1882_);
                    if v_isShared_1890_ == 0 {
                        lean_ctor_set(v___x_1889_, 0, v___x_1893_);
                        v___x_1895_ = v___x_1889_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
                        v___x_1895_ = v_reuseFailAlloc_1896_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1889_);
                    lean_dec(v_a_1887_);
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
                    v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
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
    mut v_upperBound_1906_: *mut LeanObject,
    mut v_args_1907_: *mut LeanObject,
    mut v_mode_1908_: u8,
    mut v_b_1909_: *mut LeanObject,
    mut v_a_1910_: *mut LeanObject,
    mut v_b_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v_a_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ = lean_nat_dec_lt(v_a_1910_, v_upperBound_1906_);
                if v___x_1917_ == 0 {
                    lean_dec(v_a_1910_);
                    lean_dec_ref(v_b_1909_);
                    v___x_1918_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1918_, 0, v_b_1911_);
                    return v___x_1918_;
                } else {
                    lean_dec_ref(v_b_1911_);
                    v___x_1919_ = lean_array_fget_borrowed(v_args_1907_, v_a_1910_);
                    lean_inc_ref(v_b_1909_);
                    lean_inc(v___x_1919_);
                    v___x_1920_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_1908_,
                        v___x_1919_,
                        v_b_1909_,
                        v___y_1912_,
                        v___y_1913_,
                        v___y_1914_,
                        v___y_1915_,
                    );
                    if lean_obj_tag(v___x_1920_) == 0 {
                        v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
                        v_isSharedCheck_1936_ = (!lean_is_exclusive(v___x_1920_)) as u8;
                        if v_isSharedCheck_1936_ == 0 {
                            v___x_1923_ = v___x_1920_;
                            v_isShared_1924_ = v_isSharedCheck_1936_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1921_);
                            lean_dec(v___x_1920_);
                            v___x_1923_ = lean_box(0);
                            v_isShared_1924_ = v_isSharedCheck_1936_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1910_);
                        lean_dec_ref(v_b_1909_);
                        v_a_1937_ = lean_ctor_get(v___x_1920_, 0);
                        v_isSharedCheck_1944_ = (!lean_is_exclusive(v___x_1920_)) as u8;
                        if v_isSharedCheck_1944_ == 0 {
                            v___x_1939_ = v___x_1920_;
                            v_isShared_1940_ = v_isSharedCheck_1944_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1937_);
                            lean_dec(v___x_1920_);
                            v___x_1939_ = lean_box(0);
                            v_isShared_1940_ = v_isSharedCheck_1944_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1925_ = lean_box(0);
                v___x_1926_ = (lean_unbox(v_a_1921_) as u8);
                if v___x_1926_ == 0 {
                    lean_dec(v_a_1910_);
                    lean_dec_ref(v_b_1909_);
                    v___x_1927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1927_, 0, v_a_1921_);
                    v___x_1928_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1928_, 0, v___x_1927_);
                    lean_ctor_set(v___x_1928_, 1, v___x_1925_);
                    if v_isShared_1924_ == 0 {
                        lean_ctor_set(v___x_1923_, 0, v___x_1928_);
                        v___x_1930_ = v___x_1923_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                        v___x_1930_ = v_reuseFailAlloc_1931_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1923_);
                    lean_dec(v_a_1921_);
                    v___x_1932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                    v___x_1933_ = lean_unsigned_to_nat(1);
                    v___x_1934_ = lean_nat_add(v_a_1910_, v___x_1933_);
                    lean_dec(v_a_1910_);
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
                    v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
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
    mut v_b_1946_: *mut LeanObject,
    mut v_x_1947_: *mut LeanObject,
    mut v_x_1948_: *mut LeanObject,
    mut v_x_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v_fst_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v_fst_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut v_a_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut v_val_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_a_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1947_) == 5 {
                    v_fn_1955_ = lean_ctor_get(v_x_1947_, 0);
                    lean_inc_ref(v_fn_1955_);
                    v_arg_1956_ = lean_ctor_get(v_x_1947_, 1);
                    lean_inc_ref(v_arg_1956_);
                    lean_dec_ref_known(v_x_1947_, 2);
                    v___x_1957_ = lean_array_set(v_x_1948_, v_x_1949_, v_arg_1956_);
                    v___x_1958_ = lean_unsigned_to_nat(1);
                    v___x_1959_ = lean_nat_sub(v_x_1949_, v___x_1958_);
                    lean_dec(v_x_1949_);
                    v_x_1947_ = v_fn_1955_;
                    v_x_1948_ = v___x_1957_;
                    v_x_1949_ = v___x_1959_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_1949_);
                    v___x_1961_ = lean_array_get_size(v_x_1948_);
                    v___x_1962_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(
                        v_x_1947_,
                        v___x_1961_,
                        v___y_1950_,
                        v___y_1951_,
                        v___y_1952_,
                        v___y_1953_,
                    );
                    if lean_obj_tag(v___x_1962_) == 0 {
                        v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
                        lean_inc(v_a_1963_);
                        lean_dec_ref_known(v___x_1962_, 1);
                        v___x_1964_ = lean_array_get_size(v_a_1963_);
                        v___x_1965_ = lean_unsigned_to_nat(0);
                        v___x_1966_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0;
                        lean_inc_ref(v_b_1946_);
                        v___x_1967_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_1964_, v_a_1963_, v_x_1948_, v_mode_1945_, v_b_1946_, v___x_1965_, v___x_1966_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
                        lean_dec(v_a_1963_);
                        if lean_obj_tag(v___x_1967_) == 0 {
                            v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
                            v_isSharedCheck_2001_ = (!lean_is_exclusive(v___x_1967_)) as u8;
                            if v_isSharedCheck_2001_ == 0 {
                                v___x_1970_ = v___x_1967_;
                                v_isShared_1971_ = v_isSharedCheck_2001_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1968_);
                                lean_dec(v___x_1967_);
                                v___x_1970_ = lean_box(0);
                                v_isShared_1971_ = v_isSharedCheck_2001_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_x_1948_);
                            lean_dec_ref(v_b_1946_);
                            v_a_2002_ = lean_ctor_get(v___x_1967_, 0);
                            v_isSharedCheck_2009_ = (!lean_is_exclusive(v___x_1967_)) as u8;
                            if v_isSharedCheck_2009_ == 0 {
                                v___x_2004_ = v___x_1967_;
                                v_isShared_2005_ = v_isSharedCheck_2009_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2002_);
                                lean_dec(v___x_1967_);
                                v___x_2004_ = lean_box(0);
                                v_isShared_2005_ = v_isSharedCheck_2009_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_x_1948_);
                        lean_dec_ref(v_b_1946_);
                        v_a_2010_ = lean_ctor_get(v___x_1962_, 0);
                        v_isSharedCheck_2017_ = (!lean_is_exclusive(v___x_1962_)) as u8;
                        if v_isSharedCheck_2017_ == 0 {
                            v___x_2012_ = v___x_1962_;
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2010_);
                            lean_dec(v___x_1962_);
                            v___x_2012_ = lean_box(0);
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1972_ = lean_ctor_get(v_a_1968_, 0);
                lean_inc(v_fst_1972_);
                lean_dec(v_a_1968_);
                if lean_obj_tag(v_fst_1972_) == 0 {
                    lean_del_object(v___x_1970_);
                    v___x_1973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_1961_, v_x_1948_, v_mode_1945_, v_b_1946_, v___x_1964_, v___x_1966_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
                    lean_dec_ref(v_x_1948_);
                    if lean_obj_tag(v___x_1973_) == 0 {
                        v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
                        v_isSharedCheck_1988_ = (!lean_is_exclusive(v___x_1973_)) as u8;
                        if v_isSharedCheck_1988_ == 0 {
                            v___x_1976_ = v___x_1973_;
                            v_isShared_1977_ = v_isSharedCheck_1988_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1974_);
                            lean_dec(v___x_1973_);
                            v___x_1976_ = lean_box(0);
                            v_isShared_1977_ = v_isSharedCheck_1988_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1989_ = lean_ctor_get(v___x_1973_, 0);
                        v_isSharedCheck_1996_ = (!lean_is_exclusive(v___x_1973_)) as u8;
                        if v_isSharedCheck_1996_ == 0 {
                            v___x_1991_ = v___x_1973_;
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1989_);
                            lean_dec(v___x_1973_);
                            v___x_1991_ = lean_box(0);
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_1948_);
                    lean_dec_ref(v_b_1946_);
                    v_val_1997_ = lean_ctor_get(v_fst_1972_, 0);
                    lean_inc(v_val_1997_);
                    lean_dec_ref_known(v_fst_1972_, 1);
                    if v_isShared_1971_ == 0 {
                        lean_ctor_set(v___x_1970_, 0, v_val_1997_);
                        v___x_1999_ = v___x_1970_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1997_);
                        v___x_1999_ = v_reuseFailAlloc_2000_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1978_ = lean_ctor_get(v_a_1974_, 0);
                lean_inc(v_fst_1978_);
                lean_dec(v_a_1974_);
                if lean_obj_tag(v_fst_1978_) == 0 {
                    v___x_1979_ = 1;
                    v___x_1980_ = lean_box((v___x_1979_) as usize);
                    if v_isShared_1977_ == 0 {
                        lean_ctor_set(v___x_1976_, 0, v___x_1980_);
                        v___x_1982_ = v___x_1976_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
                        v___x_1982_ = v_reuseFailAlloc_1983_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1984_ = lean_ctor_get(v_fst_1978_, 0);
                    lean_inc(v_val_1984_);
                    lean_dec_ref_known(v_fst_1978_, 1);
                    if v_isShared_1977_ == 0 {
                        lean_ctor_set(v___x_1976_, 0, v_val_1984_);
                        v___x_1986_ = v___x_1976_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_val_1984_);
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
                    v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
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
                    v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
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
                    v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
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
    mut v_a_2019_: *mut LeanObject,
    mut v_b_2020_: *mut LeanObject,
    mut v_a_2021_: *mut LeanObject,
    mut v_a_2022_: *mut LeanObject,
    mut v_a_2023_: *mut LeanObject,
    mut v_a_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_2019_) {
                11 => {
                    v_struct_2037_ = lean_ctor_get(v_a_2019_, 2);
                    lean_inc_ref(v_struct_2037_);
                    lean_dec_ref_known(v_a_2019_, 3);
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
                    v_dummy_2039_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once), _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
                    v_nargs_2040_ = l_Lean_Expr_getAppNumArgs(v_a_2019_);
                    lean_inc(v_nargs_2040_);
                    v___x_2041_ = lean_mk_array(v_nargs_2040_, v_dummy_2039_);
                    v___x_2042_ = lean_unsigned_to_nat(1);
                    v___x_2043_ = lean_nat_sub(v_nargs_2040_, v___x_2042_);
                    lean_dec(v_nargs_2040_);
                    v___x_2044_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_2018_, v_b_2020_, v_a_2019_, v___x_2041_, v___x_2043_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
                    return v___x_2044_;
                }
                6 => {
                    v_binderType_2045_ = lean_ctor_get(v_a_2019_, 1);
                    lean_inc_ref(v_binderType_2045_);
                    v_body_2046_ = lean_ctor_get(v_a_2019_, 2);
                    lean_inc_ref(v_body_2046_);
                    lean_dec_ref_known(v_a_2019_, 3);
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
                    v_binderType_2047_ = lean_ctor_get(v_a_2019_, 1);
                    lean_inc_ref(v_binderType_2047_);
                    v_body_2048_ = lean_ctor_get(v_a_2019_, 2);
                    lean_inc_ref(v_body_2048_);
                    lean_dec_ref_known(v_a_2019_, 3);
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
                    v_value_2049_ = lean_ctor_get(v_a_2019_, 2);
                    lean_inc_ref(v_value_2049_);
                    v_body_2050_ = lean_ctor_get(v_a_2019_, 3);
                    lean_inc_ref(v_body_2050_);
                    lean_dec_ref_known(v_a_2019_, 4);
                    lean_inc_ref(v_b_2020_);
                    v___x_2051_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                        v_mode_2018_,
                        v_value_2049_,
                        v_b_2020_,
                        v_a_2021_,
                        v_a_2022_,
                        v_a_2023_,
                        v_a_2024_,
                    );
                    if lean_obj_tag(v___x_2051_) == 0 {
                        v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
                        lean_inc(v_a_2052_);
                        v___x_2053_ = (lean_unbox(v_a_2052_) as u8);
                        lean_dec(v_a_2052_);
                        if v___x_2053_ == 0 {
                            lean_dec_ref(v_body_2050_);
                            lean_dec_ref(v_b_2020_);
                            return v___x_2051_;
                        } else {
                            lean_dec_ref_known(v___x_2051_, 1);
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
                        lean_dec_ref(v_body_2050_);
                        lean_dec_ref(v_b_2020_);
                        return v___x_2051_;
                    }
                }
                _ => {
                    lean_dec_ref(v_b_2020_);
                    lean_dec_ref(v_a_2019_);
                    v___x_2055_ = 1;
                    v___x_2056_ = lean_box((v___x_2055_) as usize);
                    v___x_2057_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2057_, 0, v___x_2056_);
                    return v___x_2057_;
                }
            },
            1 => {
                lean_inc_ref(v_b_2020_);
                v___x_2033_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
                    v_mode_2018_,
                    v_d_2027_,
                    v_b_2020_,
                    v___y_2029_,
                    v___y_2030_,
                    v___y_2031_,
                    v___y_2032_,
                );
                if lean_obj_tag(v___x_2033_) == 0 {
                    v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
                    lean_inc(v_a_2034_);
                    v___x_2035_ = (lean_unbox(v_a_2034_) as u8);
                    lean_dec(v_a_2034_);
                    if v___x_2035_ == 0 {
                        lean_dec_ref(v_e_2028_);
                        lean_dec_ref(v_b_2020_);
                        return v___x_2033_;
                    } else {
                        lean_dec_ref_known(v___x_2033_, 1);
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
                    lean_dec_ref(v_e_2028_);
                    lean_dec_ref(v_b_2020_);
                    return v___x_2033_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
    mut v_mode_2058_: u8,
    mut v_a_2059_: *mut LeanObject,
    mut v_b_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2081_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2066_) == 0 {
                    v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
                    v_isSharedCheck_2082_ = (!lean_is_exclusive(v___x_2066_)) as u8;
                    if v_isSharedCheck_2082_ == 0 {
                        v___x_2069_ = v___x_2066_;
                        v_isShared_2070_ = v_isSharedCheck_2082_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2067_);
                        lean_dec(v___x_2066_);
                        v___x_2069_ = lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2082_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2066_;
                }
            }
            1 => {
                v___x_2071_ = (lean_unbox(v_a_2067_) as u8);
                lean_dec(v_a_2067_);
                if v___x_2071_ == 0 {
                    v___x_2072_ = 1;
                    v___x_2073_ = lean_box((v___x_2072_) as usize);
                    if v_isShared_2070_ == 0 {
                        lean_ctor_set(v___x_2069_, 0, v___x_2073_);
                        v___x_2075_ = v___x_2069_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
                        v___x_2075_ = v_reuseFailAlloc_2076_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2077_ = 0;
                    v___x_2078_ = lean_box((v___x_2077_) as usize);
                    if v_isShared_2070_ == 0 {
                        lean_ctor_set(v___x_2069_, 0, v___x_2078_);
                        v___x_2080_ = v___x_2069_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
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
    mut v_mode_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_b_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2091_: u8 = 0;
    let mut v_res_2092_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2091_ = (lean_unbox(v_mode_2083_) as u8);
    v_res_2092_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(
        v_mode_boxed_2091_,
        v_a_2084_,
        v_b_2085_,
        v_a_2086_,
        v_a_2087_,
        v_a_2088_,
        v_a_2089_,
    );
    lean_dec(v_a_2089_);
    lean_dec_ref(v_a_2088_);
    lean_dec(v_a_2087_);
    lean_dec_ref(v_a_2086_);
    return v_res_2092_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(
    mut v_mode_2093_: *mut LeanObject,
    mut v_a_u2081_2094_: *mut LeanObject,
    mut v_a_u2082_2095_: *mut LeanObject,
    mut v_b_u2081_2096_: *mut LeanObject,
    mut v_b_u2082_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
    mut v_a_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2103_: u8 = 0;
    let mut v_res_2104_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2103_ = (lean_unbox(v_mode_2093_) as u8);
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
    lean_dec(v_a_2101_);
    lean_dec_ref(v_a_2100_);
    lean_dec(v_a_2099_);
    lean_dec_ref(v_a_2098_);
    return v_res_2104_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(
    mut v_upperBound_2105_: *mut LeanObject,
    mut v_args_2106_: *mut LeanObject,
    mut v_mode_2107_: *mut LeanObject,
    mut v_b_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_b_2110_: *mut LeanObject,
    mut v___y_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
    mut v___y_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2116_: u8 = 0;
    let mut v_res_2117_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2116_ = (lean_unbox(v_mode_2107_) as u8);
    v_res_2117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_2105_, v_args_2106_, v_mode_boxed_2116_, v_b_2108_, v_a_2109_, v_b_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
    lean_dec(v___y_2114_);
    lean_dec_ref(v___y_2113_);
    lean_dec(v___y_2112_);
    lean_dec_ref(v___y_2111_);
    lean_dec_ref(v_args_2106_);
    lean_dec(v_upperBound_2105_);
    return v_res_2117_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(
    mut v_mode_2118_: *mut LeanObject,
    mut v_a_2119_: *mut LeanObject,
    mut v_b_2120_: *mut LeanObject,
    mut v_a_2121_: *mut LeanObject,
    mut v_a_2122_: *mut LeanObject,
    mut v_a_2123_: *mut LeanObject,
    mut v_a_2124_: *mut LeanObject,
    mut v_a_2125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2126_: u8 = 0;
    let mut v_res_2127_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2126_ = (lean_unbox(v_mode_2118_) as u8);
    v_res_2127_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(
        v_mode_boxed_2126_,
        v_a_2119_,
        v_b_2120_,
        v_a_2121_,
        v_a_2122_,
        v_a_2123_,
        v_a_2124_,
    );
    lean_dec(v_a_2124_);
    lean_dec_ref(v_a_2123_);
    lean_dec(v_a_2122_);
    lean_dec_ref(v_a_2121_);
    return v_res_2127_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(
    mut v_upperBound_2128_: *mut LeanObject,
    mut v_a_2129_: *mut LeanObject,
    mut v_args_2130_: *mut LeanObject,
    mut v_mode_2131_: *mut LeanObject,
    mut v_b_2132_: *mut LeanObject,
    mut v_a_2133_: *mut LeanObject,
    mut v_b_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2140_: u8 = 0;
    let mut v_res_2141_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2140_ = (lean_unbox(v_mode_2131_) as u8);
    v_res_2141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_2128_, v_a_2129_, v_args_2130_, v_mode_boxed_2140_, v_b_2132_, v_a_2133_, v_b_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
    lean_dec(v___y_2138_);
    lean_dec_ref(v___y_2137_);
    lean_dec(v___y_2136_);
    lean_dec_ref(v___y_2135_);
    lean_dec_ref(v_args_2130_);
    lean_dec_ref(v_a_2129_);
    lean_dec(v_upperBound_2128_);
    return v_res_2141_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(
    mut v_mode_2142_: *mut LeanObject,
    mut v_a_2143_: *mut LeanObject,
    mut v_b_2144_: *mut LeanObject,
    mut v_a_2145_: *mut LeanObject,
    mut v_a_2146_: *mut LeanObject,
    mut v_a_2147_: *mut LeanObject,
    mut v_a_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2150_: u8 = 0;
    let mut v_res_2151_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2150_ = (lean_unbox(v_mode_2142_) as u8);
    v_res_2151_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(
        v_mode_boxed_2150_,
        v_a_2143_,
        v_b_2144_,
        v_a_2145_,
        v_a_2146_,
        v_a_2147_,
        v_a_2148_,
    );
    lean_dec(v_a_2148_);
    lean_dec_ref(v_a_2147_);
    lean_dec(v_a_2146_);
    lean_dec_ref(v_a_2145_);
    return v_res_2151_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(
    mut v_mode_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_b_2154_: *mut LeanObject,
    mut v_a_2155_: *mut LeanObject,
    mut v_a_2156_: *mut LeanObject,
    mut v_a_2157_: *mut LeanObject,
    mut v_a_2158_: *mut LeanObject,
    mut v_a_2159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2160_: u8 = 0;
    let mut v_res_2161_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2160_ = (lean_unbox(v_mode_2152_) as u8);
    v_res_2161_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(
        v_mode_boxed_2160_,
        v_a_2153_,
        v_b_2154_,
        v_a_2155_,
        v_a_2156_,
        v_a_2157_,
        v_a_2158_,
    );
    lean_dec(v_a_2158_);
    lean_dec_ref(v_a_2157_);
    lean_dec(v_a_2156_);
    lean_dec_ref(v_a_2155_);
    return v_res_2161_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(
    mut v_upperBound_2162_: *mut LeanObject,
    mut v___x_2163_: *mut LeanObject,
    mut v___x_2164_: *mut LeanObject,
    mut v_mode_2165_: *mut LeanObject,
    mut v_a_2166_: *mut LeanObject,
    mut v_b_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
    mut v___y_2169_: *mut LeanObject,
    mut v___y_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2173_: u8 = 0;
    let mut v_res_2174_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2173_ = (lean_unbox(v_mode_2165_) as u8);
    v_res_2174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_2162_, v___x_2163_, v___x_2164_, v_mode_boxed_2173_, v_a_2166_, v_b_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
    lean_dec(v___y_2171_);
    lean_dec_ref(v___y_2170_);
    lean_dec(v___y_2169_);
    lean_dec_ref(v___y_2168_);
    lean_dec_ref(v___x_2164_);
    lean_dec_ref(v___x_2163_);
    lean_dec(v_upperBound_2162_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(
    mut v_mode_2175_: *mut LeanObject,
    mut v_b_2176_: *mut LeanObject,
    mut v_x_2177_: *mut LeanObject,
    mut v_x_2178_: *mut LeanObject,
    mut v_x_2179_: *mut LeanObject,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
    mut v___y_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
    mut v___y_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2185_: u8 = 0;
    let mut v_res_2186_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2185_ = (lean_unbox(v_mode_2175_) as u8);
    v_res_2186_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_2185_, v_b_2176_, v_x_2177_, v_x_2178_, v_x_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
    lean_dec(v___y_2183_);
    lean_dec_ref(v___y_2182_);
    lean_dec(v___y_2181_);
    lean_dec_ref(v___y_2180_);
    return v_res_2186_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(
    mut v_upperBound_2187_: *mut LeanObject,
    mut v_a_2188_: *mut LeanObject,
    mut v___x_2189_: *mut LeanObject,
    mut v___x_2190_: *mut LeanObject,
    mut v_mode_2191_: *mut LeanObject,
    mut v_a_2192_: *mut LeanObject,
    mut v_b_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2199_: u8 = 0;
    let mut v_res_2200_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2199_ = (lean_unbox(v_mode_2191_) as u8);
    v_res_2200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_2187_, v_a_2188_, v___x_2189_, v___x_2190_, v_mode_boxed_2199_, v_a_2192_, v_b_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
    lean_dec(v___y_2197_);
    lean_dec_ref(v___y_2196_);
    lean_dec(v___y_2195_);
    lean_dec_ref(v___y_2194_);
    lean_dec_ref(v___x_2190_);
    lean_dec_ref(v___x_2189_);
    lean_dec_ref(v_a_2188_);
    lean_dec(v_upperBound_2187_);
    return v_res_2200_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(
    mut v_mode_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_b_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2209_: u8 = 0;
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2209_ = (lean_unbox(v_mode_2201_) as u8);
    v_res_2210_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(
        v_mode_boxed_2209_,
        v_a_2202_,
        v_b_2203_,
        v_a_2204_,
        v_a_2205_,
        v_a_2206_,
        v_a_2207_,
    );
    lean_dec(v_a_2207_);
    lean_dec_ref(v_a_2206_);
    lean_dec(v_a_2205_);
    lean_dec_ref(v_a_2204_);
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(
    mut v_mode_2211_: *mut LeanObject,
    mut v_a_2212_: *mut LeanObject,
    mut v_b_2213_: *mut LeanObject,
    mut v_a_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
    mut v_a_2216_: *mut LeanObject,
    mut v_a_2217_: *mut LeanObject,
    mut v_a_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2219_: u8 = 0;
    let mut v_res_2220_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2219_ = (lean_unbox(v_mode_2211_) as u8);
    v_res_2220_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(
        v_mode_boxed_2219_,
        v_a_2212_,
        v_b_2213_,
        v_a_2214_,
        v_a_2215_,
        v_a_2216_,
        v_a_2217_,
    );
    lean_dec(v_a_2217_);
    lean_dec_ref(v_a_2216_);
    lean_dec(v_a_2215_);
    lean_dec_ref(v_a_2214_);
    return v_res_2220_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(
    mut v_upperBound_2221_: *mut LeanObject,
    mut v___x_2222_: *mut LeanObject,
    mut v___x_2223_: *mut LeanObject,
    mut v_mode_2224_: u8,
    mut v_inst_2225_: *mut LeanObject,
    mut v_R_2226_: *mut LeanObject,
    mut v_a_2227_: *mut LeanObject,
    mut v_b_2228_: *mut LeanObject,
    mut v_c_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
    mut v___y_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
    mut v___y_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    v___x_2235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_2221_, v___x_2222_, v___x_2223_, v_mode_2224_, v_a_2227_, v_b_2228_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
    return v___x_2235_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(
    mut v_upperBound_2236_: *mut LeanObject,
    mut v___x_2237_: *mut LeanObject,
    mut v___x_2238_: *mut LeanObject,
    mut v_mode_2239_: *mut LeanObject,
    mut v_inst_2240_: *mut LeanObject,
    mut v_R_2241_: *mut LeanObject,
    mut v_a_2242_: *mut LeanObject,
    mut v_b_2243_: *mut LeanObject,
    mut v_c_2244_: *mut LeanObject,
    mut v___y_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2250_: u8 = 0;
    let mut v_res_2251_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2250_ = (lean_unbox(v_mode_2239_) as u8);
    v_res_2251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_2236_, v___x_2237_, v___x_2238_, v_mode_boxed_2250_, v_inst_2240_, v_R_2241_, v_a_2242_, v_b_2243_, v_c_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
    lean_dec(v___y_2248_);
    lean_dec_ref(v___y_2247_);
    lean_dec(v___y_2246_);
    lean_dec_ref(v___y_2245_);
    lean_dec_ref(v___x_2238_);
    lean_dec_ref(v___x_2237_);
    lean_dec(v_upperBound_2236_);
    return v_res_2251_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(
    mut v_upperBound_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
    mut v___x_2254_: *mut LeanObject,
    mut v___x_2255_: *mut LeanObject,
    mut v_mode_2256_: u8,
    mut v_inst_2257_: *mut LeanObject,
    mut v_R_2258_: *mut LeanObject,
    mut v_a_2259_: *mut LeanObject,
    mut v_b_2260_: *mut LeanObject,
    mut v_c_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    v___x_2267_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_2252_, v_a_2253_, v___x_2254_, v___x_2255_, v_mode_2256_, v_a_2259_, v_b_2260_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
    return v___x_2267_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(
    mut v_upperBound_2268_: *mut LeanObject,
    mut v_a_2269_: *mut LeanObject,
    mut v___x_2270_: *mut LeanObject,
    mut v___x_2271_: *mut LeanObject,
    mut v_mode_2272_: *mut LeanObject,
    mut v_inst_2273_: *mut LeanObject,
    mut v_R_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
    mut v_b_2276_: *mut LeanObject,
    mut v_c_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2283_: u8 = 0;
    let mut v_res_2284_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2283_ = (lean_unbox(v_mode_2272_) as u8);
    v_res_2284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_2268_, v_a_2269_, v___x_2270_, v___x_2271_, v_mode_boxed_2283_, v_inst_2273_, v_R_2274_, v_a_2275_, v_b_2276_, v_c_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
    lean_dec(v___y_2281_);
    lean_dec_ref(v___y_2280_);
    lean_dec(v___y_2279_);
    lean_dec_ref(v___y_2278_);
    lean_dec_ref(v___x_2271_);
    lean_dec_ref(v___x_2270_);
    lean_dec_ref(v_a_2269_);
    lean_dec(v_upperBound_2268_);
    return v_res_2284_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(
    mut v_upperBound_2285_: *mut LeanObject,
    mut v_args_2286_: *mut LeanObject,
    mut v_mode_2287_: u8,
    mut v_b_2288_: *mut LeanObject,
    mut v_inst_2289_: *mut LeanObject,
    mut v_R_2290_: *mut LeanObject,
    mut v_a_2291_: *mut LeanObject,
    mut v_b_2292_: *mut LeanObject,
    mut v_c_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
    mut v___y_2296_: *mut LeanObject,
    mut v___y_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_2285_, v_args_2286_, v_mode_2287_, v_b_2288_, v_a_2291_, v_b_2292_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
    return v___x_2299_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(
    mut v_upperBound_2300_: *mut LeanObject,
    mut v_args_2301_: *mut LeanObject,
    mut v_mode_2302_: *mut LeanObject,
    mut v_b_2303_: *mut LeanObject,
    mut v_inst_2304_: *mut LeanObject,
    mut v_R_2305_: *mut LeanObject,
    mut v_a_2306_: *mut LeanObject,
    mut v_b_2307_: *mut LeanObject,
    mut v_c_2308_: *mut LeanObject,
    mut v___y_2309_: *mut LeanObject,
    mut v___y_2310_: *mut LeanObject,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2314_: u8 = 0;
    let mut v_res_2315_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2314_ = (lean_unbox(v_mode_2302_) as u8);
    v_res_2315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_2300_, v_args_2301_, v_mode_boxed_2314_, v_b_2303_, v_inst_2304_, v_R_2305_, v_a_2306_, v_b_2307_, v_c_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    lean_dec(v___y_2312_);
    lean_dec_ref(v___y_2311_);
    lean_dec(v___y_2310_);
    lean_dec_ref(v___y_2309_);
    lean_dec_ref(v_args_2301_);
    lean_dec(v_upperBound_2300_);
    return v_res_2315_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(
    mut v_upperBound_2316_: *mut LeanObject,
    mut v_a_2317_: *mut LeanObject,
    mut v_args_2318_: *mut LeanObject,
    mut v_mode_2319_: u8,
    mut v_b_2320_: *mut LeanObject,
    mut v_inst_2321_: *mut LeanObject,
    mut v_R_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
    mut v_b_2324_: *mut LeanObject,
    mut v_c_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    v___x_2331_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_2316_, v_a_2317_, v_args_2318_, v_mode_2319_, v_b_2320_, v_a_2323_, v_b_2324_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
    return v___x_2331_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(
    mut v_upperBound_2332_: *mut LeanObject,
    mut v_a_2333_: *mut LeanObject,
    mut v_args_2334_: *mut LeanObject,
    mut v_mode_2335_: *mut LeanObject,
    mut v_b_2336_: *mut LeanObject,
    mut v_inst_2337_: *mut LeanObject,
    mut v_R_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
    mut v_b_2340_: *mut LeanObject,
    mut v_c_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2347_: u8 = 0;
    let mut v_res_2348_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2347_ = (lean_unbox(v_mode_2335_) as u8);
    v_res_2348_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_2332_, v_a_2333_, v_args_2334_, v_mode_boxed_2347_, v_b_2336_, v_inst_2337_, v_R_2338_, v_a_2339_, v_b_2340_, v_c_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
    lean_dec(v___y_2345_);
    lean_dec_ref(v___y_2344_);
    lean_dec(v___y_2343_);
    lean_dec_ref(v___y_2342_);
    lean_dec_ref(v_args_2334_);
    lean_dec_ref(v_a_2333_);
    lean_dec(v_upperBound_2332_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_Meta_ACLt_main(
    mut v_a_2349_: *mut LeanObject,
    mut v_b_2350_: *mut LeanObject,
    mut v_mode_2351_: u8,
    mut v_a_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2358_: *mut LeanObject,
    mut v_b_2359_: *mut LeanObject,
    mut v_mode_2360_: *mut LeanObject,
    mut v_a_2361_: *mut LeanObject,
    mut v_a_2362_: *mut LeanObject,
    mut v_a_2363_: *mut LeanObject,
    mut v_a_2364_: *mut LeanObject,
    mut v_a_2365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2366_: u8 = 0;
    let mut v_res_2367_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2366_ = (lean_unbox(v_mode_2360_) as u8);
    v_res_2367_ = l_Lean_Meta_ACLt_main(
        v_a_2358_,
        v_b_2359_,
        v_mode_boxed_2366_,
        v_a_2361_,
        v_a_2362_,
        v_a_2363_,
        v_a_2364_,
    );
    lean_dec(v_a_2364_);
    lean_dec_ref(v_a_2363_);
    lean_dec(v_a_2362_);
    lean_dec_ref(v_a_2361_);
    return v_res_2367_;
}
pub unsafe fn l_Lean_Meta_acLt(
    mut v_a_2368_: *mut LeanObject,
    mut v_b_2369_: *mut LeanObject,
    mut v_mode_2370_: u8,
    mut v_a_2371_: *mut LeanObject,
    mut v_a_2372_: *mut LeanObject,
    mut v_a_2373_: *mut LeanObject,
    mut v_a_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2377_: *mut LeanObject,
    mut v_b_2378_: *mut LeanObject,
    mut v_mode_2379_: *mut LeanObject,
    mut v_a_2380_: *mut LeanObject,
    mut v_a_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
    mut v_a_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mode_boxed_2385_: u8 = 0;
    let mut v_res_2386_: *mut LeanObject = core::ptr::null_mut();
    v_mode_boxed_2385_ = (lean_unbox(v_mode_2379_) as u8);
    v_res_2386_ = l_Lean_Meta_acLt(
        v_a_2377_,
        v_b_2378_,
        v_mode_boxed_2385_,
        v_a_2380_,
        v_a_2381_,
        v_a_2382_,
        v_a_2383_,
    );
    lean_dec(v_a_2383_);
    lean_dec_ref(v_a_2382_);
    lean_dec(v_a_2381_);
    lean_dec_ref(v_a_2380_);
    return v_res_2386_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ACLt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_DiscrTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config =
        _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config();
    lean_mark_persistent(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ACLt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ACLt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_DiscrTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ACLt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ACLt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_ACLt(builtin);
}
