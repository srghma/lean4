// Lean compiler output
// Module: Lean.Meta.Sym.Intro
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Sym.InstantiateS Lean.Meta.Sym.IsClass Lean.Meta.Sym.AlphaShareBuilder
use crate::r#gen::Init::Prelude::l_Lean_Name_num___override;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_fvar___override, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_letE___override, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkBVar, l_Lean_mkLambda,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_mkLetDecl, l_Lean_LocalContext_mkLocalDecl,
};
use crate::r#gen::Lean::Meta::Basic::{l_Lean_MVarId_getDecl, l_Lean_Meta_mkFreshExprMVarAt};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateS::{
    initialize_Lean_Meta_Sym_InstantiateS, l_Lean_Meta_Sym_instantiateRevRangeS,
    runtime_initialize_Lean_Meta_Sym_InstantiateS,
};
use crate::r#gen::Lean::Meta::Sym::IsClass::{
    initialize_Lean_Meta_Sym_IsClass, l_Lean_Meta_Sym_isClass_x3f,
    runtime_initialize_Lean_Meta_Sym_IsClass,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_7, lean_apply_11, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0_value:
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
static mut l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1_value:
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
static mut l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1_value
)
    as *mut LeanObject;
pub static mut l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(
    mut v_max_997_: *mut LeanObject,
    mut v_i_998_: *mut LeanObject,
    mut v_type_999_: *mut LeanObject,
    mut v_body_1000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1001_: u8 = 0;
    let mut v_expr_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1007_: u8 = 0;
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1016_: u8 = 0;
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1001_ = lean_nat_dec_le(v_max_997_, v_i_998_);
                if v___x_1001_ == 0 {
                    match lean_obj_tag(v_type_999_) {
                        10 => {
                            v_expr_1002_ = lean_ctor_get(v_type_999_, 1);
                            lean_inc_ref(v_expr_1002_);
                            lean_dec_ref_known(v_type_999_, 2);
                            v_type_999_ = v_expr_1002_;
                            state = 0;
                            continue;
                        }
                        7 => {
                            v_binderName_1004_ = lean_ctor_get(v_type_999_, 0);
                            lean_inc(v_binderName_1004_);
                            v_binderType_1005_ = lean_ctor_get(v_type_999_, 1);
                            lean_inc_ref(v_binderType_1005_);
                            v_body_1006_ = lean_ctor_get(v_type_999_, 2);
                            lean_inc_ref(v_body_1006_);
                            v_binderInfo_1007_ = lean_ctor_get_uint8(
                                v_type_999_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_dec_ref_known(v_type_999_, 3);
                            v___x_1008_ = lean_unsigned_to_nat(1);
                            v___x_1009_ = lean_nat_add(v_i_998_, v___x_1008_);
                            v___x_1010_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_997_, v___x_1009_, v_body_1006_, v_body_1000_);
                            lean_dec(v___x_1009_);
                            v___x_1011_ = l_Lean_mkLambda(
                                v_binderName_1004_,
                                v_binderInfo_1007_,
                                v_binderType_1005_,
                                v___x_1010_,
                            );
                            return v___x_1011_;
                        }
                        8 => {
                            v_declName_1012_ = lean_ctor_get(v_type_999_, 0);
                            lean_inc(v_declName_1012_);
                            v_type_1013_ = lean_ctor_get(v_type_999_, 1);
                            lean_inc_ref(v_type_1013_);
                            v_value_1014_ = lean_ctor_get(v_type_999_, 2);
                            lean_inc_ref(v_value_1014_);
                            v_body_1015_ = lean_ctor_get(v_type_999_, 3);
                            lean_inc_ref(v_body_1015_);
                            v_nondep_1016_ = lean_ctor_get_uint8(
                                v_type_999_,
                                (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                            );
                            lean_dec_ref_known(v_type_999_, 4);
                            v___x_1017_ = lean_unsigned_to_nat(1);
                            v___x_1018_ = lean_nat_add(v_i_998_, v___x_1017_);
                            v___x_1019_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_997_, v___x_1018_, v_body_1015_, v_body_1000_);
                            lean_dec(v___x_1018_);
                            v___x_1020_ = l_Lean_Expr_letE___override(
                                v_declName_1012_,
                                v_type_1013_,
                                v_value_1014_,
                                v___x_1019_,
                                v_nondep_1016_,
                            );
                            return v___x_1020_;
                        }
                        _ => {
                            lean_dec_ref(v_type_999_);
                            lean_inc_ref(v_body_1000_);
                            return v_body_1000_;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_999_);
                    lean_inc_ref(v_body_1000_);
                    return v_body_1000_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop___boxed(
    mut v_max_1021_: *mut LeanObject,
    mut v_i_1022_: *mut LeanObject,
    mut v_type_1023_: *mut LeanObject,
    mut v_body_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1025_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(
        v_max_1021_,
        v_i_1022_,
        v_type_1023_,
        v_body_1024_,
    );
    lean_dec_ref(v_body_1024_);
    lean_dec(v_i_1022_);
    lean_dec(v_max_1021_);
    return v_res_1025_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(
    mut v_e_1026_: *mut LeanObject,
    mut v_n_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1029_: u8 = 0;
    let mut v_one_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1028_ = lean_unsigned_to_nat(0);
                v_isZero_1029_ = lean_nat_dec_eq(v_n_1027_, v_zero_1028_);
                if v_isZero_1029_ == 1 {
                    lean_dec(v_n_1027_);
                    return v_e_1026_;
                } else {
                    v_one_1030_ = lean_unsigned_to_nat(1);
                    v_n_1031_ = lean_nat_sub(v_n_1027_, v_one_1030_);
                    lean_dec(v_n_1027_);
                    lean_inc(v_n_1031_);
                    v___x_1032_ = l_Lean_mkBVar(v_n_1031_);
                    v___x_1033_ = l_Lean_Expr_app___override(v_e_1026_, v___x_1032_);
                    v_e_1026_ = v___x_1033_;
                    v_n_1027_ = v_n_1031_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(
    mut v_fvarId_1035_: *mut LeanObject,
    mut v___y_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    v___x_1038_ = l_Lean_Expr_fvar___override(v_fvarId_1035_);
    v___x_1039_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1038_, v___y_1036_);
    return v___x_1039_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg___boxed(
    mut v_fvarId_1040_: *mut LeanObject,
    mut v___y_1041_: *mut LeanObject,
    mut v___y_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1043_: *mut LeanObject = core::ptr::null_mut();
    v_res_1043_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_fvarId_1040_, v___y_1041_);
    lean_dec(v___y_1041_);
    return v_res_1043_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(
    mut v_fvarId_1044_: *mut LeanObject,
    mut v___y_1045_: *mut LeanObject,
    mut v___y_1046_: *mut LeanObject,
    mut v___y_1047_: *mut LeanObject,
    mut v___y_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
    mut v___y_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1052_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_fvarId_1044_, v___y_1046_);
    return v___x_1052_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___boxed(
    mut v_fvarId_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
    mut v___y_1055_: *mut LeanObject,
    mut v___y_1056_: *mut LeanObject,
    mut v___y_1057_: *mut LeanObject,
    mut v___y_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1061_: *mut LeanObject = core::ptr::null_mut();
    v_res_1061_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1(v_fvarId_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
    lean_dec(v___y_1059_);
    lean_dec_ref(v___y_1058_);
    lean_dec(v___y_1057_);
    lean_dec_ref(v___y_1056_);
    lean_dec(v___y_1055_);
    lean_dec_ref(v___y_1054_);
    return v_res_1061_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(
    mut v___y_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1070_: u8 = 0;
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1082_: u8 = 0;
    let mut v_r_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut v_unused_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1064_ = lean_st_ref_get(v___y_1062_);
                v_ngen_1065_ = lean_ctor_get(v___x_1064_, 2);
                lean_inc_ref(v_ngen_1065_);
                lean_dec(v___x_1064_);
                v_namePrefix_1066_ = lean_ctor_get(v_ngen_1065_, 0);
                v_idx_1067_ = lean_ctor_get(v_ngen_1065_, 1);
                v_isSharedCheck_1096_ = (!lean_is_exclusive(v_ngen_1065_)) as u8;
                if v_isSharedCheck_1096_ == 0 {
                    v___x_1069_ = v_ngen_1065_;
                    v_isShared_1070_ = v_isSharedCheck_1096_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1067_);
                    lean_inc(v_namePrefix_1066_);
                    lean_dec(v_ngen_1065_);
                    v___x_1069_ = lean_box(0);
                    v_isShared_1070_ = v_isSharedCheck_1096_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1071_ = lean_st_ref_take(v___y_1062_);
                v_env_1072_ = lean_ctor_get(v___x_1071_, 0);
                v_nextMacroScope_1073_ = lean_ctor_get(v___x_1071_, 1);
                v_auxDeclNGen_1074_ = lean_ctor_get(v___x_1071_, 3);
                v_traceState_1075_ = lean_ctor_get(v___x_1071_, 4);
                v_cache_1076_ = lean_ctor_get(v___x_1071_, 5);
                v_messages_1077_ = lean_ctor_get(v___x_1071_, 6);
                v_infoState_1078_ = lean_ctor_get(v___x_1071_, 7);
                v_snapshotTasks_1079_ = lean_ctor_get(v___x_1071_, 8);
                v_isSharedCheck_1094_ = (!lean_is_exclusive(v___x_1071_)) as u8;
                if v_isSharedCheck_1094_ == 0 {
                    v_unused_1095_ = lean_ctor_get(v___x_1071_, 2);
                    lean_dec(v_unused_1095_);
                    v___x_1081_ = v___x_1071_;
                    v_isShared_1082_ = v_isSharedCheck_1094_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1079_);
                    lean_inc(v_infoState_1078_);
                    lean_inc(v_messages_1077_);
                    lean_inc(v_cache_1076_);
                    lean_inc(v_traceState_1075_);
                    lean_inc(v_auxDeclNGen_1074_);
                    lean_inc(v_nextMacroScope_1073_);
                    lean_inc(v_env_1072_);
                    lean_dec(v___x_1071_);
                    v___x_1081_ = lean_box(0);
                    v_isShared_1082_ = v_isSharedCheck_1094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_1067_);
                lean_inc(v_namePrefix_1066_);
                v_r_1083_ = l_Lean_Name_num___override(v_namePrefix_1066_, v_idx_1067_);
                v___x_1084_ = lean_unsigned_to_nat(1);
                v___x_1085_ = lean_nat_add(v_idx_1067_, v___x_1084_);
                lean_dec(v_idx_1067_);
                if v_isShared_1070_ == 0 {
                    lean_ctor_set(v___x_1069_, 1, v___x_1085_);
                    v___x_1087_ = v___x_1069_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_namePrefix_1066_);
                    lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1085_);
                    v___x_1087_ = v_reuseFailAlloc_1093_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1082_ == 0 {
                    lean_ctor_set(v___x_1081_, 2, v___x_1087_);
                    v___x_1089_ = v___x_1081_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_env_1072_);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_nextMacroScope_1073_);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 2, v___x_1087_);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_auxDeclNGen_1074_);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_traceState_1075_);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 5, v_cache_1076_);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 6, v_messages_1077_);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 7, v_infoState_1078_);
                    lean_ctor_set(v_reuseFailAlloc_1092_, 8, v_snapshotTasks_1079_);
                    v___x_1089_ = v_reuseFailAlloc_1092_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1090_ = lean_st_ref_set(v___y_1062_, v___x_1089_);
                v___x_1091_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1091_, 0, v_r_1083_);
                return v___x_1091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg___boxed(
    mut v___y_1097_: *mut LeanObject,
    mut v___y_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1099_: *mut LeanObject = core::ptr::null_mut();
    v_res_1099_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_1097_);
    lean_dec(v___y_1097_);
    return v_res_1099_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(
    mut v___y_1100_: *mut LeanObject,
    mut v___y_1101_: *mut LeanObject,
    mut v___y_1102_: *mut LeanObject,
    mut v___y_1103_: *mut LeanObject,
    mut v___y_1104_: *mut LeanObject,
    mut v___y_1105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1111_: u8 = 0;
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1107_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_1105_);
                v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
                v_isSharedCheck_1115_ = (!lean_is_exclusive(v___x_1107_)) as u8;
                if v_isSharedCheck_1115_ == 0 {
                    v___x_1110_ = v___x_1107_;
                    v_isShared_1111_ = v_isSharedCheck_1115_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1108_);
                    lean_dec(v___x_1107_);
                    v___x_1110_ = lean_box(0);
                    v_isShared_1111_ = v_isSharedCheck_1115_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1111_ == 0 {
                    v___x_1113_ = v___x_1110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
                    v___x_1113_ = v_reuseFailAlloc_1114_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0___boxed(
    mut v___y_1116_: *mut LeanObject,
    mut v___y_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
    mut v___y_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1123_: *mut LeanObject = core::ptr::null_mut();
    v_res_1123_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
    lean_dec(v___y_1121_);
    lean_dec_ref(v___y_1120_);
    lean_dec(v___y_1119_);
    lean_dec_ref(v___y_1118_);
    lean_dec(v___y_1117_);
    lean_dec_ref(v___y_1116_);
    return v_res_1123_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(
    mut v_max_1124_: *mut LeanObject,
    mut v_finalize_1125_: *mut LeanObject,
    mut v_mkName_1126_: *mut LeanObject,
    mut v_updateLocalInsts_1127_: *mut LeanObject,
    mut v_i_1128_: *mut LeanObject,
    mut v_lctx_1129_: *mut LeanObject,
    mut v_localInsts_1130_: *mut LeanObject,
    mut v_fvars_1131_: *mut LeanObject,
    mut v_type_1132_: *mut LeanObject,
    mut v_a_1133_: *mut LeanObject,
    mut v_a_1134_: *mut LeanObject,
    mut v_a_1135_: *mut LeanObject,
    mut v_a_1136_: *mut LeanObject,
    mut v_a_1137_: *mut LeanObject,
    mut v_a_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1140_: u8 = 0;
    let mut v_expr_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1146_: u8 = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: u8 = 0;
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1167_: u8 = 0;
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut v_a_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1175_: u8 = 0;
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_a_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1183_: u8 = 0;
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut v_a_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1195_: u8 = 0;
    let mut v_declName_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v_a_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1234_: u8 = 0;
    let mut v_a_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1238_: u8 = 0;
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1242_: u8 = 0;
    let mut v_a_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1250_: u8 = 0;
    let mut v_a_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1254_: u8 = 0;
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1258_: u8 = 0;
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1140_ = lean_nat_dec_le(v_max_1124_, v_i_1128_);
                if v___x_1140_ == 0 {
                    match lean_obj_tag(v_type_1132_) {
                        10 => {
                            v_expr_1141_ = lean_ctor_get(v_type_1132_, 1);
                            lean_inc_ref(v_expr_1141_);
                            lean_dec_ref_known(v_type_1132_, 2);
                            v_type_1132_ = v_expr_1141_;
                            state = 0;
                            continue;
                        }
                        7 => {
                            v_binderName_1143_ = lean_ctor_get(v_type_1132_, 0);
                            lean_inc(v_binderName_1143_);
                            v_binderType_1144_ = lean_ctor_get(v_type_1132_, 1);
                            lean_inc_ref(v_binderType_1144_);
                            v_body_1145_ = lean_ctor_get(v_type_1132_, 2);
                            lean_inc_ref(v_body_1145_);
                            v_binderInfo_1146_ = lean_ctor_get_uint8(
                                v_type_1132_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_dec_ref_known(v_type_1132_, 3);
                            v___x_1147_ = lean_unsigned_to_nat(0);
                            v___x_1148_ = lean_array_get_size(v_fvars_1131_);
                            v___x_1149_ = l_Lean_Meta_Sym_instantiateRevRangeS(
                                v_binderType_1144_,
                                v___x_1147_,
                                v___x_1148_,
                                v_fvars_1131_,
                                v_a_1133_,
                                v_a_1134_,
                                v_a_1135_,
                                v_a_1136_,
                                v_a_1137_,
                                v_a_1138_,
                            );
                            if lean_obj_tag(v___x_1149_) == 0 {
                                v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
                                lean_inc(v_a_1150_);
                                lean_dec_ref_known(v___x_1149_, 1);
                                v___x_1151_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                                if lean_obj_tag(v___x_1151_) == 0 {
                                    v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
                                    lean_inc(v_a_1152_);
                                    lean_dec_ref_known(v___x_1151_, 1);
                                    lean_inc_ref(v_mkName_1126_);
                                    lean_inc(v_a_1138_);
                                    lean_inc_ref(v_a_1137_);
                                    lean_inc(v_a_1136_);
                                    lean_inc_ref(v_a_1135_);
                                    lean_inc(v_i_1128_);
                                    v___x_1153_ = lean_apply_7(
                                        v_mkName_1126_,
                                        v_binderName_1143_,
                                        v_i_1128_,
                                        v_a_1135_,
                                        v_a_1136_,
                                        v_a_1137_,
                                        v_a_1138_,
                                        lean_box(0),
                                    );
                                    if lean_obj_tag(v___x_1153_) == 0 {
                                        v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
                                        lean_inc(v_a_1154_);
                                        lean_dec_ref_known(v___x_1153_, 1);
                                        v___x_1155_ = 0;
                                        lean_inc(v_a_1150_);
                                        lean_inc(v_a_1152_);
                                        v___x_1156_ = l_Lean_LocalContext_mkLocalDecl(
                                            v_lctx_1129_,
                                            v_a_1152_,
                                            v_a_1154_,
                                            v_a_1150_,
                                            v_binderInfo_1146_,
                                            v___x_1155_,
                                        );
                                        v___x_1157_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_a_1152_, v_a_1134_);
                                        if lean_obj_tag(v___x_1157_) == 0 {
                                            v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
                                            lean_inc_n(v_a_1158_, 2);
                                            lean_dec_ref_known(v___x_1157_, 1);
                                            v___x_1159_ = lean_array_push(v_fvars_1131_, v_a_1158_);
                                            lean_inc_ref(v_updateLocalInsts_1127_);
                                            v___x_1160_ = lean_apply_3(
                                                v_updateLocalInsts_1127_,
                                                v_localInsts_1130_,
                                                v_a_1158_,
                                                v_a_1150_,
                                            );
                                            v___x_1161_ = lean_unsigned_to_nat(1);
                                            v___x_1162_ = lean_nat_add(v_i_1128_, v___x_1161_);
                                            lean_dec(v_i_1128_);
                                            v_i_1128_ = v___x_1162_;
                                            v_lctx_1129_ = v___x_1156_;
                                            v_localInsts_1130_ = v___x_1160_;
                                            v_fvars_1131_ = v___x_1159_;
                                            v_type_1132_ = v_body_1145_;
                                            state = 0;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_1156_);
                                            lean_dec(v_a_1150_);
                                            lean_dec_ref(v_body_1145_);
                                            lean_dec_ref(v_fvars_1131_);
                                            lean_dec_ref(v_localInsts_1130_);
                                            lean_dec(v_i_1128_);
                                            lean_dec_ref(v_updateLocalInsts_1127_);
                                            lean_dec_ref(v_mkName_1126_);
                                            lean_dec_ref(v_finalize_1125_);
                                            v_a_1164_ = lean_ctor_get(v___x_1157_, 0);
                                            v_isSharedCheck_1171_ =
                                                (!lean_is_exclusive(v___x_1157_)) as u8;
                                            if v_isSharedCheck_1171_ == 0 {
                                                v___x_1166_ = v___x_1157_;
                                                v_isShared_1167_ = v_isSharedCheck_1171_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1164_);
                                                lean_dec(v___x_1157_);
                                                v___x_1166_ = lean_box(0);
                                                v_isShared_1167_ = v_isSharedCheck_1171_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_1152_);
                                        lean_dec(v_a_1150_);
                                        lean_dec_ref(v_body_1145_);
                                        lean_dec_ref(v_fvars_1131_);
                                        lean_dec_ref(v_localInsts_1130_);
                                        lean_dec_ref(v_lctx_1129_);
                                        lean_dec(v_i_1128_);
                                        lean_dec_ref(v_updateLocalInsts_1127_);
                                        lean_dec_ref(v_mkName_1126_);
                                        lean_dec_ref(v_finalize_1125_);
                                        v_a_1172_ = lean_ctor_get(v___x_1153_, 0);
                                        v_isSharedCheck_1179_ =
                                            (!lean_is_exclusive(v___x_1153_)) as u8;
                                        if v_isSharedCheck_1179_ == 0 {
                                            v___x_1174_ = v___x_1153_;
                                            v_isShared_1175_ = v_isSharedCheck_1179_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1172_);
                                            lean_dec(v___x_1153_);
                                            v___x_1174_ = lean_box(0);
                                            v_isShared_1175_ = v_isSharedCheck_1179_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_1150_);
                                    lean_dec_ref(v_body_1145_);
                                    lean_dec(v_binderName_1143_);
                                    lean_dec_ref(v_fvars_1131_);
                                    lean_dec_ref(v_localInsts_1130_);
                                    lean_dec_ref(v_lctx_1129_);
                                    lean_dec(v_i_1128_);
                                    lean_dec_ref(v_updateLocalInsts_1127_);
                                    lean_dec_ref(v_mkName_1126_);
                                    lean_dec_ref(v_finalize_1125_);
                                    v_a_1180_ = lean_ctor_get(v___x_1151_, 0);
                                    v_isSharedCheck_1187_ = (!lean_is_exclusive(v___x_1151_)) as u8;
                                    if v_isSharedCheck_1187_ == 0 {
                                        v___x_1182_ = v___x_1151_;
                                        v_isShared_1183_ = v_isSharedCheck_1187_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1180_);
                                        lean_dec(v___x_1151_);
                                        v___x_1182_ = lean_box(0);
                                        v_isShared_1183_ = v_isSharedCheck_1187_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_body_1145_);
                                lean_dec(v_binderName_1143_);
                                lean_dec_ref(v_fvars_1131_);
                                lean_dec_ref(v_localInsts_1130_);
                                lean_dec_ref(v_lctx_1129_);
                                lean_dec(v_i_1128_);
                                lean_dec_ref(v_updateLocalInsts_1127_);
                                lean_dec_ref(v_mkName_1126_);
                                lean_dec_ref(v_finalize_1125_);
                                v_a_1188_ = lean_ctor_get(v___x_1149_, 0);
                                v_isSharedCheck_1195_ = (!lean_is_exclusive(v___x_1149_)) as u8;
                                if v_isSharedCheck_1195_ == 0 {
                                    v___x_1190_ = v___x_1149_;
                                    v_isShared_1191_ = v_isSharedCheck_1195_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_1188_);
                                    lean_dec(v___x_1149_);
                                    v___x_1190_ = lean_box(0);
                                    v_isShared_1191_ = v_isSharedCheck_1195_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                        8 => {
                            v_declName_1196_ = lean_ctor_get(v_type_1132_, 0);
                            lean_inc(v_declName_1196_);
                            v_type_1197_ = lean_ctor_get(v_type_1132_, 1);
                            lean_inc_ref(v_type_1197_);
                            v_value_1198_ = lean_ctor_get(v_type_1132_, 2);
                            lean_inc_ref(v_value_1198_);
                            v_body_1199_ = lean_ctor_get(v_type_1132_, 3);
                            lean_inc_ref(v_body_1199_);
                            lean_dec_ref_known(v_type_1132_, 4);
                            v___x_1200_ = lean_unsigned_to_nat(0);
                            v___x_1201_ = lean_array_get_size(v_fvars_1131_);
                            v___x_1202_ = l_Lean_Meta_Sym_instantiateRevRangeS(
                                v_type_1197_,
                                v___x_1200_,
                                v___x_1201_,
                                v_fvars_1131_,
                                v_a_1133_,
                                v_a_1134_,
                                v_a_1135_,
                                v_a_1136_,
                                v_a_1137_,
                                v_a_1138_,
                            );
                            if lean_obj_tag(v___x_1202_) == 0 {
                                v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
                                lean_inc(v_a_1203_);
                                lean_dec_ref_known(v___x_1202_, 1);
                                v___x_1204_ = l_Lean_Meta_Sym_instantiateRevRangeS(
                                    v_value_1198_,
                                    v___x_1200_,
                                    v___x_1201_,
                                    v_fvars_1131_,
                                    v_a_1133_,
                                    v_a_1134_,
                                    v_a_1135_,
                                    v_a_1136_,
                                    v_a_1137_,
                                    v_a_1138_,
                                );
                                if lean_obj_tag(v___x_1204_) == 0 {
                                    v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
                                    lean_inc(v_a_1205_);
                                    lean_dec_ref_known(v___x_1204_, 1);
                                    v___x_1206_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0(v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
                                    if lean_obj_tag(v___x_1206_) == 0 {
                                        v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
                                        lean_inc(v_a_1207_);
                                        lean_dec_ref_known(v___x_1206_, 1);
                                        lean_inc_ref(v_mkName_1126_);
                                        lean_inc(v_a_1138_);
                                        lean_inc_ref(v_a_1137_);
                                        lean_inc(v_a_1136_);
                                        lean_inc_ref(v_a_1135_);
                                        lean_inc(v_i_1128_);
                                        v___x_1208_ = lean_apply_7(
                                            v_mkName_1126_,
                                            v_declName_1196_,
                                            v_i_1128_,
                                            v_a_1135_,
                                            v_a_1136_,
                                            v_a_1137_,
                                            v_a_1138_,
                                            lean_box(0),
                                        );
                                        if lean_obj_tag(v___x_1208_) == 0 {
                                            v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
                                            lean_inc(v_a_1209_);
                                            lean_dec_ref_known(v___x_1208_, 1);
                                            v___x_1210_ = 0;
                                            lean_inc(v_a_1203_);
                                            lean_inc(v_a_1207_);
                                            v___x_1211_ = l_Lean_LocalContext_mkLetDecl(
                                                v_lctx_1129_,
                                                v_a_1207_,
                                                v_a_1209_,
                                                v_a_1203_,
                                                v_a_1205_,
                                                v___x_1140_,
                                                v___x_1210_,
                                            );
                                            v___x_1212_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__1___redArg(v_a_1207_, v_a_1134_);
                                            if lean_obj_tag(v___x_1212_) == 0 {
                                                v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
                                                lean_inc_n(v_a_1213_, 2);
                                                lean_dec_ref_known(v___x_1212_, 1);
                                                v___x_1214_ =
                                                    lean_array_push(v_fvars_1131_, v_a_1213_);
                                                lean_inc_ref(v_updateLocalInsts_1127_);
                                                v___x_1215_ = lean_apply_3(
                                                    v_updateLocalInsts_1127_,
                                                    v_localInsts_1130_,
                                                    v_a_1213_,
                                                    v_a_1203_,
                                                );
                                                v___x_1216_ = lean_unsigned_to_nat(1);
                                                v___x_1217_ = lean_nat_add(v_i_1128_, v___x_1216_);
                                                lean_dec(v_i_1128_);
                                                v_i_1128_ = v___x_1217_;
                                                v_lctx_1129_ = v___x_1211_;
                                                v_localInsts_1130_ = v___x_1215_;
                                                v_fvars_1131_ = v___x_1214_;
                                                v_type_1132_ = v_body_1199_;
                                                state = 0;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_1211_);
                                                lean_dec(v_a_1203_);
                                                lean_dec_ref(v_body_1199_);
                                                lean_dec_ref(v_fvars_1131_);
                                                lean_dec_ref(v_localInsts_1130_);
                                                lean_dec(v_i_1128_);
                                                lean_dec_ref(v_updateLocalInsts_1127_);
                                                lean_dec_ref(v_mkName_1126_);
                                                lean_dec_ref(v_finalize_1125_);
                                                v_a_1219_ = lean_ctor_get(v___x_1212_, 0);
                                                v_isSharedCheck_1226_ =
                                                    (!lean_is_exclusive(v___x_1212_)) as u8;
                                                if v_isSharedCheck_1226_ == 0 {
                                                    v___x_1221_ = v___x_1212_;
                                                    v_isShared_1222_ = v_isSharedCheck_1226_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_1219_);
                                                    lean_dec(v___x_1212_);
                                                    v___x_1221_ = lean_box(0);
                                                    v_isShared_1222_ = v_isSharedCheck_1226_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_1207_);
                                            lean_dec(v_a_1205_);
                                            lean_dec(v_a_1203_);
                                            lean_dec_ref(v_body_1199_);
                                            lean_dec_ref(v_fvars_1131_);
                                            lean_dec_ref(v_localInsts_1130_);
                                            lean_dec_ref(v_lctx_1129_);
                                            lean_dec(v_i_1128_);
                                            lean_dec_ref(v_updateLocalInsts_1127_);
                                            lean_dec_ref(v_mkName_1126_);
                                            lean_dec_ref(v_finalize_1125_);
                                            v_a_1227_ = lean_ctor_get(v___x_1208_, 0);
                                            v_isSharedCheck_1234_ =
                                                (!lean_is_exclusive(v___x_1208_)) as u8;
                                            if v_isSharedCheck_1234_ == 0 {
                                                v___x_1229_ = v___x_1208_;
                                                v_isShared_1230_ = v_isSharedCheck_1234_;
                                                state = 11;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1227_);
                                                lean_dec(v___x_1208_);
                                                v___x_1229_ = lean_box(0);
                                                v_isShared_1230_ = v_isSharedCheck_1234_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_1205_);
                                        lean_dec(v_a_1203_);
                                        lean_dec_ref(v_body_1199_);
                                        lean_dec(v_declName_1196_);
                                        lean_dec_ref(v_fvars_1131_);
                                        lean_dec_ref(v_localInsts_1130_);
                                        lean_dec_ref(v_lctx_1129_);
                                        lean_dec(v_i_1128_);
                                        lean_dec_ref(v_updateLocalInsts_1127_);
                                        lean_dec_ref(v_mkName_1126_);
                                        lean_dec_ref(v_finalize_1125_);
                                        v_a_1235_ = lean_ctor_get(v___x_1206_, 0);
                                        v_isSharedCheck_1242_ =
                                            (!lean_is_exclusive(v___x_1206_)) as u8;
                                        if v_isSharedCheck_1242_ == 0 {
                                            v___x_1237_ = v___x_1206_;
                                            v_isShared_1238_ = v_isSharedCheck_1242_;
                                            state = 13;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1235_);
                                            lean_dec(v___x_1206_);
                                            v___x_1237_ = lean_box(0);
                                            v_isShared_1238_ = v_isSharedCheck_1242_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_1203_);
                                    lean_dec_ref(v_body_1199_);
                                    lean_dec(v_declName_1196_);
                                    lean_dec_ref(v_fvars_1131_);
                                    lean_dec_ref(v_localInsts_1130_);
                                    lean_dec_ref(v_lctx_1129_);
                                    lean_dec(v_i_1128_);
                                    lean_dec_ref(v_updateLocalInsts_1127_);
                                    lean_dec_ref(v_mkName_1126_);
                                    lean_dec_ref(v_finalize_1125_);
                                    v_a_1243_ = lean_ctor_get(v___x_1204_, 0);
                                    v_isSharedCheck_1250_ = (!lean_is_exclusive(v___x_1204_)) as u8;
                                    if v_isSharedCheck_1250_ == 0 {
                                        v___x_1245_ = v___x_1204_;
                                        v_isShared_1246_ = v_isSharedCheck_1250_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1243_);
                                        lean_dec(v___x_1204_);
                                        v___x_1245_ = lean_box(0);
                                        v_isShared_1246_ = v_isSharedCheck_1250_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_body_1199_);
                                lean_dec_ref(v_value_1198_);
                                lean_dec(v_declName_1196_);
                                lean_dec_ref(v_fvars_1131_);
                                lean_dec_ref(v_localInsts_1130_);
                                lean_dec_ref(v_lctx_1129_);
                                lean_dec(v_i_1128_);
                                lean_dec_ref(v_updateLocalInsts_1127_);
                                lean_dec_ref(v_mkName_1126_);
                                lean_dec_ref(v_finalize_1125_);
                                v_a_1251_ = lean_ctor_get(v___x_1202_, 0);
                                v_isSharedCheck_1258_ = (!lean_is_exclusive(v___x_1202_)) as u8;
                                if v_isSharedCheck_1258_ == 0 {
                                    v___x_1253_ = v___x_1202_;
                                    v_isShared_1254_ = v_isSharedCheck_1258_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_1251_);
                                    lean_dec(v___x_1202_);
                                    v___x_1253_ = lean_box(0);
                                    v_isShared_1254_ = v_isSharedCheck_1258_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            lean_dec(v_i_1128_);
                            lean_dec_ref(v_updateLocalInsts_1127_);
                            lean_dec_ref(v_mkName_1126_);
                            lean_inc(v_a_1138_);
                            lean_inc_ref(v_a_1137_);
                            lean_inc(v_a_1136_);
                            lean_inc_ref(v_a_1135_);
                            lean_inc(v_a_1134_);
                            lean_inc_ref(v_a_1133_);
                            v___x_1259_ = lean_apply_11(
                                v_finalize_1125_,
                                v_lctx_1129_,
                                v_localInsts_1130_,
                                v_fvars_1131_,
                                v_type_1132_,
                                v_a_1133_,
                                v_a_1134_,
                                v_a_1135_,
                                v_a_1136_,
                                v_a_1137_,
                                v_a_1138_,
                                lean_box(0),
                            );
                            return v___x_1259_;
                        }
                    }
                } else {
                    lean_dec(v_i_1128_);
                    lean_dec_ref(v_updateLocalInsts_1127_);
                    lean_dec_ref(v_mkName_1126_);
                    lean_inc(v_a_1138_);
                    lean_inc_ref(v_a_1137_);
                    lean_inc(v_a_1136_);
                    lean_inc_ref(v_a_1135_);
                    lean_inc(v_a_1134_);
                    lean_inc_ref(v_a_1133_);
                    v___x_1260_ = lean_apply_11(
                        v_finalize_1125_,
                        v_lctx_1129_,
                        v_localInsts_1130_,
                        v_fvars_1131_,
                        v_type_1132_,
                        v_a_1133_,
                        v_a_1134_,
                        v_a_1135_,
                        v_a_1136_,
                        v_a_1137_,
                        v_a_1138_,
                        lean_box(0),
                    );
                    return v___x_1260_;
                }
            }
            1 => {
                if v_isShared_1167_ == 0 {
                    v___x_1169_ = v___x_1166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
                    v___x_1169_ = v_reuseFailAlloc_1170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1169_;
            }
            3 => {
                if v_isShared_1175_ == 0 {
                    v___x_1177_ = v___x_1174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
                    v___x_1177_ = v_reuseFailAlloc_1178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1177_;
            }
            5 => {
                if v_isShared_1183_ == 0 {
                    v___x_1185_ = v___x_1182_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
                    v___x_1185_ = v_reuseFailAlloc_1186_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1185_;
            }
            7 => {
                if v_isShared_1191_ == 0 {
                    v___x_1193_ = v___x_1190_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
                    v___x_1193_ = v_reuseFailAlloc_1194_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1193_;
            }
            9 => {
                if v_isShared_1222_ == 0 {
                    v___x_1224_ = v___x_1221_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1224_;
            }
            11 => {
                if v_isShared_1230_ == 0 {
                    v___x_1232_ = v___x_1229_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
                    v___x_1232_ = v_reuseFailAlloc_1233_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1232_;
            }
            13 => {
                if v_isShared_1238_ == 0 {
                    v___x_1240_ = v___x_1237_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
                    v___x_1240_ = v_reuseFailAlloc_1241_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1240_;
            }
            15 => {
                if v_isShared_1246_ == 0 {
                    v___x_1248_ = v___x_1245_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
                    v___x_1248_ = v_reuseFailAlloc_1249_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1248_;
            }
            17 => {
                if v_isShared_1254_ == 0 {
                    v___x_1256_ = v___x_1253_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
                    v___x_1256_ = v_reuseFailAlloc_1257_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit___boxed(
    mut v_max_1261_: *mut LeanObject,
    mut v_finalize_1262_: *mut LeanObject,
    mut v_mkName_1263_: *mut LeanObject,
    mut v_updateLocalInsts_1264_: *mut LeanObject,
    mut v_i_1265_: *mut LeanObject,
    mut v_lctx_1266_: *mut LeanObject,
    mut v_localInsts_1267_: *mut LeanObject,
    mut v_fvars_1268_: *mut LeanObject,
    mut v_type_1269_: *mut LeanObject,
    mut v_a_1270_: *mut LeanObject,
    mut v_a_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
    mut v_a_1274_: *mut LeanObject,
    mut v_a_1275_: *mut LeanObject,
    mut v_a_1276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1277_: *mut LeanObject = core::ptr::null_mut();
    v_res_1277_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(
        v_max_1261_,
        v_finalize_1262_,
        v_mkName_1263_,
        v_updateLocalInsts_1264_,
        v_i_1265_,
        v_lctx_1266_,
        v_localInsts_1267_,
        v_fvars_1268_,
        v_type_1269_,
        v_a_1270_,
        v_a_1271_,
        v_a_1272_,
        v_a_1273_,
        v_a_1274_,
        v_a_1275_,
    );
    lean_dec(v_a_1275_);
    lean_dec_ref(v_a_1274_);
    lean_dec(v_a_1273_);
    lean_dec_ref(v_a_1272_);
    lean_dec(v_a_1271_);
    lean_dec_ref(v_a_1270_);
    lean_dec(v_max_1261_);
    return v_res_1277_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    v___x_1285_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___redArg(v___y_1283_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0___boxed(
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
    mut v___y_1288_: *mut LeanObject,
    mut v___y_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
    mut v___y_1291_: *mut LeanObject,
    mut v___y_1292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1293_: *mut LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit_spec__0_spec__0(v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
    lean_dec(v___y_1291_);
    lean_dec_ref(v___y_1290_);
    lean_dec(v___y_1289_);
    lean_dec_ref(v___y_1288_);
    lean_dec(v___y_1287_);
    lean_dec_ref(v___y_1286_);
    return v_res_1293_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(
    mut v_names_1294_: *mut LeanObject,
    mut v_binderName_1295_: *mut LeanObject,
    mut v_i_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u8 = 0;
    v___x_1302_ = lean_array_get_size(v_names_1294_);
    v___x_1303_ = lean_nat_dec_lt(v_i_1296_, v___x_1302_);
    if v___x_1303_ == 0 {
        let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
        v___x_1304_ = l_Lean_Core_mkFreshUserName(v_binderName_1295_, v___y_1299_, v___y_1300_);
        return v___x_1304_;
    } else {
        let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_binderName_1295_);
        v___x_1305_ = lean_array_fget_borrowed(v_names_1294_, v_i_1296_);
        lean_inc(v___x_1305_);
        v___x_1306_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1306_, 0, v___x_1305_);
        return v___x_1306_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed(
    mut v_names_1307_: *mut LeanObject,
    mut v_binderName_1308_: *mut LeanObject,
    mut v_i_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1315_: *mut LeanObject = core::ptr::null_mut();
    v_res_1315_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0(
        v_names_1307_,
        v_binderName_1308_,
        v_i_1309_,
        v___y_1310_,
        v___y_1311_,
        v___y_1312_,
        v___y_1313_,
    );
    lean_dec(v___y_1313_);
    lean_dec_ref(v___y_1312_);
    lean_dec(v___y_1311_);
    lean_dec_ref(v___y_1310_);
    lean_dec(v_i_1309_);
    lean_dec_ref(v_names_1307_);
    return v_res_1315_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(
    mut v_x_1316_: *mut LeanObject,
    mut v_x_1317_: *mut LeanObject,
    mut v_x_1318_: *mut LeanObject,
    mut v_x_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: u8 = 0;
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1320_ = lean_ctor_get(v_x_1316_, 0);
                v_vs_1321_ = lean_ctor_get(v_x_1316_, 1);
                v_isSharedCheck_1345_ = (!lean_is_exclusive(v_x_1316_)) as u8;
                if v_isSharedCheck_1345_ == 0 {
                    v___x_1323_ = v_x_1316_;
                    v_isShared_1324_ = v_isSharedCheck_1345_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1321_);
                    lean_inc(v_ks_1320_);
                    lean_dec(v_x_1316_);
                    v___x_1323_ = lean_box(0);
                    v_isShared_1324_ = v_isSharedCheck_1345_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1325_ = lean_array_get_size(v_ks_1320_);
                v___x_1326_ = lean_nat_dec_lt(v_x_1317_, v___x_1325_);
                if v___x_1326_ == 0 {
                    lean_dec(v_x_1317_);
                    v___x_1327_ = lean_array_push(v_ks_1320_, v_x_1318_);
                    v___x_1328_ = lean_array_push(v_vs_1321_, v_x_1319_);
                    if v_isShared_1324_ == 0 {
                        lean_ctor_set(v___x_1323_, 1, v___x_1328_);
                        lean_ctor_set(v___x_1323_, 0, v___x_1327_);
                        v___x_1330_ = v___x_1323_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
                        lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1328_);
                        v___x_1330_ = v_reuseFailAlloc_1331_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1332_ = lean_array_fget_borrowed(v_ks_1320_, v_x_1317_);
                    v___x_1333_ = l_Lean_instBEqMVarId_beq(v_x_1318_, v_k_x27_1332_);
                    if v___x_1333_ == 0 {
                        if v_isShared_1324_ == 0 {
                            v___x_1335_ = v___x_1323_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_ks_1320_);
                            lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_vs_1321_);
                            v___x_1335_ = v_reuseFailAlloc_1339_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1340_ = lean_array_fset(v_ks_1320_, v_x_1317_, v_x_1318_);
                        v___x_1341_ = lean_array_fset(v_vs_1321_, v_x_1317_, v_x_1319_);
                        lean_dec(v_x_1317_);
                        if v_isShared_1324_ == 0 {
                            lean_ctor_set(v___x_1323_, 1, v___x_1341_);
                            lean_ctor_set(v___x_1323_, 0, v___x_1340_);
                            v___x_1343_ = v___x_1323_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1340_);
                            lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1341_);
                            v___x_1343_ = v_reuseFailAlloc_1344_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1330_;
            }
            3 => {
                v___x_1336_ = lean_unsigned_to_nat(1);
                v___x_1337_ = lean_nat_add(v_x_1317_, v___x_1336_);
                lean_dec(v_x_1317_);
                v_x_1316_ = v___x_1335_;
                v_x_1317_ = v___x_1337_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_n_1346_: *mut LeanObject,
    mut v_k_1347_: *mut LeanObject,
    mut v_v_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    v___x_1349_ = lean_unsigned_to_nat(0);
    v___x_1350_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_1346_, v___x_1349_, v_k_1347_, v_v_1348_);
    return v___x_1350_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1351_: usize = 0;
    let mut v___x_1352_: usize = 0;
    let mut v___x_1353_: usize = 0;
    v___x_1351_ = 5usize;
    v___x_1352_ = 1usize;
    v___x_1353_ = lean_usize_shift_left(v___x_1352_, v___x_1351_);
    return v___x_1353_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1354_: usize = 0;
    let mut v___x_1355_: usize = 0;
    let mut v___x_1356_: usize = 0;
    v___x_1354_ = 1usize;
    v___x_1355_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_1356_ = lean_usize_sub(v___x_1355_, v___x_1354_);
    return v___x_1356_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(
    mut v_x_1358_: *mut LeanObject,
    mut v_x_1359_: usize,
    mut v_x_1360_: usize,
    mut v_x_1361_: *mut LeanObject,
    mut v_x_1362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: usize = 0;
    let mut v___x_1365_: usize = 0;
    let mut v___x_1366_: usize = 0;
    let mut v___x_1367_: usize = 0;
    let mut v_j_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v_v_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_node_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1398_: u8 = 0;
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: usize = 0;
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut v_unused_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: u8 = 0;
    let mut v_ks_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: usize = 0;
    let mut v___x_1425_: u8 = 0;
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v_reuseFailAlloc_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1358_) == 0 {
                    v_es_1363_ = lean_ctor_get(v_x_1358_, 0);
                    v___x_1364_ = 5usize;
                    v___x_1365_ = 1usize;
                    v___x_1366_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_1367_ = lean_usize_land(v_x_1359_, v___x_1366_);
                    v_j_1368_ = lean_usize_to_nat(v___x_1367_);
                    v___x_1369_ = lean_array_get_size(v_es_1363_);
                    v___x_1370_ = lean_nat_dec_lt(v_j_1368_, v___x_1369_);
                    if v___x_1370_ == 0 {
                        lean_dec(v_j_1368_);
                        lean_dec(v_x_1362_);
                        lean_dec(v_x_1361_);
                        return v_x_1358_;
                    } else {
                        lean_inc_ref(v_es_1363_);
                        v_isSharedCheck_1407_ = (!lean_is_exclusive(v_x_1358_)) as u8;
                        if v_isSharedCheck_1407_ == 0 {
                            v_unused_1408_ = lean_ctor_get(v_x_1358_, 0);
                            lean_dec(v_unused_1408_);
                            v___x_1372_ = v_x_1358_;
                            v_isShared_1373_ = v_isSharedCheck_1407_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1358_);
                            v___x_1372_ = lean_box(0);
                            v_isShared_1373_ = v_isSharedCheck_1407_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1409_ = lean_ctor_get(v_x_1358_, 0);
                    v_vs_1410_ = lean_ctor_get(v_x_1358_, 1);
                    v_isSharedCheck_1430_ = (!lean_is_exclusive(v_x_1358_)) as u8;
                    if v_isSharedCheck_1430_ == 0 {
                        v___x_1412_ = v_x_1358_;
                        v_isShared_1413_ = v_isSharedCheck_1430_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1410_);
                        lean_inc(v_ks_1409_);
                        lean_dec(v_x_1358_);
                        v___x_1412_ = lean_box(0);
                        v_isShared_1413_ = v_isSharedCheck_1430_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1374_ = lean_array_fget(v_es_1363_, v_j_1368_);
                v___x_1375_ = lean_box(0);
                v_xs_x27_1376_ = lean_array_fset(v_es_1363_, v_j_1368_, v___x_1375_);
                match lean_obj_tag(v_v_1374_) {
                    0 => {
                        v_key_1383_ = lean_ctor_get(v_v_1374_, 0);
                        v_val_1384_ = lean_ctor_get(v_v_1374_, 1);
                        v_isSharedCheck_1394_ = (!lean_is_exclusive(v_v_1374_)) as u8;
                        if v_isSharedCheck_1394_ == 0 {
                            v___x_1386_ = v_v_1374_;
                            v_isShared_1387_ = v_isSharedCheck_1394_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1384_);
                            lean_inc(v_key_1383_);
                            lean_dec(v_v_1374_);
                            v___x_1386_ = lean_box(0);
                            v_isShared_1387_ = v_isSharedCheck_1394_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1395_ = lean_ctor_get(v_v_1374_, 0);
                        v_isSharedCheck_1405_ = (!lean_is_exclusive(v_v_1374_)) as u8;
                        if v_isSharedCheck_1405_ == 0 {
                            v___x_1397_ = v_v_1374_;
                            v_isShared_1398_ = v_isSharedCheck_1405_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1395_);
                            lean_dec(v_v_1374_);
                            v___x_1397_ = lean_box(0);
                            v_isShared_1398_ = v_isSharedCheck_1405_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1406_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1406_, 0, v_x_1361_);
                        lean_ctor_set(v___x_1406_, 1, v_x_1362_);
                        v___y_1378_ = v___x_1406_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1379_ = lean_array_fset(v_xs_x27_1376_, v_j_1368_, v___y_1378_);
                lean_dec(v_j_1368_);
                if v_isShared_1373_ == 0 {
                    lean_ctor_set(v___x_1372_, 0, v___x_1379_);
                    v___x_1381_ = v___x_1372_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
                    v___x_1381_ = v_reuseFailAlloc_1382_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1381_;
            }
            4 => {
                v___x_1388_ = l_Lean_instBEqMVarId_beq(v_x_1361_, v_key_1383_);
                if v___x_1388_ == 0 {
                    lean_del_object(v___x_1386_);
                    v___x_1389_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1383_,
                        v_val_1384_,
                        v_x_1361_,
                        v_x_1362_,
                    );
                    v___x_1390_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1390_, 0, v___x_1389_);
                    v___y_1378_ = v___x_1390_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1384_);
                    lean_dec(v_key_1383_);
                    if v_isShared_1387_ == 0 {
                        lean_ctor_set(v___x_1386_, 1, v_x_1362_);
                        lean_ctor_set(v___x_1386_, 0, v_x_1361_);
                        v___x_1392_ = v___x_1386_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_x_1361_);
                        lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_x_1362_);
                        v___x_1392_ = v_reuseFailAlloc_1393_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1378_ = v___x_1392_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1399_ = lean_usize_shift_right(v_x_1359_, v___x_1364_);
                v___x_1400_ = lean_usize_add(v_x_1360_, v___x_1365_);
                v___x_1401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_node_1395_, v___x_1399_, v___x_1400_, v_x_1361_, v_x_1362_);
                if v_isShared_1398_ == 0 {
                    lean_ctor_set(v___x_1397_, 0, v___x_1401_);
                    v___x_1403_ = v___x_1397_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
                    v___x_1403_ = v_reuseFailAlloc_1404_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1378_ = v___x_1403_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1413_ == 0 {
                    v___x_1415_ = v___x_1412_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_ks_1409_);
                    lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_vs_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1429_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1416_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1415_, v_x_1361_, v_x_1362_);
                v___x_1424_ = 7usize;
                v___x_1425_ = lean_usize_dec_le(v___x_1424_, v_x_1360_);
                if v___x_1425_ == 0 {
                    v___x_1426_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1416_);
                    v___x_1427_ = lean_unsigned_to_nat(4);
                    v___x_1428_ = lean_nat_dec_lt(v___x_1426_, v___x_1427_);
                    lean_dec(v___x_1426_);
                    v___y_1418_ = v___x_1428_;
                    state = 10;
                    continue;
                } else {
                    v___y_1418_ = v___x_1425_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1418_ == 0 {
                    v_ks_1419_ = lean_ctor_get(v_newNode_1416_, 0);
                    lean_inc_ref(v_ks_1419_);
                    v_vs_1420_ = lean_ctor_get(v_newNode_1416_, 1);
                    lean_inc_ref(v_vs_1420_);
                    lean_dec_ref(v_newNode_1416_);
                    v___x_1421_ = lean_unsigned_to_nat(0);
                    v___x_1422_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_1423_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1360_, v_ks_1419_, v_vs_1420_, v___x_1421_, v___x_1422_);
                    lean_dec_ref(v_vs_1420_);
                    lean_dec_ref(v_ks_1419_);
                    return v___x_1423_;
                } else {
                    return v_newNode_1416_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_depth_1431_: usize,
    mut v_keys_1432_: *mut LeanObject,
    mut v_vals_1433_: *mut LeanObject,
    mut v_i_1434_: *mut LeanObject,
    mut v_entries_1435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut v_k_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: u64 = 0;
    let mut v_h_1441_: usize = 0;
    let mut v___x_1442_: usize = 0;
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: usize = 0;
    let mut v___x_1445_: usize = 0;
    let mut v___x_1446_: usize = 0;
    let mut v_h_1447_: usize = 0;
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1436_ = lean_array_get_size(v_keys_1432_);
                v___x_1437_ = lean_nat_dec_lt(v_i_1434_, v___x_1436_);
                if v___x_1437_ == 0 {
                    lean_dec(v_i_1434_);
                    return v_entries_1435_;
                } else {
                    v_k_1438_ = lean_array_fget_borrowed(v_keys_1432_, v_i_1434_);
                    v_v_1439_ = lean_array_fget_borrowed(v_vals_1433_, v_i_1434_);
                    v___x_1440_ = l_Lean_instHashableMVarId_hash(v_k_1438_);
                    v_h_1441_ = lean_uint64_to_usize(v___x_1440_);
                    v___x_1442_ = 5usize;
                    v___x_1443_ = lean_unsigned_to_nat(1);
                    v___x_1444_ = 1usize;
                    v___x_1445_ = lean_usize_sub(v_depth_1431_, v___x_1444_);
                    v___x_1446_ = lean_usize_mul(v___x_1442_, v___x_1445_);
                    v_h_1447_ = lean_usize_shift_right(v_h_1441_, v___x_1446_);
                    v___x_1448_ = lean_nat_add(v_i_1434_, v___x_1443_);
                    lean_dec(v_i_1434_);
                    lean_inc(v_v_1439_);
                    lean_inc(v_k_1438_);
                    v___x_1449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_entries_1435_, v_h_1447_, v_depth_1431_, v_k_1438_, v_v_1439_);
                    v_i_1434_ = v___x_1448_;
                    v_entries_1435_ = v___x_1449_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_depth_1451_: *mut LeanObject,
    mut v_keys_1452_: *mut LeanObject,
    mut v_vals_1453_: *mut LeanObject,
    mut v_i_1454_: *mut LeanObject,
    mut v_entries_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1456_: usize = 0;
    let mut v_res_1457_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1456_ = lean_unbox_usize(v_depth_1451_);
    lean_dec(v_depth_1451_);
    v_res_1457_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_1456_, v_keys_1452_, v_vals_1453_, v_i_1454_, v_entries_1455_);
    lean_dec_ref(v_vals_1453_);
    lean_dec_ref(v_keys_1452_);
    return v_res_1457_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1458_: *mut LeanObject,
    mut v_x_1459_: *mut LeanObject,
    mut v_x_1460_: *mut LeanObject,
    mut v_x_1461_: *mut LeanObject,
    mut v_x_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5923__boxed_1463_: usize = 0;
    let mut v_x_5924__boxed_1464_: usize = 0;
    let mut v_res_1465_: *mut LeanObject = core::ptr::null_mut();
    v_x_5923__boxed_1463_ = lean_unbox_usize(v_x_1459_);
    lean_dec(v_x_1459_);
    v_x_5924__boxed_1464_ = lean_unbox_usize(v_x_1460_);
    lean_dec(v_x_1460_);
    v_res_1465_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_1458_, v_x_5923__boxed_1463_, v_x_5924__boxed_1464_, v_x_1461_, v_x_1462_);
    return v_res_1465_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(
    mut v_x_1466_: *mut LeanObject,
    mut v_x_1467_: *mut LeanObject,
    mut v_x_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1469_: u64 = 0;
    let mut v___x_1470_: usize = 0;
    let mut v___x_1471_: usize = 0;
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    v___x_1469_ = l_Lean_instHashableMVarId_hash(v_x_1467_);
    v___x_1470_ = lean_uint64_to_usize(v___x_1469_);
    v___x_1471_ = 1usize;
    v___x_1472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_1466_, v___x_1470_, v___x_1471_, v_x_1467_, v_x_1468_);
    return v___x_1472_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(
    mut v_mvarId_1473_: *mut LeanObject,
    mut v_val_1474_: *mut LeanObject,
    mut v___y_1475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1485_: u8 = 0;
    let mut v_depth_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1477_ = lean_st_ref_take(v___y_1475_);
                v_mctx_1478_ = lean_ctor_get(v___x_1477_, 0);
                v_cache_1479_ = lean_ctor_get(v___x_1477_, 1);
                v_zetaDeltaFVarIds_1480_ = lean_ctor_get(v___x_1477_, 2);
                v_postponed_1481_ = lean_ctor_get(v___x_1477_, 3);
                v_diag_1482_ = lean_ctor_get(v___x_1477_, 4);
                v_isSharedCheck_1510_ = (!lean_is_exclusive(v___x_1477_)) as u8;
                if v_isSharedCheck_1510_ == 0 {
                    v___x_1484_ = v___x_1477_;
                    v_isShared_1485_ = v_isSharedCheck_1510_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1482_);
                    lean_inc(v_postponed_1481_);
                    lean_inc(v_zetaDeltaFVarIds_1480_);
                    lean_inc(v_cache_1479_);
                    lean_inc(v_mctx_1478_);
                    lean_dec(v___x_1477_);
                    v___x_1484_ = lean_box(0);
                    v_isShared_1485_ = v_isSharedCheck_1510_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1486_ = lean_ctor_get(v_mctx_1478_, 0);
                v_levelAssignDepth_1487_ = lean_ctor_get(v_mctx_1478_, 1);
                v_lmvarCounter_1488_ = lean_ctor_get(v_mctx_1478_, 2);
                v_mvarCounter_1489_ = lean_ctor_get(v_mctx_1478_, 3);
                v_lDecls_1490_ = lean_ctor_get(v_mctx_1478_, 4);
                v_decls_1491_ = lean_ctor_get(v_mctx_1478_, 5);
                v_userNames_1492_ = lean_ctor_get(v_mctx_1478_, 6);
                v_lAssignment_1493_ = lean_ctor_get(v_mctx_1478_, 7);
                v_eAssignment_1494_ = lean_ctor_get(v_mctx_1478_, 8);
                v_dAssignment_1495_ = lean_ctor_get(v_mctx_1478_, 9);
                v_isSharedCheck_1509_ = (!lean_is_exclusive(v_mctx_1478_)) as u8;
                if v_isSharedCheck_1509_ == 0 {
                    v___x_1497_ = v_mctx_1478_;
                    v_isShared_1498_ = v_isSharedCheck_1509_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1495_);
                    lean_inc(v_eAssignment_1494_);
                    lean_inc(v_lAssignment_1493_);
                    lean_inc(v_userNames_1492_);
                    lean_inc(v_decls_1491_);
                    lean_inc(v_lDecls_1490_);
                    lean_inc(v_mvarCounter_1489_);
                    lean_inc(v_lmvarCounter_1488_);
                    lean_inc(v_levelAssignDepth_1487_);
                    lean_inc(v_depth_1486_);
                    lean_dec(v_mctx_1478_);
                    v___x_1497_ = lean_box(0);
                    v_isShared_1498_ = v_isSharedCheck_1509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1499_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_eAssignment_1494_, v_mvarId_1473_, v_val_1474_);
                if v_isShared_1498_ == 0 {
                    lean_ctor_set(v___x_1497_, 8, v___x_1499_);
                    v___x_1501_ = v___x_1497_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_depth_1486_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_levelAssignDepth_1487_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_lmvarCounter_1488_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_mvarCounter_1489_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_lDecls_1490_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_decls_1491_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 6, v_userNames_1492_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 7, v_lAssignment_1493_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 8, v___x_1499_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 9, v_dAssignment_1495_);
                    v___x_1501_ = v_reuseFailAlloc_1508_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1485_ == 0 {
                    lean_ctor_set(v___x_1484_, 0, v___x_1501_);
                    v___x_1503_ = v___x_1484_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1501_);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_cache_1479_);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_zetaDeltaFVarIds_1480_);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_postponed_1481_);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_diag_1482_);
                    v___x_1503_ = v_reuseFailAlloc_1507_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1504_ = lean_st_ref_set(v___y_1475_, v___x_1503_);
                v___x_1505_ = lean_box(0);
                v___x_1506_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1506_, 0, v___x_1505_);
                return v___x_1506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg___boxed(
    mut v_mvarId_1511_: *mut LeanObject,
    mut v_val_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
    mut v___y_1514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1515_: *mut LeanObject = core::ptr::null_mut();
    v_res_1515_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_1511_, v_val_1512_, v___y_1513_);
    lean_dec(v___y_1513_);
    return v_res_1515_;
}
pub unsafe fn l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(
    mut v_mvarId_1516_: *mut LeanObject,
    mut v_fvars_1517_: *mut LeanObject,
    mut v_mvarIdPending_1518_: *mut LeanObject,
    mut v___y_1519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v_depth_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut v_isSharedCheck_1555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1521_ = lean_st_ref_take(v___y_1519_);
                v_mctx_1522_ = lean_ctor_get(v___x_1521_, 0);
                v_cache_1523_ = lean_ctor_get(v___x_1521_, 1);
                v_zetaDeltaFVarIds_1524_ = lean_ctor_get(v___x_1521_, 2);
                v_postponed_1525_ = lean_ctor_get(v___x_1521_, 3);
                v_diag_1526_ = lean_ctor_get(v___x_1521_, 4);
                v_isSharedCheck_1555_ = (!lean_is_exclusive(v___x_1521_)) as u8;
                if v_isSharedCheck_1555_ == 0 {
                    v___x_1528_ = v___x_1521_;
                    v_isShared_1529_ = v_isSharedCheck_1555_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1526_);
                    lean_inc(v_postponed_1525_);
                    lean_inc(v_zetaDeltaFVarIds_1524_);
                    lean_inc(v_cache_1523_);
                    lean_inc(v_mctx_1522_);
                    lean_dec(v___x_1521_);
                    v___x_1528_ = lean_box(0);
                    v_isShared_1529_ = v_isSharedCheck_1555_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1530_ = lean_ctor_get(v_mctx_1522_, 0);
                v_levelAssignDepth_1531_ = lean_ctor_get(v_mctx_1522_, 1);
                v_lmvarCounter_1532_ = lean_ctor_get(v_mctx_1522_, 2);
                v_mvarCounter_1533_ = lean_ctor_get(v_mctx_1522_, 3);
                v_lDecls_1534_ = lean_ctor_get(v_mctx_1522_, 4);
                v_decls_1535_ = lean_ctor_get(v_mctx_1522_, 5);
                v_userNames_1536_ = lean_ctor_get(v_mctx_1522_, 6);
                v_lAssignment_1537_ = lean_ctor_get(v_mctx_1522_, 7);
                v_eAssignment_1538_ = lean_ctor_get(v_mctx_1522_, 8);
                v_dAssignment_1539_ = lean_ctor_get(v_mctx_1522_, 9);
                v_isSharedCheck_1554_ = (!lean_is_exclusive(v_mctx_1522_)) as u8;
                if v_isSharedCheck_1554_ == 0 {
                    v___x_1541_ = v_mctx_1522_;
                    v_isShared_1542_ = v_isSharedCheck_1554_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1539_);
                    lean_inc(v_eAssignment_1538_);
                    lean_inc(v_lAssignment_1537_);
                    lean_inc(v_userNames_1536_);
                    lean_inc(v_decls_1535_);
                    lean_inc(v_lDecls_1534_);
                    lean_inc(v_mvarCounter_1533_);
                    lean_inc(v_lmvarCounter_1532_);
                    lean_inc(v_levelAssignDepth_1531_);
                    lean_inc(v_depth_1530_);
                    lean_dec(v_mctx_1522_);
                    v___x_1541_ = lean_box(0);
                    v_isShared_1542_ = v_isSharedCheck_1554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1543_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1543_, 0, v_fvars_1517_);
                lean_ctor_set(v___x_1543_, 1, v_mvarIdPending_1518_);
                v___x_1544_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_dAssignment_1539_, v_mvarId_1516_, v___x_1543_);
                if v_isShared_1542_ == 0 {
                    lean_ctor_set(v___x_1541_, 9, v___x_1544_);
                    v___x_1546_ = v___x_1541_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_depth_1530_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_levelAssignDepth_1531_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_lmvarCounter_1532_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_mvarCounter_1533_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_lDecls_1534_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 5, v_decls_1535_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 6, v_userNames_1536_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 7, v_lAssignment_1537_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 8, v_eAssignment_1538_);
                    lean_ctor_set(v_reuseFailAlloc_1553_, 9, v___x_1544_);
                    v___x_1546_ = v_reuseFailAlloc_1553_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1529_ == 0 {
                    lean_ctor_set(v___x_1528_, 0, v___x_1546_);
                    v___x_1548_ = v___x_1528_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1546_);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_cache_1523_);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_zetaDeltaFVarIds_1524_);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_postponed_1525_);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_diag_1526_);
                    v___x_1548_ = v_reuseFailAlloc_1552_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1549_ = lean_st_ref_set(v___y_1519_, v___x_1548_);
                v___x_1550_ = lean_box(0);
                v___x_1551_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1551_, 0, v___x_1550_);
                return v___x_1551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg___boxed(
    mut v_mvarId_1556_: *mut LeanObject,
    mut v_fvars_1557_: *mut LeanObject,
    mut v_mvarIdPending_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1561_: *mut LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_1556_, v_fvars_1557_, v_mvarIdPending_1558_, v___y_1559_);
    lean_dec(v___y_1559_);
    return v_res_1561_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(
    mut v___x_1562_: *mut LeanObject,
    mut v_userName_1563_: *mut LeanObject,
    mut v_lctx_1564_: *mut LeanObject,
    mut v_localInstances_1565_: *mut LeanObject,
    mut v_type_1566_: *mut LeanObject,
    mut v_max_1567_: *mut LeanObject,
    mut v_mvarId_1568_: *mut LeanObject,
    mut v_lctx_1569_: *mut LeanObject,
    mut v_localInsts_1570_: *mut LeanObject,
    mut v_fvars_1571_: *mut LeanObject,
    mut v_type_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
    mut v___y_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
    mut v___y_1578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1595_: u8 = 0;
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_unused_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1610_: u8 = 0;
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1614_: u8 = 0;
    let mut v_a_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1622_: u8 = 0;
    let mut v_a_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1630_: u8 = 0;
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1580_ = lean_array_get_size(v_fvars_1571_);
                v___x_1581_ = lean_nat_dec_eq(v___x_1580_, v___x_1562_);
                if v___x_1581_ == 0 {
                    v___x_1582_ = l_Lean_Meta_Sym_instantiateRevRangeS(
                        v_type_1572_,
                        v___x_1562_,
                        v___x_1580_,
                        v_fvars_1571_,
                        v___y_1573_,
                        v___y_1574_,
                        v___y_1575_,
                        v___y_1576_,
                        v___y_1577_,
                        v___y_1578_,
                    );
                    if lean_obj_tag(v___x_1582_) == 0 {
                        v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
                        lean_inc(v_a_1583_);
                        lean_dec_ref_known(v___x_1582_, 1);
                        v___x_1584_ = 2;
                        lean_inc(v___x_1562_);
                        v___x_1585_ = l_Lean_Meta_mkFreshExprMVarAt(
                            v_lctx_1569_,
                            v_localInsts_1570_,
                            v_a_1583_,
                            v___x_1584_,
                            v_userName_1563_,
                            v___x_1562_,
                            v___y_1575_,
                            v___y_1576_,
                            v___y_1577_,
                            v___y_1578_,
                        );
                        if lean_obj_tag(v___x_1585_) == 0 {
                            v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
                            lean_inc(v_a_1586_);
                            lean_dec_ref_known(v___x_1585_, 1);
                            v___x_1587_ = lean_box(0);
                            lean_inc(v___x_1562_);
                            lean_inc_ref(v_type_1566_);
                            v___x_1588_ = l_Lean_Meta_mkFreshExprMVarAt(
                                v_lctx_1564_,
                                v_localInstances_1565_,
                                v_type_1566_,
                                v___x_1584_,
                                v___x_1587_,
                                v___x_1562_,
                                v___y_1575_,
                                v___y_1576_,
                                v___y_1577_,
                                v___y_1578_,
                            );
                            if lean_obj_tag(v___x_1588_) == 0 {
                                v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
                                lean_inc(v_a_1589_);
                                lean_dec_ref_known(v___x_1588_, 1);
                                v___x_1590_ = l_Lean_Expr_mvarId_x21(v_a_1586_);
                                lean_dec(v_a_1586_);
                                v___x_1602_ = l_Lean_Expr_mvarId_x21(v_a_1589_);
                                lean_inc(v___x_1590_);
                                lean_inc_ref(v_fvars_1571_);
                                v___x_1603_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v___x_1602_, v_fvars_1571_, v___x_1590_, v___y_1576_);
                                lean_dec_ref(v___x_1603_);
                                v___x_1604_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkAppBVars(v_a_1589_, v___x_1580_);
                                v___x_1605_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_mkValueLoop(v_max_1567_, v___x_1562_, v_type_1566_, v___x_1604_);
                                lean_dec_ref(v___x_1604_);
                                lean_dec(v___x_1562_);
                                v___x_1606_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_1568_, v___x_1605_, v___y_1576_);
                                v___y_1592_ = v___x_1606_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_a_1586_);
                                lean_dec_ref(v_fvars_1571_);
                                lean_dec(v_mvarId_1568_);
                                lean_dec_ref(v_type_1566_);
                                lean_dec(v___x_1562_);
                                v_a_1607_ = lean_ctor_get(v___x_1588_, 0);
                                v_isSharedCheck_1614_ = (!lean_is_exclusive(v___x_1588_)) as u8;
                                if v_isSharedCheck_1614_ == 0 {
                                    v___x_1609_ = v___x_1588_;
                                    v_isShared_1610_ = v_isSharedCheck_1614_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_1607_);
                                    lean_dec(v___x_1588_);
                                    v___x_1609_ = lean_box(0);
                                    v_isShared_1610_ = v_isSharedCheck_1614_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_fvars_1571_);
                            lean_dec(v_mvarId_1568_);
                            lean_dec_ref(v_type_1566_);
                            lean_dec_ref(v_localInstances_1565_);
                            lean_dec_ref(v_lctx_1564_);
                            lean_dec(v___x_1562_);
                            v_a_1615_ = lean_ctor_get(v___x_1585_, 0);
                            v_isSharedCheck_1622_ = (!lean_is_exclusive(v___x_1585_)) as u8;
                            if v_isSharedCheck_1622_ == 0 {
                                v___x_1617_ = v___x_1585_;
                                v_isShared_1618_ = v_isSharedCheck_1622_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1615_);
                                lean_dec(v___x_1585_);
                                v___x_1617_ = lean_box(0);
                                v_isShared_1618_ = v_isSharedCheck_1622_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_fvars_1571_);
                        lean_dec_ref(v_localInsts_1570_);
                        lean_dec_ref(v_lctx_1569_);
                        lean_dec(v_mvarId_1568_);
                        lean_dec_ref(v_type_1566_);
                        lean_dec_ref(v_localInstances_1565_);
                        lean_dec_ref(v_lctx_1564_);
                        lean_dec(v_userName_1563_);
                        lean_dec(v___x_1562_);
                        v_a_1623_ = lean_ctor_get(v___x_1582_, 0);
                        v_isSharedCheck_1630_ = (!lean_is_exclusive(v___x_1582_)) as u8;
                        if v_isSharedCheck_1630_ == 0 {
                            v___x_1625_ = v___x_1582_;
                            v_isShared_1626_ = v_isSharedCheck_1630_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1623_);
                            lean_dec(v___x_1582_);
                            v___x_1625_ = lean_box(0);
                            v_isShared_1626_ = v_isSharedCheck_1630_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_1572_);
                    lean_dec_ref(v_fvars_1571_);
                    lean_dec_ref(v_localInsts_1570_);
                    lean_dec_ref(v_lctx_1569_);
                    lean_dec_ref(v_type_1566_);
                    lean_dec_ref(v_localInstances_1565_);
                    lean_dec_ref(v_lctx_1564_);
                    lean_dec(v_userName_1563_);
                    v___x_1631_ = lean_mk_empty_array_with_capacity(v___x_1562_);
                    lean_dec(v___x_1562_);
                    v___x_1632_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1632_, 0, v___x_1631_);
                    lean_ctor_set(v___x_1632_, 1, v_mvarId_1568_);
                    v___x_1633_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1633_, 0, v___x_1632_);
                    return v___x_1633_;
                }
            }
            1 => {
                v_isSharedCheck_1600_ = (!lean_is_exclusive(v___y_1592_)) as u8;
                if v_isSharedCheck_1600_ == 0 {
                    v_unused_1601_ = lean_ctor_get(v___y_1592_, 0);
                    lean_dec(v_unused_1601_);
                    v___x_1594_ = v___y_1592_;
                    v_isShared_1595_ = v_isSharedCheck_1600_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_1592_);
                    v___x_1594_ = lean_box(0);
                    v_isShared_1595_ = v_isSharedCheck_1600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1596_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1596_, 0, v_fvars_1571_);
                lean_ctor_set(v___x_1596_, 1, v___x_1590_);
                if v_isShared_1595_ == 0 {
                    lean_ctor_set(v___x_1594_, 0, v___x_1596_);
                    v___x_1598_ = v___x_1594_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
                    v___x_1598_ = v_reuseFailAlloc_1599_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1598_;
            }
            4 => {
                if v_isShared_1610_ == 0 {
                    v___x_1612_ = v___x_1609_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
                    v___x_1612_ = v_reuseFailAlloc_1613_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1612_;
            }
            6 => {
                if v_isShared_1618_ == 0 {
                    v___x_1620_ = v___x_1617_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
                    v___x_1620_ = v_reuseFailAlloc_1621_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1620_;
            }
            8 => {
                if v_isShared_1626_ == 0 {
                    v___x_1628_ = v___x_1625_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
                    v___x_1628_ = v_reuseFailAlloc_1629_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1628_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = *_args.add(0);
    let mut v_userName_1635_: *mut LeanObject = *_args.add(1);
    let mut v_lctx_1636_: *mut LeanObject = *_args.add(2);
    let mut v_localInstances_1637_: *mut LeanObject = *_args.add(3);
    let mut v_type_1638_: *mut LeanObject = *_args.add(4);
    let mut v_max_1639_: *mut LeanObject = *_args.add(5);
    let mut v_mvarId_1640_: *mut LeanObject = *_args.add(6);
    let mut v_lctx_1641_: *mut LeanObject = *_args.add(7);
    let mut v_localInsts_1642_: *mut LeanObject = *_args.add(8);
    let mut v_fvars_1643_: *mut LeanObject = *_args.add(9);
    let mut v_type_1644_: *mut LeanObject = *_args.add(10);
    let mut v___y_1645_: *mut LeanObject = *_args.add(11);
    let mut v___y_1646_: *mut LeanObject = *_args.add(12);
    let mut v___y_1647_: *mut LeanObject = *_args.add(13);
    let mut v___y_1648_: *mut LeanObject = *_args.add(14);
    let mut v___y_1649_: *mut LeanObject = *_args.add(15);
    let mut v___y_1650_: *mut LeanObject = *_args.add(16);
    let mut v___y_1651_: *mut LeanObject = *_args.add(17);
    let mut v_res_1652_: *mut LeanObject = core::ptr::null_mut();
    v_res_1652_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1(
        v___x_1634_,
        v_userName_1635_,
        v_lctx_1636_,
        v_localInstances_1637_,
        v_type_1638_,
        v_max_1639_,
        v_mvarId_1640_,
        v_lctx_1641_,
        v_localInsts_1642_,
        v_fvars_1643_,
        v_type_1644_,
        v___y_1645_,
        v___y_1646_,
        v___y_1647_,
        v___y_1648_,
        v___y_1649_,
        v___y_1650_,
    );
    lean_dec(v___y_1650_);
    lean_dec_ref(v___y_1649_);
    lean_dec(v___y_1648_);
    lean_dec_ref(v___y_1647_);
    lean_dec(v___y_1646_);
    lean_dec_ref(v___y_1645_);
    lean_dec(v_max_1639_);
    return v_res_1652_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2(
    mut v_env_1653_: *mut LeanObject,
    mut v_localInsts_1654_: *mut LeanObject,
    mut v_fvar_1655_: *mut LeanObject,
    mut v_type_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    v___x_1657_ = l_Lean_Meta_Sym_isClass_x3f(v_env_1653_, v_type_1656_);
    if lean_obj_tag(v___x_1657_) == 1 {
        let mut v_val_1658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
        v_val_1658_ = lean_ctor_get(v___x_1657_, 0);
        lean_inc(v_val_1658_);
        lean_dec_ref_known(v___x_1657_, 1);
        v___x_1659_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1659_, 0, v_val_1658_);
        lean_ctor_set(v___x_1659_, 1, v_fvar_1655_);
        v___x_1660_ = lean_array_push(v_localInsts_1654_, v___x_1659_);
        return v___x_1660_;
    } else {
        lean_dec(v___x_1657_);
        lean_dec_ref(v_fvar_1655_);
        return v_localInsts_1654_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(
    mut v_sz_1661_: usize,
    mut v_i_1662_: usize,
    mut v_bs_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1664_: u8 = 0;
    let mut v_v_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: usize = 0;
    let mut v___x_1670_: usize = 0;
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1664_ = lean_usize_dec_lt(v_i_1662_, v_sz_1661_);
                if v___x_1664_ == 0 {
                    return v_bs_1663_;
                } else {
                    v_v_1665_ = lean_array_uget(v_bs_1663_, v_i_1662_);
                    v___x_1666_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1667_ = lean_array_uset(v_bs_1663_, v_i_1662_, v___x_1666_);
                    v___x_1668_ = l_Lean_Expr_fvarId_x21(v_v_1665_);
                    lean_dec(v_v_1665_);
                    v___x_1669_ = 1usize;
                    v___x_1670_ = lean_usize_add(v_i_1662_, v___x_1669_);
                    v___x_1671_ = lean_array_uset(v_bs_x27_1667_, v_i_1662_, v___x_1668_);
                    v_i_1662_ = v___x_1670_;
                    v_bs_1663_ = v___x_1671_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2___boxed(
    mut v_sz_1673_: *mut LeanObject,
    mut v_i_1674_: *mut LeanObject,
    mut v_bs_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1676_: usize = 0;
    let mut v_i_boxed_1677_: usize = 0;
    let mut v_res_1678_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1676_ = lean_unbox_usize(v_sz_1673_);
    lean_dec(v_sz_1673_);
    v_i_boxed_1677_ = lean_unbox_usize(v_i_1674_);
    lean_dec(v_i_1674_);
    v_res_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_boxed_1676_, v_i_boxed_1677_, v_bs_1675_);
    return v_res_1678_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(
    mut v_mvarId_1683_: *mut LeanObject,
    mut v_max_1684_: *mut LeanObject,
    mut v_names_1685_: *mut LeanObject,
    mut v_a_1686_: *mut LeanObject,
    mut v_a_1687_: *mut LeanObject,
    mut v_a_1688_: *mut LeanObject,
    mut v_a_1689_: *mut LeanObject,
    mut v_a_1690_: *mut LeanObject,
    mut v_a_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1711_: u8 = 0;
    let mut v_fst_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v_sz_1717_: usize = 0;
    let mut v___x_1718_: usize = 0;
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1726_: u8 = 0;
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_a_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v_a_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1693_ = lean_unsigned_to_nat(0);
                v___x_1694_ = lean_nat_dec_eq(v_max_1684_, v___x_1693_);
                if v___x_1694_ == 0 {
                    v___x_1695_ = lean_st_ref_get(v_a_1691_);
                    lean_inc(v_mvarId_1683_);
                    v___x_1696_ = l_Lean_MVarId_getDecl(
                        v_mvarId_1683_,
                        v_a_1688_,
                        v_a_1689_,
                        v_a_1690_,
                        v_a_1691_,
                    );
                    if lean_obj_tag(v___x_1696_) == 0 {
                        v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
                        lean_inc(v_a_1697_);
                        lean_dec_ref_known(v___x_1696_, 1);
                        v_env_1698_ = lean_ctor_get(v___x_1695_, 0);
                        lean_inc_ref(v_env_1698_);
                        lean_dec(v___x_1695_);
                        v_userName_1699_ = lean_ctor_get(v_a_1697_, 0);
                        lean_inc(v_userName_1699_);
                        v_lctx_1700_ = lean_ctor_get(v_a_1697_, 1);
                        lean_inc_ref_n(v_lctx_1700_, 2);
                        v_type_1701_ = lean_ctor_get(v_a_1697_, 2);
                        lean_inc_ref_n(v_type_1701_, 2);
                        v_localInstances_1702_ = lean_ctor_get(v_a_1697_, 4);
                        lean_inc_ref_n(v_localInstances_1702_, 2);
                        lean_dec(v_a_1697_);
                        v___f_1703_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                        lean_closure_set(v___f_1703_, 0, v_names_1685_);
                        lean_inc(v_max_1684_);
                        v___f_1704_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__1___boxed as *mut core::ffi::c_void, 18, 7);
                        lean_closure_set(v___f_1704_, 0, v___x_1693_);
                        lean_closure_set(v___f_1704_, 1, v_userName_1699_);
                        lean_closure_set(v___f_1704_, 2, v_lctx_1700_);
                        lean_closure_set(v___f_1704_, 3, v_localInstances_1702_);
                        lean_closure_set(v___f_1704_, 4, v_type_1701_);
                        lean_closure_set(v___f_1704_, 5, v_max_1684_);
                        lean_closure_set(v___f_1704_, 6, v_mvarId_1683_);
                        v___f_1705_ = lean_alloc_closure(
                            l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___lam__2
                                as *mut core::ffi::c_void,
                            4,
                            1,
                        );
                        lean_closure_set(v___f_1705_, 0, v_env_1698_);
                        v___x_1706_ =
                            l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__0;
                        v___x_1707_ =
                            l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_visit(
                                v_max_1684_,
                                v___f_1704_,
                                v___f_1703_,
                                v___f_1705_,
                                v___x_1693_,
                                v_lctx_1700_,
                                v_localInstances_1702_,
                                v___x_1706_,
                                v_type_1701_,
                                v_a_1686_,
                                v_a_1687_,
                                v_a_1688_,
                                v_a_1689_,
                                v_a_1690_,
                                v_a_1691_,
                            );
                        lean_dec(v_max_1684_);
                        if lean_obj_tag(v___x_1707_) == 0 {
                            v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
                            v_isSharedCheck_1727_ = (!lean_is_exclusive(v___x_1707_)) as u8;
                            if v_isSharedCheck_1727_ == 0 {
                                v___x_1710_ = v___x_1707_;
                                v_isShared_1711_ = v_isSharedCheck_1727_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1708_);
                                lean_dec(v___x_1707_);
                                v___x_1710_ = lean_box(0);
                                v_isShared_1711_ = v_isSharedCheck_1727_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1728_ = lean_ctor_get(v___x_1707_, 0);
                            v_isSharedCheck_1735_ = (!lean_is_exclusive(v___x_1707_)) as u8;
                            if v_isSharedCheck_1735_ == 0 {
                                v___x_1730_ = v___x_1707_;
                                v_isShared_1731_ = v_isSharedCheck_1735_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1728_);
                                lean_dec(v___x_1707_);
                                v___x_1730_ = lean_box(0);
                                v_isShared_1731_ = v_isSharedCheck_1735_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1695_);
                        lean_dec_ref(v_names_1685_);
                        lean_dec(v_max_1684_);
                        lean_dec(v_mvarId_1683_);
                        v_a_1736_ = lean_ctor_get(v___x_1696_, 0);
                        v_isSharedCheck_1743_ = (!lean_is_exclusive(v___x_1696_)) as u8;
                        if v_isSharedCheck_1743_ == 0 {
                            v___x_1738_ = v___x_1696_;
                            v_isShared_1739_ = v_isSharedCheck_1743_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1736_);
                            lean_dec(v___x_1696_);
                            v___x_1738_ = lean_box(0);
                            v_isShared_1739_ = v_isSharedCheck_1743_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_names_1685_);
                    lean_dec(v_max_1684_);
                    v___x_1744_ =
                        l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1;
                    v___x_1745_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1745_, 0, v___x_1744_);
                    lean_ctor_set(v___x_1745_, 1, v_mvarId_1683_);
                    v___x_1746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1746_, 0, v___x_1745_);
                    return v___x_1746_;
                }
            }
            1 => {
                v_fst_1712_ = lean_ctor_get(v_a_1708_, 0);
                v_snd_1713_ = lean_ctor_get(v_a_1708_, 1);
                v_isSharedCheck_1726_ = (!lean_is_exclusive(v_a_1708_)) as u8;
                if v_isSharedCheck_1726_ == 0 {
                    v___x_1715_ = v_a_1708_;
                    v_isShared_1716_ = v_isSharedCheck_1726_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1713_);
                    lean_inc(v_fst_1712_);
                    lean_dec(v_a_1708_);
                    v___x_1715_ = lean_box(0);
                    v_isShared_1716_ = v_isSharedCheck_1726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_1717_ = lean_array_size(v_fst_1712_);
                v___x_1718_ = 0usize;
                v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__2(v_sz_1717_, v___x_1718_, v_fst_1712_);
                if v_isShared_1716_ == 0 {
                    lean_ctor_set(v___x_1715_, 0, v___x_1719_);
                    v___x_1721_ = v___x_1715_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1719_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_snd_1713_);
                    v___x_1721_ = v_reuseFailAlloc_1725_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1711_ == 0 {
                    lean_ctor_set(v___x_1710_, 0, v___x_1721_);
                    v___x_1723_ = v___x_1710_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
                    v___x_1723_ = v_reuseFailAlloc_1724_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1723_;
            }
            5 => {
                if v_isShared_1731_ == 0 {
                    v___x_1733_ = v___x_1730_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1733_;
            }
            7 => {
                if v_isShared_1739_ == 0 {
                    v___x_1741_ = v___x_1738_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
                    v___x_1741_ = v_reuseFailAlloc_1742_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___boxed(
    mut v_mvarId_1747_: *mut LeanObject,
    mut v_max_1748_: *mut LeanObject,
    mut v_names_1749_: *mut LeanObject,
    mut v_a_1750_: *mut LeanObject,
    mut v_a_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
    mut v_a_1753_: *mut LeanObject,
    mut v_a_1754_: *mut LeanObject,
    mut v_a_1755_: *mut LeanObject,
    mut v_a_1756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1757_: *mut LeanObject = core::ptr::null_mut();
    v_res_1757_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(
        v_mvarId_1747_,
        v_max_1748_,
        v_names_1749_,
        v_a_1750_,
        v_a_1751_,
        v_a_1752_,
        v_a_1753_,
        v_a_1754_,
        v_a_1755_,
    );
    lean_dec(v_a_1755_);
    lean_dec_ref(v_a_1754_);
    lean_dec(v_a_1753_);
    lean_dec_ref(v_a_1752_);
    lean_dec(v_a_1751_);
    lean_dec_ref(v_a_1750_);
    return v_res_1757_;
}
pub unsafe fn l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(
    mut v_mvarId_1758_: *mut LeanObject,
    mut v_fvars_1759_: *mut LeanObject,
    mut v_mvarIdPending_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
    mut v___y_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    v___x_1766_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___redArg(v_mvarId_1758_, v_fvars_1759_, v_mvarIdPending_1760_, v___y_1762_);
    return v___x_1766_;
}
pub unsafe fn l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0___boxed(
    mut v_mvarId_1767_: *mut LeanObject,
    mut v_fvars_1768_: *mut LeanObject,
    mut v_mvarIdPending_1769_: *mut LeanObject,
    mut v___y_1770_: *mut LeanObject,
    mut v___y_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1775_: *mut LeanObject = core::ptr::null_mut();
    v_res_1775_ = l_Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0(v_mvarId_1767_, v_fvars_1768_, v_mvarIdPending_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
    lean_dec(v___y_1773_);
    lean_dec_ref(v___y_1772_);
    lean_dec(v___y_1771_);
    lean_dec_ref(v___y_1770_);
    return v_res_1775_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(
    mut v_mvarId_1776_: *mut LeanObject,
    mut v_val_1777_: *mut LeanObject,
    mut v___y_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___redArg(v_mvarId_1776_, v_val_1777_, v___y_1779_);
    return v___x_1783_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1___boxed(
    mut v_mvarId_1784_: *mut LeanObject,
    mut v_val_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1791_: *mut LeanObject = core::ptr::null_mut();
    v_res_1791_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__1(v_mvarId_1784_, v_val_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
    lean_dec(v___y_1789_);
    lean_dec_ref(v___y_1788_);
    lean_dec(v___y_1787_);
    lean_dec_ref(v___y_1786_);
    return v_res_1791_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0(
    mut v_00_u03b2_1792_: *mut LeanObject,
    mut v_x_1793_: *mut LeanObject,
    mut v_x_1794_: *mut LeanObject,
    mut v_x_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0___redArg(v_x_1793_, v_x_1794_, v_x_1795_);
    return v___x_1796_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1797_: *mut LeanObject,
    mut v_x_1798_: *mut LeanObject,
    mut v_x_1799_: usize,
    mut v_x_1800_: usize,
    mut v_x_1801_: *mut LeanObject,
    mut v_x_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    v___x_1803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___redArg(v_x_1798_, v_x_1799_, v_x_1800_, v_x_1801_, v_x_1802_);
    return v___x_1803_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1804_: *mut LeanObject,
    mut v_x_1805_: *mut LeanObject,
    mut v_x_1806_: *mut LeanObject,
    mut v_x_1807_: *mut LeanObject,
    mut v_x_1808_: *mut LeanObject,
    mut v_x_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6500__boxed_1810_: usize = 0;
    let mut v_x_6501__boxed_1811_: usize = 0;
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_x_6500__boxed_1810_ = lean_unbox_usize(v_x_1806_);
    lean_dec(v_x_1806_);
    v_x_6501__boxed_1811_ = lean_unbox_usize(v_x_1807_);
    lean_dec(v_x_1807_);
    v_res_1812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1(v_00_u03b2_1804_, v_x_1805_, v_x_6500__boxed_1810_, v_x_6501__boxed_1811_, v_x_1808_, v_x_1809_);
    return v_res_1812_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_1813_: *mut LeanObject,
    mut v_n_1814_: *mut LeanObject,
    mut v_k_1815_: *mut LeanObject,
    mut v_v_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    v___x_1817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_1814_, v_k_1815_, v_v_1816_);
    return v___x_1817_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b2_1818_: *mut LeanObject,
    mut v_depth_1819_: usize,
    mut v_keys_1820_: *mut LeanObject,
    mut v_vals_1821_: *mut LeanObject,
    mut v_heq_1822_: *mut LeanObject,
    mut v_i_1823_: *mut LeanObject,
    mut v_entries_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_1819_, v_keys_1820_, v_vals_1821_, v_i_1823_, v_entries_1824_);
    return v___x_1825_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b2_1826_: *mut LeanObject,
    mut v_depth_1827_: *mut LeanObject,
    mut v_keys_1828_: *mut LeanObject,
    mut v_vals_1829_: *mut LeanObject,
    mut v_heq_1830_: *mut LeanObject,
    mut v_i_1831_: *mut LeanObject,
    mut v_entries_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1833_: usize = 0;
    let mut v_res_1834_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1833_ = lean_unbox_usize(v_depth_1827_);
    lean_dec(v_depth_1827_);
    v_res_1834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_1826_, v_depth_boxed_1833_, v_keys_1828_, v_vals_1829_, v_heq_1830_, v_i_1831_, v_entries_1832_);
    lean_dec_ref(v_vals_1829_);
    lean_dec_ref(v_keys_1828_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_00_u03b2_1835_: *mut LeanObject,
    mut v_x_1836_: *mut LeanObject,
    mut v_x_1837_: *mut LeanObject,
    mut v_x_1838_: *mut LeanObject,
    mut v_x_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    v___x_1840_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignDelayedMVar___at___00__private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_1836_, v_x_1837_, v_x_1838_, v_x_1839_);
    return v___x_1840_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat() -> *mut LeanObject {
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    v___x_1841_ = lean_unsigned_to_nat(1000000);
    return v___x_1841_;
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_ctorIdx(
    mut v_x_1842_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1842_) == 0 {
        let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
        v___x_1843_ = lean_unsigned_to_nat(0);
        return v___x_1843_;
    } else {
        let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
        v___x_1844_ = lean_unsigned_to_nat(1);
        return v___x_1844_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_ctorIdx___boxed(
    mut v_x_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1846_: *mut LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Lean_Meta_Sym_IntrosResult_ctorIdx(v_x_1845_);
    lean_dec(v_x_1845_);
    return v_res_1846_;
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(
    mut v_t_1847_: *mut LeanObject,
    mut v_k_1848_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1847_) == 0 {
        return v_k_1848_;
    } else {
        let mut v_newDecls_1849_: *mut LeanObject = core::ptr::null_mut();
        let mut v_mvarId_1850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
        v_newDecls_1849_ = lean_ctor_get(v_t_1847_, 0);
        lean_inc_ref(v_newDecls_1849_);
        v_mvarId_1850_ = lean_ctor_get(v_t_1847_, 1);
        lean_inc(v_mvarId_1850_);
        lean_dec_ref_known(v_t_1847_, 2);
        v___x_1851_ = lean_apply_2(v_k_1848_, v_newDecls_1849_, v_mvarId_1850_);
        return v___x_1851_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_ctorElim(
    mut v_motive_1852_: *mut LeanObject,
    mut v_ctorIdx_1853_: *mut LeanObject,
    mut v_t_1854_: *mut LeanObject,
    mut v_h_1855_: *mut LeanObject,
    mut v_k_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    v___x_1857_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1854_, v_k_1856_);
    return v___x_1857_;
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_ctorElim___boxed(
    mut v_motive_1858_: *mut LeanObject,
    mut v_ctorIdx_1859_: *mut LeanObject,
    mut v_t_1860_: *mut LeanObject,
    mut v_h_1861_: *mut LeanObject,
    mut v_k_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1863_: *mut LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_Lean_Meta_Sym_IntrosResult_ctorElim(
        v_motive_1858_,
        v_ctorIdx_1859_,
        v_t_1860_,
        v_h_1861_,
        v_k_1862_,
    );
    lean_dec(v_ctorIdx_1859_);
    return v_res_1863_;
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_failed_elim___redArg(
    mut v_t_1864_: *mut LeanObject,
    mut v_failed_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1864_, v_failed_1865_);
    return v___x_1866_;
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_failed_elim(
    mut v_motive_1867_: *mut LeanObject,
    mut v_t_1868_: *mut LeanObject,
    mut v_h_1869_: *mut LeanObject,
    mut v_failed_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    v___x_1871_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1868_, v_failed_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_goal_elim___redArg(
    mut v_t_1872_: *mut LeanObject,
    mut v_goal_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1872_, v_goal_1873_);
    return v___x_1874_;
}
pub unsafe fn l_Lean_Meta_Sym_IntrosResult_goal_elim(
    mut v_motive_1875_: *mut LeanObject,
    mut v_t_1876_: *mut LeanObject,
    mut v_h_1877_: *mut LeanObject,
    mut v_goal_1878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    v___x_1879_ = l_Lean_Meta_Sym_IntrosResult_ctorElim___redArg(v_t_1876_, v_goal_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lean_Meta_Sym_intros(
    mut v_mvarId_1880_: *mut LeanObject,
    mut v_names_1881_: *mut LeanObject,
    mut v_a_1882_: *mut LeanObject,
    mut v_a_1883_: *mut LeanObject,
    mut v_a_1884_: *mut LeanObject,
    mut v_a_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_result_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u8 = 0;
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1906_ = lean_array_get_size(v_names_1881_);
                v___x_1907_ = lean_unsigned_to_nat(0);
                v___x_1908_ = lean_nat_dec_eq(v___x_1906_, v___x_1907_);
                if v___x_1908_ == 0 {
                    v___x_1909_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(
                        v_mvarId_1880_,
                        v___x_1906_,
                        v_names_1881_,
                        v_a_1882_,
                        v_a_1883_,
                        v_a_1884_,
                        v_a_1885_,
                        v_a_1886_,
                        v_a_1887_,
                    );
                    if lean_obj_tag(v___x_1909_) == 0 {
                        v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
                        lean_inc(v_a_1910_);
                        lean_dec_ref_known(v___x_1909_, 1);
                        v_result_1890_ = v_a_1910_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1911_ = lean_ctor_get(v___x_1909_, 0);
                        v_isSharedCheck_1918_ = (!lean_is_exclusive(v___x_1909_)) as u8;
                        if v_isSharedCheck_1918_ == 0 {
                            v___x_1913_ = v___x_1909_;
                            v_isShared_1914_ = v_isSharedCheck_1918_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1911_);
                            lean_dec(v___x_1909_);
                            v___x_1913_ = lean_box(0);
                            v_isShared_1914_ = v_isSharedCheck_1918_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_names_1881_);
                    v___x_1919_ = lean_unsigned_to_nat(1000000);
                    v___x_1920_ =
                        l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1;
                    v___x_1921_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(
                        v_mvarId_1880_,
                        v___x_1919_,
                        v___x_1920_,
                        v_a_1882_,
                        v_a_1883_,
                        v_a_1884_,
                        v_a_1885_,
                        v_a_1886_,
                        v_a_1887_,
                    );
                    if lean_obj_tag(v___x_1921_) == 0 {
                        v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
                        lean_inc(v_a_1922_);
                        lean_dec_ref_known(v___x_1921_, 1);
                        v_result_1890_ = v_a_1922_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1923_ = lean_ctor_get(v___x_1921_, 0);
                        v_isSharedCheck_1930_ = (!lean_is_exclusive(v___x_1921_)) as u8;
                        if v_isSharedCheck_1930_ == 0 {
                            v___x_1925_ = v___x_1921_;
                            v_isShared_1926_ = v_isSharedCheck_1930_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1923_);
                            lean_dec(v___x_1921_);
                            v___x_1925_ = lean_box(0);
                            v_isShared_1926_ = v_isSharedCheck_1930_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1891_ = lean_ctor_get(v_result_1890_, 0);
                v_snd_1892_ = lean_ctor_get(v_result_1890_, 1);
                v_isSharedCheck_1905_ = (!lean_is_exclusive(v_result_1890_)) as u8;
                if v_isSharedCheck_1905_ == 0 {
                    v___x_1894_ = v_result_1890_;
                    v_isShared_1895_ = v_isSharedCheck_1905_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1892_);
                    lean_inc(v_fst_1891_);
                    lean_dec(v_result_1890_);
                    v___x_1894_ = lean_box(0);
                    v_isShared_1895_ = v_isSharedCheck_1905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1896_ = lean_array_get_size(v_fst_1891_);
                v___x_1897_ = lean_unsigned_to_nat(0);
                v___x_1898_ = lean_nat_dec_eq(v___x_1896_, v___x_1897_);
                if v___x_1898_ == 0 {
                    if v_isShared_1895_ == 0 {
                        lean_ctor_set_tag(v___x_1894_, 1);
                        v___x_1900_ = v___x_1894_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_fst_1891_);
                        lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_snd_1892_);
                        v___x_1900_ = v_reuseFailAlloc_1902_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1894_);
                    lean_dec(v_snd_1892_);
                    lean_dec(v_fst_1891_);
                    v___x_1903_ = lean_box(0);
                    v___x_1904_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1904_, 0, v___x_1903_);
                    return v___x_1904_;
                }
            }
            3 => {
                v___x_1901_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1901_, 0, v___x_1900_);
                return v___x_1901_;
            }
            4 => {
                if v_isShared_1914_ == 0 {
                    v___x_1916_ = v___x_1913_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1916_;
            }
            6 => {
                if v_isShared_1926_ == 0 {
                    v___x_1928_ = v___x_1925_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
                    v___x_1928_ = v_reuseFailAlloc_1929_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_intros___boxed(
    mut v_mvarId_1931_: *mut LeanObject,
    mut v_names_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
    mut v_a_1934_: *mut LeanObject,
    mut v_a_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
    mut v_a_1938_: *mut LeanObject,
    mut v_a_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1940_: *mut LeanObject = core::ptr::null_mut();
    v_res_1940_ = l_Lean_Meta_Sym_intros(
        v_mvarId_1931_,
        v_names_1932_,
        v_a_1933_,
        v_a_1934_,
        v_a_1935_,
        v_a_1936_,
        v_a_1937_,
        v_a_1938_,
    );
    lean_dec(v_a_1938_);
    lean_dec_ref(v_a_1937_);
    lean_dec(v_a_1936_);
    lean_dec_ref(v_a_1935_);
    lean_dec(v_a_1934_);
    lean_dec_ref(v_a_1933_);
    return v_res_1940_;
}
pub unsafe fn l_Lean_Meta_Sym_introN(
    mut v_mvarId_1941_: *mut LeanObject,
    mut v_num_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
    mut v_a_1944_: *mut LeanObject,
    mut v_a_1945_: *mut LeanObject,
    mut v_a_1946_: *mut LeanObject,
    mut v_a_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1955_: u8 = 0;
    let mut v_fst_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1960_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v_a_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1950_ =
                    l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore___closed__1;
                lean_inc(v_num_1942_);
                v___x_1951_ = l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_introCore(
                    v_mvarId_1941_,
                    v_num_1942_,
                    v___x_1950_,
                    v_a_1943_,
                    v_a_1944_,
                    v_a_1945_,
                    v_a_1946_,
                    v_a_1947_,
                    v_a_1948_,
                );
                if lean_obj_tag(v___x_1951_) == 0 {
                    v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
                    v_isSharedCheck_1974_ = (!lean_is_exclusive(v___x_1951_)) as u8;
                    if v_isSharedCheck_1974_ == 0 {
                        v___x_1954_ = v___x_1951_;
                        v_isShared_1955_ = v_isSharedCheck_1974_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1952_);
                        lean_dec(v___x_1951_);
                        v___x_1954_ = lean_box(0);
                        v_isShared_1955_ = v_isSharedCheck_1974_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_num_1942_);
                    v_a_1975_ = lean_ctor_get(v___x_1951_, 0);
                    v_isSharedCheck_1982_ = (!lean_is_exclusive(v___x_1951_)) as u8;
                    if v_isSharedCheck_1982_ == 0 {
                        v___x_1977_ = v___x_1951_;
                        v_isShared_1978_ = v_isSharedCheck_1982_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1975_);
                        lean_dec(v___x_1951_);
                        v___x_1977_ = lean_box(0);
                        v_isShared_1978_ = v_isSharedCheck_1982_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1956_ = lean_ctor_get(v_a_1952_, 0);
                v_snd_1957_ = lean_ctor_get(v_a_1952_, 1);
                v_isSharedCheck_1973_ = (!lean_is_exclusive(v_a_1952_)) as u8;
                if v_isSharedCheck_1973_ == 0 {
                    v___x_1959_ = v_a_1952_;
                    v_isShared_1960_ = v_isSharedCheck_1973_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1957_);
                    lean_inc(v_fst_1956_);
                    lean_dec(v_a_1952_);
                    v___x_1959_ = lean_box(0);
                    v_isShared_1960_ = v_isSharedCheck_1973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1961_ = lean_array_get_size(v_fst_1956_);
                v___x_1962_ = lean_nat_dec_eq(v___x_1961_, v_num_1942_);
                lean_dec(v_num_1942_);
                if v___x_1962_ == 0 {
                    lean_del_object(v___x_1959_);
                    lean_dec(v_snd_1957_);
                    lean_dec(v_fst_1956_);
                    v___x_1963_ = lean_box(0);
                    if v_isShared_1955_ == 0 {
                        lean_ctor_set(v___x_1954_, 0, v___x_1963_);
                        v___x_1965_ = v___x_1954_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
                        v___x_1965_ = v_reuseFailAlloc_1966_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1960_ == 0 {
                        lean_ctor_set_tag(v___x_1959_, 1);
                        v___x_1968_ = v___x_1959_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_fst_1956_);
                        lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_snd_1957_);
                        v___x_1968_ = v_reuseFailAlloc_1972_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1965_;
            }
            4 => {
                if v_isShared_1955_ == 0 {
                    lean_ctor_set(v___x_1954_, 0, v___x_1968_);
                    v___x_1970_ = v___x_1954_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
                    v___x_1970_ = v_reuseFailAlloc_1971_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1970_;
            }
            6 => {
                if v_isShared_1978_ == 0 {
                    v___x_1980_ = v___x_1977_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
                    v___x_1980_ = v_reuseFailAlloc_1981_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_introN___boxed(
    mut v_mvarId_1983_: *mut LeanObject,
    mut v_num_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
    mut v_a_1986_: *mut LeanObject,
    mut v_a_1987_: *mut LeanObject,
    mut v_a_1988_: *mut LeanObject,
    mut v_a_1989_: *mut LeanObject,
    mut v_a_1990_: *mut LeanObject,
    mut v_a_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1992_: *mut LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Lean_Meta_Sym_introN(
        v_mvarId_1983_,
        v_num_1984_,
        v_a_1985_,
        v_a_1986_,
        v_a_1987_,
        v_a_1988_,
        v_a_1989_,
        v_a_1990_,
    );
    lean_dec(v_a_1990_);
    lean_dec_ref(v_a_1989_);
    lean_dec(v_a_1988_);
    lean_dec_ref(v_a_1987_);
    lean_dec(v_a_1986_);
    lean_dec_ref(v_a_1985_);
    return v_res_1992_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Intro(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat =
        _init_l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat();
    lean_mark_persistent(l___private_Lean_Meta_Sym_Intro_0__Lean_Meta_Sym_hugeNat);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Intro(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Intro(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_IsClass(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Intro(builtin);
}
