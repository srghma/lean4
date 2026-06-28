// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Rewrite
// Imports: Lean.Meta.Sym.Simp.Simproc Lean.Meta.Sym.Simp.Theorems Lean.Meta.Sym.Simp.App Lean.Meta.Sym.Simp.Discharger Lean.Meta.ACLt Lean.Meta.Sym.InstantiateS Lean.Meta.Sym.InstantiateMVarsS Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkAppN,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::ACLt::{
    initialize_Lean_Meta_ACLt, l_Lean_Meta_acLt, runtime_initialize_Lean_Meta_ACLt,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_MVarId_getDecl,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::InstantiateMVarsS::{
    initialize_Lean_Meta_Sym_InstantiateMVarsS, l_Lean_Meta_Sym_instantiateMVarsS,
    runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateS::{
    initialize_Lean_Meta_Sym_InstantiateS, l_Lean_Meta_Sym_instantiateRevBetaS___redArg,
    runtime_initialize_Lean_Meta_Sym_InstantiateS,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::l_Lean_Meta_Sym_Pattern_match_x3f;
use crate::r#gen::Lean::Meta::Sym::Simp::App::{
    initialize_Lean_Meta_Sym_Simp_App, l_Lean_Meta_Sym_Simp_simpOverApplied,
    runtime_initialize_Lean_Meta_Sym_Simp_App,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Discharger::{
    initialize_Lean_Meta_Sym_Simp_Discharger, runtime_initialize_Lean_Meta_Sym_Simp_Discharger,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    l_Lean_Meta_Sym_Simp_Result_withContextDependent, l_Lean_Meta_Sym_Simp_mkRflResultCD,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Simproc::{
    initialize_Lean_Meta_Sym_Simp_Simproc, runtime_initialize_Lean_Meta_Sym_Simp_Simproc,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Theorems::{
    initialize_Lean_Meta_Sym_Simp_Theorems, l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra,
    runtime_initialize_Lean_Meta_Sym_Simp_Theorems,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommonInc___redArg;
use crate::r#gen::Lean::Util::InstantiateLevelParams::l_Lean_Expr_instantiateLevelParams;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::MetavarContext::lean_instantiate_level_mvars;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_10,
    lean_apply_11, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [0 as *mut LeanObject],
    };
static mut l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(
    mut v_expr_1235_: *mut LeanObject,
    mut v_pattern_1236_: *mut LeanObject,
    mut v_us_1237_: *mut LeanObject,
    mut v_args_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_levelParams_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_expr_1235_) == 4 {
                    v_us_1243_ = lean_ctor_get(v_expr_1235_, 1);
                    if lean_obj_tag(v_us_1243_) == 0 {
                        lean_dec_ref(v_pattern_1236_);
                        v_declName_1244_ = lean_ctor_get(v_expr_1235_, 0);
                        lean_inc(v_declName_1244_);
                        lean_dec_ref_known(v_expr_1235_, 2);
                        v___x_1245_ = l_Lean_mkConst(v_declName_1244_, v_us_1237_);
                        v___x_1246_ = l_Lean_mkAppN(v___x_1245_, v_args_1238_);
                        return v___x_1246_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_levelParams_1240_ = lean_ctor_get(v_pattern_1236_, 0);
                lean_inc(v_levelParams_1240_);
                lean_dec_ref(v_pattern_1236_);
                v___x_1241_ = l_Lean_Expr_instantiateLevelParams(
                    v_expr_1235_,
                    v_levelParams_1240_,
                    v_us_1237_,
                );
                lean_dec_ref(v_expr_1235_);
                v___x_1242_ = l_Lean_mkAppN(v___x_1241_, v_args_1238_);
                return v___x_1242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue___boxed(
    mut v_expr_1247_: *mut LeanObject,
    mut v_pattern_1248_: *mut LeanObject,
    mut v_us_1249_: *mut LeanObject,
    mut v_args_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: *mut LeanObject = core::ptr::null_mut();
    v_res_1251_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(
        v_expr_1247_,
        v_pattern_1248_,
        v_us_1249_,
        v_args_1250_,
    );
    lean_dec_ref(v_args_1250_);
    return v_res_1251_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(
    mut v_perm_1252_: u8,
    mut v_e_1253_: *mut LeanObject,
    mut v_result_1254_: *mut LeanObject,
    mut v_a_1255_: *mut LeanObject,
    mut v_a_1256_: *mut LeanObject,
    mut v_a_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
) -> *mut LeanObject {
    if v_perm_1252_ == 0 {
        let mut v___x_1260_: u8 = 0;
        let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_result_1254_);
        lean_dec_ref(v_e_1253_);
        v___x_1260_ = 1;
        v___x_1261_ = lean_box((v___x_1260_) as usize);
        v___x_1262_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1262_, 0, v___x_1261_);
        return v___x_1262_;
    } else {
        let mut v___x_1263_: u8 = 0;
        let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
        v___x_1263_ = 2;
        v___x_1264_ = l_Lean_Meta_acLt(
            v_result_1254_,
            v_e_1253_,
            v___x_1263_,
            v_a_1255_,
            v_a_1256_,
            v_a_1257_,
            v_a_1258_,
        );
        return v___x_1264_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm___boxed(
    mut v_perm_1265_: *mut LeanObject,
    mut v_e_1266_: *mut LeanObject,
    mut v_result_1267_: *mut LeanObject,
    mut v_a_1268_: *mut LeanObject,
    mut v_a_1269_: *mut LeanObject,
    mut v_a_1270_: *mut LeanObject,
    mut v_a_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_perm_boxed_1273_: u8 = 0;
    let mut v_res_1274_: *mut LeanObject = core::ptr::null_mut();
    v_perm_boxed_1273_ = (lean_unbox(v_perm_1265_) as u8);
    v_res_1274_ =
        l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(
            v_perm_boxed_1273_,
            v_e_1266_,
            v_result_1267_,
            v_a_1268_,
            v_a_1269_,
            v_a_1270_,
            v_a_1271_,
        );
    lean_dec(v_a_1271_);
    lean_dec_ref(v_a_1270_);
    lean_dec(v_a_1269_);
    lean_dec_ref(v_a_1268_);
    return v_res_1274_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(
    mut v_l_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v_unused_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1278_ = lean_st_ref_get(v___y_1276_);
                v_mctx_1279_ = lean_ctor_get(v___x_1278_, 0);
                lean_inc_ref(v_mctx_1279_);
                lean_dec(v___x_1278_);
                v___x_1280_ = lean_instantiate_level_mvars(v_mctx_1279_, v_l_1275_);
                v_fst_1281_ = lean_ctor_get(v___x_1280_, 0);
                lean_inc(v_fst_1281_);
                v_snd_1282_ = lean_ctor_get(v___x_1280_, 1);
                lean_inc(v_snd_1282_);
                lean_dec_ref(v___x_1280_);
                v___x_1283_ = lean_st_ref_take(v___y_1276_);
                v_cache_1284_ = lean_ctor_get(v___x_1283_, 1);
                v_zetaDeltaFVarIds_1285_ = lean_ctor_get(v___x_1283_, 2);
                v_postponed_1286_ = lean_ctor_get(v___x_1283_, 3);
                v_diag_1287_ = lean_ctor_get(v___x_1283_, 4);
                v_isSharedCheck_1296_ = (!lean_is_exclusive(v___x_1283_)) as u8;
                if v_isSharedCheck_1296_ == 0 {
                    v_unused_1297_ = lean_ctor_get(v___x_1283_, 0);
                    lean_dec(v_unused_1297_);
                    v___x_1289_ = v___x_1283_;
                    v_isShared_1290_ = v_isSharedCheck_1296_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1287_);
                    lean_inc(v_postponed_1286_);
                    lean_inc(v_zetaDeltaFVarIds_1285_);
                    lean_inc(v_cache_1284_);
                    lean_dec(v___x_1283_);
                    v___x_1289_ = lean_box(0);
                    v_isShared_1290_ = v_isSharedCheck_1296_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 0, v_fst_1281_);
                    v___x_1292_ = v___x_1289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_fst_1281_);
                    lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_cache_1284_);
                    lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_zetaDeltaFVarIds_1285_);
                    lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_postponed_1286_);
                    lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_diag_1287_);
                    v___x_1292_ = v_reuseFailAlloc_1295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1293_ = lean_st_ref_set(v___y_1276_, v___x_1292_);
                v___x_1294_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1294_, 0, v_snd_1282_);
                return v___x_1294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg___boxed(
    mut v_l_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1301_: *mut LeanObject = core::ptr::null_mut();
    v_res_1301_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(
            v_l_1298_,
            v___y_1299_,
        );
    lean_dec(v___y_1299_);
    return v_res_1301_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(
    mut v_l_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
    mut v___y_1308_: *mut LeanObject,
    mut v___y_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    v___x_1313_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(
            v_l_1302_,
            v___y_1309_,
        );
    return v___x_1313_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___boxed(
    mut v_l_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1325_: *mut LeanObject = core::ptr::null_mut();
    v_res_1325_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(
        v_l_1314_,
        v___y_1315_,
        v___y_1316_,
        v___y_1317_,
        v___y_1318_,
        v___y_1319_,
        v___y_1320_,
        v___y_1321_,
        v___y_1322_,
        v___y_1323_,
    );
    lean_dec(v___y_1323_);
    lean_dec_ref(v___y_1322_);
    lean_dec(v___y_1321_);
    lean_dec_ref(v___y_1320_);
    lean_dec(v___y_1319_);
    lean_dec_ref(v___y_1318_);
    lean_dec(v___y_1317_);
    lean_dec_ref(v___y_1316_);
    lean_dec(v___y_1315_);
    return v_res_1325_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(
    mut v_k_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
    mut v___y_1330_: *mut LeanObject,
    mut v___y_1331_: *mut LeanObject,
    mut v___y_1332_: *mut LeanObject,
    mut v___y_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1331_);
    lean_inc_ref(v___y_1330_);
    lean_inc(v___y_1329_);
    lean_inc_ref(v___y_1328_);
    lean_inc(v___y_1327_);
    v___x_1337_ = lean_apply_10(
        v_k_1326_,
        v___y_1327_,
        v___y_1328_,
        v___y_1329_,
        v___y_1330_,
        v___y_1331_,
        v___y_1332_,
        v___y_1333_,
        v___y_1334_,
        v___y_1335_,
        lean_box(0),
    );
    return v___x_1337_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(
    mut v_k_1338_: *mut LeanObject,
    mut v___y_1339_: *mut LeanObject,
    mut v___y_1340_: *mut LeanObject,
    mut v___y_1341_: *mut LeanObject,
    mut v___y_1342_: *mut LeanObject,
    mut v___y_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
    mut v___y_1345_: *mut LeanObject,
    mut v___y_1346_: *mut LeanObject,
    mut v___y_1347_: *mut LeanObject,
    mut v___y_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1349_: *mut LeanObject = core::ptr::null_mut();
    v_res_1349_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_k_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
    lean_dec(v___y_1343_);
    lean_dec_ref(v___y_1342_);
    lean_dec(v___y_1341_);
    lean_dec_ref(v___y_1340_);
    lean_dec(v___y_1339_);
    return v_res_1349_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(
    mut v_k_1350_: *mut LeanObject,
    mut v_allowLevelAssignments_1351_: u8,
    mut v___y_1352_: *mut LeanObject,
    mut v___y_1353_: *mut LeanObject,
    mut v___y_1354_: *mut LeanObject,
    mut v___y_1355_: *mut LeanObject,
    mut v___y_1356_: *mut LeanObject,
    mut v___y_1357_: *mut LeanObject,
    mut v___y_1358_: *mut LeanObject,
    mut v___y_1359_: *mut LeanObject,
    mut v___y_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1356_);
                lean_inc_ref(v___y_1355_);
                lean_inc(v___y_1354_);
                lean_inc_ref(v___y_1353_);
                lean_inc(v___y_1352_);
                v___f_1362_ = lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                lean_closure_set(v___f_1362_, 0, v_k_1350_);
                lean_closure_set(v___f_1362_, 1, v___y_1352_);
                lean_closure_set(v___f_1362_, 2, v___y_1353_);
                lean_closure_set(v___f_1362_, 3, v___y_1354_);
                lean_closure_set(v___f_1362_, 4, v___y_1355_);
                lean_closure_set(v___f_1362_, 5, v___y_1356_);
                v___x_1363_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_1351_,
                    v___f_1362_,
                    v___y_1357_,
                    v___y_1358_,
                    v___y_1359_,
                    v___y_1360_,
                );
                if lean_obj_tag(v___x_1363_) == 0 {
                    return v___x_1363_;
                } else {
                    v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
                    v_isSharedCheck_1371_ = (!lean_is_exclusive(v___x_1363_)) as u8;
                    if v_isSharedCheck_1371_ == 0 {
                        v___x_1366_ = v___x_1363_;
                        v_isShared_1367_ = v_isSharedCheck_1371_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1364_);
                        lean_dec(v___x_1363_);
                        v___x_1366_ = lean_box(0);
                        v_isShared_1367_ = v_isSharedCheck_1371_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1367_ == 0 {
                    v___x_1369_ = v___x_1366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
                    v___x_1369_ = v_reuseFailAlloc_1370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(
    mut v_k_1372_: *mut LeanObject,
    mut v_allowLevelAssignments_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
    mut v___y_1375_: *mut LeanObject,
    mut v___y_1376_: *mut LeanObject,
    mut v___y_1377_: *mut LeanObject,
    mut v___y_1378_: *mut LeanObject,
    mut v___y_1379_: *mut LeanObject,
    mut v___y_1380_: *mut LeanObject,
    mut v___y_1381_: *mut LeanObject,
    mut v___y_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_1384_: u8 = 0;
    let mut v_res_1385_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1384_ = (lean_unbox(v_allowLevelAssignments_1373_) as u8);
    v_res_1385_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(
            v_k_1372_,
            v_allowLevelAssignments_boxed_1384_,
            v___y_1374_,
            v___y_1375_,
            v___y_1376_,
            v___y_1377_,
            v___y_1378_,
            v___y_1379_,
            v___y_1380_,
            v___y_1381_,
            v___y_1382_,
        );
    lean_dec(v___y_1382_);
    lean_dec_ref(v___y_1381_);
    lean_dec(v___y_1380_);
    lean_dec_ref(v___y_1379_);
    lean_dec(v___y_1378_);
    lean_dec_ref(v___y_1377_);
    lean_dec(v___y_1376_);
    lean_dec_ref(v___y_1375_);
    lean_dec(v___y_1374_);
    return v_res_1385_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(
    mut v_00_u03b1_1386_: *mut LeanObject,
    mut v_k_1387_: *mut LeanObject,
    mut v_allowLevelAssignments_1388_: u8,
    mut v___y_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
    mut v___y_1394_: *mut LeanObject,
    mut v___y_1395_: *mut LeanObject,
    mut v___y_1396_: *mut LeanObject,
    mut v___y_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(
            v_k_1387_,
            v_allowLevelAssignments_1388_,
            v___y_1389_,
            v___y_1390_,
            v___y_1391_,
            v___y_1392_,
            v___y_1393_,
            v___y_1394_,
            v___y_1395_,
            v___y_1396_,
            v___y_1397_,
        );
    return v___x_1399_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(
    mut v_00_u03b1_1400_: *mut LeanObject,
    mut v_k_1401_: *mut LeanObject,
    mut v_allowLevelAssignments_1402_: *mut LeanObject,
    mut v___y_1403_: *mut LeanObject,
    mut v___y_1404_: *mut LeanObject,
    mut v___y_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
    mut v___y_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_1413_: u8 = 0;
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1413_ = (lean_unbox(v_allowLevelAssignments_1402_) as u8);
    v_res_1414_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(
        v_00_u03b1_1400_,
        v_k_1401_,
        v_allowLevelAssignments_boxed_1413_,
        v___y_1403_,
        v___y_1404_,
        v___y_1405_,
        v___y_1406_,
        v___y_1407_,
        v___y_1408_,
        v___y_1409_,
        v___y_1410_,
        v___y_1411_,
    );
    lean_dec(v___y_1411_);
    lean_dec_ref(v___y_1410_);
    lean_dec(v___y_1409_);
    lean_dec_ref(v___y_1408_);
    lean_dec(v___y_1407_);
    lean_dec_ref(v___y_1406_);
    lean_dec(v___y_1405_);
    lean_dec_ref(v___y_1404_);
    lean_dec(v___y_1403_);
    return v_res_1414_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(
    mut v_x_1415_: *mut LeanObject,
    mut v_x_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
    mut v___y_1422_: *mut LeanObject,
    mut v___y_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1415_) == 0 {
                    v___x_1427_ = l_List_reverse___redArg(v_x_1416_);
                    v___x_1428_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1428_, 0, v___x_1427_);
                    return v___x_1428_;
                } else {
                    v_head_1429_ = lean_ctor_get(v_x_1415_, 0);
                    v_tail_1430_ = lean_ctor_get(v_x_1415_, 1);
                    v_isSharedCheck_1440_ = (!lean_is_exclusive(v_x_1415_)) as u8;
                    if v_isSharedCheck_1440_ == 0 {
                        v___x_1432_ = v_x_1415_;
                        v_isShared_1433_ = v_isSharedCheck_1440_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1430_);
                        lean_inc(v_head_1429_);
                        lean_dec(v_x_1415_);
                        v___x_1432_ = lean_box(0);
                        v_isShared_1433_ = v_isSharedCheck_1440_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1434_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_1429_, v___y_1423_);
                v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
                lean_inc(v_a_1435_);
                lean_dec_ref(v___x_1434_);
                if v_isShared_1433_ == 0 {
                    lean_ctor_set(v___x_1432_, 1, v_x_1416_);
                    lean_ctor_set(v___x_1432_, 0, v_a_1435_);
                    v___x_1437_ = v___x_1432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1435_);
                    lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_x_1416_);
                    v___x_1437_ = v_reuseFailAlloc_1439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_1415_ = v_tail_1430_;
                v_x_1416_ = v___x_1437_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(
    mut v_x_1441_: *mut LeanObject,
    mut v_x_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
    mut v___y_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
    mut v___y_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1453_: *mut LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(
        v_x_1441_,
        v_x_1442_,
        v___y_1443_,
        v___y_1444_,
        v___y_1445_,
        v___y_1446_,
        v___y_1447_,
        v___y_1448_,
        v___y_1449_,
        v___y_1450_,
        v___y_1451_,
    );
    lean_dec(v___y_1451_);
    lean_dec_ref(v___y_1450_);
    lean_dec(v___y_1449_);
    lean_dec_ref(v___y_1448_);
    lean_dec(v___y_1447_);
    lean_dec_ref(v___y_1446_);
    lean_dec(v___y_1445_);
    lean_dec_ref(v___y_1444_);
    lean_dec(v___y_1443_);
    return v_res_1453_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(
    mut v_x_1454_: *mut LeanObject,
    mut v_x_1455_: *mut LeanObject,
    mut v_x_1456_: *mut LeanObject,
    mut v_x_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1462_: u8 = 0;
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1458_ = lean_ctor_get(v_x_1454_, 0);
                v_vs_1459_ = lean_ctor_get(v_x_1454_, 1);
                v_isSharedCheck_1483_ = (!lean_is_exclusive(v_x_1454_)) as u8;
                if v_isSharedCheck_1483_ == 0 {
                    v___x_1461_ = v_x_1454_;
                    v_isShared_1462_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1459_);
                    lean_inc(v_ks_1458_);
                    lean_dec(v_x_1454_);
                    v___x_1461_ = lean_box(0);
                    v_isShared_1462_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1463_ = lean_array_get_size(v_ks_1458_);
                v___x_1464_ = lean_nat_dec_lt(v_x_1455_, v___x_1463_);
                if v___x_1464_ == 0 {
                    lean_dec(v_x_1455_);
                    v___x_1465_ = lean_array_push(v_ks_1458_, v_x_1456_);
                    v___x_1466_ = lean_array_push(v_vs_1459_, v_x_1457_);
                    if v_isShared_1462_ == 0 {
                        lean_ctor_set(v___x_1461_, 1, v___x_1466_);
                        lean_ctor_set(v___x_1461_, 0, v___x_1465_);
                        v___x_1468_ = v___x_1461_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1465_);
                        lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1466_);
                        v___x_1468_ = v_reuseFailAlloc_1469_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1470_ = lean_array_fget_borrowed(v_ks_1458_, v_x_1455_);
                    v___x_1471_ = l_Lean_instBEqMVarId_beq(v_x_1456_, v_k_x27_1470_);
                    if v___x_1471_ == 0 {
                        if v_isShared_1462_ == 0 {
                            v___x_1473_ = v___x_1461_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_ks_1458_);
                            lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_vs_1459_);
                            v___x_1473_ = v_reuseFailAlloc_1477_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1478_ = lean_array_fset(v_ks_1458_, v_x_1455_, v_x_1456_);
                        v___x_1479_ = lean_array_fset(v_vs_1459_, v_x_1455_, v_x_1457_);
                        lean_dec(v_x_1455_);
                        if v_isShared_1462_ == 0 {
                            lean_ctor_set(v___x_1461_, 1, v___x_1479_);
                            lean_ctor_set(v___x_1461_, 0, v___x_1478_);
                            v___x_1481_ = v___x_1461_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1478_);
                            lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1479_);
                            v___x_1481_ = v_reuseFailAlloc_1482_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1468_;
            }
            3 => {
                v___x_1474_ = lean_unsigned_to_nat(1);
                v___x_1475_ = lean_nat_add(v_x_1455_, v___x_1474_);
                lean_dec(v_x_1455_);
                v_x_1454_ = v___x_1473_;
                v_x_1455_ = v___x_1475_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(
    mut v_n_1484_: *mut LeanObject,
    mut v_k_1485_: *mut LeanObject,
    mut v_v_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    v___x_1487_ = lean_unsigned_to_nat(0);
    v___x_1488_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_n_1484_, v___x_1487_, v_k_1485_, v_v_1486_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0()
-> usize {
    let mut v___x_1489_: usize = 0;
    let mut v___x_1490_: usize = 0;
    let mut v___x_1491_: usize = 0;
    v___x_1489_ = 5usize;
    v___x_1490_ = 1usize;
    v___x_1491_ = lean_usize_shift_left(v___x_1490_, v___x_1489_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1()
-> usize {
    let mut v___x_1492_: usize = 0;
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    v___x_1492_ = 1usize;
    v___x_1493_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0);
    v___x_1494_ = lean_usize_sub(v___x_1493_, v___x_1492_);
    return v___x_1494_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1495_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(
    mut v_x_1496_: *mut LeanObject,
    mut v_x_1497_: usize,
    mut v_x_1498_: usize,
    mut v_x_1499_: *mut LeanObject,
    mut v_x_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: usize = 0;
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: usize = 0;
    let mut v___x_1505_: usize = 0;
    let mut v_j_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v_v_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1532_: u8 = 0;
    let mut v_node_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: usize = 0;
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v_unused_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: u8 = 0;
    let mut v_ks_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: usize = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: u8 = 0;
    let mut v_reuseFailAlloc_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1496_) == 0 {
                    v_es_1501_ = lean_ctor_get(v_x_1496_, 0);
                    v___x_1502_ = 5usize;
                    v___x_1503_ = 1usize;
                    v___x_1504_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1);
                    v___x_1505_ = lean_usize_land(v_x_1497_, v___x_1504_);
                    v_j_1506_ = lean_usize_to_nat(v___x_1505_);
                    v___x_1507_ = lean_array_get_size(v_es_1501_);
                    v___x_1508_ = lean_nat_dec_lt(v_j_1506_, v___x_1507_);
                    if v___x_1508_ == 0 {
                        lean_dec(v_j_1506_);
                        lean_dec(v_x_1500_);
                        lean_dec(v_x_1499_);
                        return v_x_1496_;
                    } else {
                        lean_inc_ref(v_es_1501_);
                        v_isSharedCheck_1545_ = (!lean_is_exclusive(v_x_1496_)) as u8;
                        if v_isSharedCheck_1545_ == 0 {
                            v_unused_1546_ = lean_ctor_get(v_x_1496_, 0);
                            lean_dec(v_unused_1546_);
                            v___x_1510_ = v_x_1496_;
                            v_isShared_1511_ = v_isSharedCheck_1545_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1496_);
                            v___x_1510_ = lean_box(0);
                            v_isShared_1511_ = v_isSharedCheck_1545_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1547_ = lean_ctor_get(v_x_1496_, 0);
                    v_vs_1548_ = lean_ctor_get(v_x_1496_, 1);
                    v_isSharedCheck_1568_ = (!lean_is_exclusive(v_x_1496_)) as u8;
                    if v_isSharedCheck_1568_ == 0 {
                        v___x_1550_ = v_x_1496_;
                        v_isShared_1551_ = v_isSharedCheck_1568_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1548_);
                        lean_inc(v_ks_1547_);
                        lean_dec(v_x_1496_);
                        v___x_1550_ = lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1568_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1512_ = lean_array_fget(v_es_1501_, v_j_1506_);
                v___x_1513_ = lean_box(0);
                v_xs_x27_1514_ = lean_array_fset(v_es_1501_, v_j_1506_, v___x_1513_);
                match lean_obj_tag(v_v_1512_) {
                    0 => {
                        v_key_1521_ = lean_ctor_get(v_v_1512_, 0);
                        v_val_1522_ = lean_ctor_get(v_v_1512_, 1);
                        v_isSharedCheck_1532_ = (!lean_is_exclusive(v_v_1512_)) as u8;
                        if v_isSharedCheck_1532_ == 0 {
                            v___x_1524_ = v_v_1512_;
                            v_isShared_1525_ = v_isSharedCheck_1532_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1522_);
                            lean_inc(v_key_1521_);
                            lean_dec(v_v_1512_);
                            v___x_1524_ = lean_box(0);
                            v_isShared_1525_ = v_isSharedCheck_1532_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1533_ = lean_ctor_get(v_v_1512_, 0);
                        v_isSharedCheck_1543_ = (!lean_is_exclusive(v_v_1512_)) as u8;
                        if v_isSharedCheck_1543_ == 0 {
                            v___x_1535_ = v_v_1512_;
                            v_isShared_1536_ = v_isSharedCheck_1543_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1533_);
                            lean_dec(v_v_1512_);
                            v___x_1535_ = lean_box(0);
                            v_isShared_1536_ = v_isSharedCheck_1543_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1544_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1544_, 0, v_x_1499_);
                        lean_ctor_set(v___x_1544_, 1, v_x_1500_);
                        v___y_1516_ = v___x_1544_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1517_ = lean_array_fset(v_xs_x27_1514_, v_j_1506_, v___y_1516_);
                lean_dec(v_j_1506_);
                if v_isShared_1511_ == 0 {
                    lean_ctor_set(v___x_1510_, 0, v___x_1517_);
                    v___x_1519_ = v___x_1510_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
                    v___x_1519_ = v_reuseFailAlloc_1520_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1519_;
            }
            4 => {
                v___x_1526_ = l_Lean_instBEqMVarId_beq(v_x_1499_, v_key_1521_);
                if v___x_1526_ == 0 {
                    lean_del_object(v___x_1524_);
                    v___x_1527_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1521_,
                        v_val_1522_,
                        v_x_1499_,
                        v_x_1500_,
                    );
                    v___x_1528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1528_, 0, v___x_1527_);
                    v___y_1516_ = v___x_1528_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1522_);
                    lean_dec(v_key_1521_);
                    if v_isShared_1525_ == 0 {
                        lean_ctor_set(v___x_1524_, 1, v_x_1500_);
                        lean_ctor_set(v___x_1524_, 0, v_x_1499_);
                        v___x_1530_ = v___x_1524_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_x_1499_);
                        lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_x_1500_);
                        v___x_1530_ = v_reuseFailAlloc_1531_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1516_ = v___x_1530_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1537_ = lean_usize_shift_right(v_x_1497_, v___x_1502_);
                v___x_1538_ = lean_usize_add(v_x_1498_, v___x_1503_);
                v___x_1539_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_node_1533_, v___x_1537_, v___x_1538_, v_x_1499_, v_x_1500_);
                if v_isShared_1536_ == 0 {
                    lean_ctor_set(v___x_1535_, 0, v___x_1539_);
                    v___x_1541_ = v___x_1535_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
                    v___x_1541_ = v_reuseFailAlloc_1542_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1516_ = v___x_1541_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1551_ == 0 {
                    v___x_1553_ = v___x_1550_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_ks_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_vs_1548_);
                    v___x_1553_ = v_reuseFailAlloc_1567_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1554_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v___x_1553_, v_x_1499_, v_x_1500_);
                v___x_1562_ = 7usize;
                v___x_1563_ = lean_usize_dec_le(v___x_1562_, v_x_1498_);
                if v___x_1563_ == 0 {
                    v___x_1564_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1554_);
                    v___x_1565_ = lean_unsigned_to_nat(4);
                    v___x_1566_ = lean_nat_dec_lt(v___x_1564_, v___x_1565_);
                    lean_dec(v___x_1564_);
                    v___y_1556_ = v___x_1566_;
                    state = 10;
                    continue;
                } else {
                    v___y_1556_ = v___x_1563_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1556_ == 0 {
                    v_ks_1557_ = lean_ctor_get(v_newNode_1554_, 0);
                    lean_inc_ref(v_ks_1557_);
                    v_vs_1558_ = lean_ctor_get(v_newNode_1554_, 1);
                    lean_inc_ref(v_vs_1558_);
                    lean_dec_ref(v_newNode_1554_);
                    v___x_1559_ = lean_unsigned_to_nat(0);
                    v___x_1560_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2);
                    v___x_1561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_x_1498_, v_ks_1557_, v_vs_1558_, v___x_1559_, v___x_1560_);
                    lean_dec_ref(v_vs_1558_);
                    lean_dec_ref(v_ks_1557_);
                    return v___x_1561_;
                } else {
                    return v_newNode_1554_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(
    mut v_depth_1569_: usize,
    mut v_keys_1570_: *mut LeanObject,
    mut v_vals_1571_: *mut LeanObject,
    mut v_i_1572_: *mut LeanObject,
    mut v_entries_1573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v_k_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u64 = 0;
    let mut v_h_1579_: usize = 0;
    let mut v___x_1580_: usize = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1584_: usize = 0;
    let mut v_h_1585_: usize = 0;
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1574_ = lean_array_get_size(v_keys_1570_);
                v___x_1575_ = lean_nat_dec_lt(v_i_1572_, v___x_1574_);
                if v___x_1575_ == 0 {
                    lean_dec(v_i_1572_);
                    return v_entries_1573_;
                } else {
                    v_k_1576_ = lean_array_fget_borrowed(v_keys_1570_, v_i_1572_);
                    v_v_1577_ = lean_array_fget_borrowed(v_vals_1571_, v_i_1572_);
                    v___x_1578_ = l_Lean_instHashableMVarId_hash(v_k_1576_);
                    v_h_1579_ = lean_uint64_to_usize(v___x_1578_);
                    v___x_1580_ = 5usize;
                    v___x_1581_ = lean_unsigned_to_nat(1);
                    v___x_1582_ = 1usize;
                    v___x_1583_ = lean_usize_sub(v_depth_1569_, v___x_1582_);
                    v___x_1584_ = lean_usize_mul(v___x_1580_, v___x_1583_);
                    v_h_1585_ = lean_usize_shift_right(v_h_1579_, v___x_1584_);
                    v___x_1586_ = lean_nat_add(v_i_1572_, v___x_1581_);
                    lean_dec(v_i_1572_);
                    lean_inc(v_v_1577_);
                    lean_inc(v_k_1576_);
                    v___x_1587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_entries_1573_, v_h_1585_, v_depth_1569_, v_k_1576_, v_v_1577_);
                    v_i_1572_ = v___x_1586_;
                    v_entries_1573_ = v___x_1587_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg___boxed(
    mut v_depth_1589_: *mut LeanObject,
    mut v_keys_1590_: *mut LeanObject,
    mut v_vals_1591_: *mut LeanObject,
    mut v_i_1592_: *mut LeanObject,
    mut v_entries_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1594_: usize = 0;
    let mut v_res_1595_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1594_ = lean_unbox_usize(v_depth_1589_);
    lean_dec(v_depth_1589_);
    v_res_1595_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_boxed_1594_, v_keys_1590_, v_vals_1591_, v_i_1592_, v_entries_1593_);
    lean_dec_ref(v_vals_1591_);
    lean_dec_ref(v_keys_1590_);
    return v_res_1595_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___boxed(
    mut v_x_1596_: *mut LeanObject,
    mut v_x_1597_: *mut LeanObject,
    mut v_x_1598_: *mut LeanObject,
    mut v_x_1599_: *mut LeanObject,
    mut v_x_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_34068__boxed_1601_: usize = 0;
    let mut v_x_34069__boxed_1602_: usize = 0;
    let mut v_res_1603_: *mut LeanObject = core::ptr::null_mut();
    v_x_34068__boxed_1601_ = lean_unbox_usize(v_x_1597_);
    lean_dec(v_x_1597_);
    v_x_34069__boxed_1602_ = lean_unbox_usize(v_x_1598_);
    lean_dec(v_x_1598_);
    v_res_1603_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_1596_, v_x_34068__boxed_1601_, v_x_34069__boxed_1602_, v_x_1599_, v_x_1600_);
    return v_res_1603_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(
    mut v_x_1604_: *mut LeanObject,
    mut v_x_1605_: *mut LeanObject,
    mut v_x_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1607_: u64 = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: usize = 0;
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1607_ = l_Lean_instHashableMVarId_hash(v_x_1605_);
    v___x_1608_ = lean_uint64_to_usize(v___x_1607_);
    v___x_1609_ = 1usize;
    v___x_1610_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_1604_, v___x_1608_, v___x_1609_, v_x_1605_, v_x_1606_);
    return v___x_1610_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(
    mut v_mvarId_1611_: *mut LeanObject,
    mut v_val_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v_depth_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1636_: u8 = 0;
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut v_isSharedCheck_1648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1615_ = lean_st_ref_take(v___y_1613_);
                v_mctx_1616_ = lean_ctor_get(v___x_1615_, 0);
                v_cache_1617_ = lean_ctor_get(v___x_1615_, 1);
                v_zetaDeltaFVarIds_1618_ = lean_ctor_get(v___x_1615_, 2);
                v_postponed_1619_ = lean_ctor_get(v___x_1615_, 3);
                v_diag_1620_ = lean_ctor_get(v___x_1615_, 4);
                v_isSharedCheck_1648_ = (!lean_is_exclusive(v___x_1615_)) as u8;
                if v_isSharedCheck_1648_ == 0 {
                    v___x_1622_ = v___x_1615_;
                    v_isShared_1623_ = v_isSharedCheck_1648_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1620_);
                    lean_inc(v_postponed_1619_);
                    lean_inc(v_zetaDeltaFVarIds_1618_);
                    lean_inc(v_cache_1617_);
                    lean_inc(v_mctx_1616_);
                    lean_dec(v___x_1615_);
                    v___x_1622_ = lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1648_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1624_ = lean_ctor_get(v_mctx_1616_, 0);
                v_levelAssignDepth_1625_ = lean_ctor_get(v_mctx_1616_, 1);
                v_lmvarCounter_1626_ = lean_ctor_get(v_mctx_1616_, 2);
                v_mvarCounter_1627_ = lean_ctor_get(v_mctx_1616_, 3);
                v_lDecls_1628_ = lean_ctor_get(v_mctx_1616_, 4);
                v_decls_1629_ = lean_ctor_get(v_mctx_1616_, 5);
                v_userNames_1630_ = lean_ctor_get(v_mctx_1616_, 6);
                v_lAssignment_1631_ = lean_ctor_get(v_mctx_1616_, 7);
                v_eAssignment_1632_ = lean_ctor_get(v_mctx_1616_, 8);
                v_dAssignment_1633_ = lean_ctor_get(v_mctx_1616_, 9);
                v_isSharedCheck_1647_ = (!lean_is_exclusive(v_mctx_1616_)) as u8;
                if v_isSharedCheck_1647_ == 0 {
                    v___x_1635_ = v_mctx_1616_;
                    v_isShared_1636_ = v_isSharedCheck_1647_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1633_);
                    lean_inc(v_eAssignment_1632_);
                    lean_inc(v_lAssignment_1631_);
                    lean_inc(v_userNames_1630_);
                    lean_inc(v_decls_1629_);
                    lean_inc(v_lDecls_1628_);
                    lean_inc(v_mvarCounter_1627_);
                    lean_inc(v_lmvarCounter_1626_);
                    lean_inc(v_levelAssignDepth_1625_);
                    lean_inc(v_depth_1624_);
                    lean_dec(v_mctx_1616_);
                    v___x_1635_ = lean_box(0);
                    v_isShared_1636_ = v_isSharedCheck_1647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1637_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_1632_, v_mvarId_1611_, v_val_1612_);
                if v_isShared_1636_ == 0 {
                    lean_ctor_set(v___x_1635_, 8, v___x_1637_);
                    v___x_1639_ = v___x_1635_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_depth_1624_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_levelAssignDepth_1625_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_lmvarCounter_1626_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_mvarCounter_1627_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_lDecls_1628_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 5, v_decls_1629_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 6, v_userNames_1630_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 7, v_lAssignment_1631_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 8, v___x_1637_);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 9, v_dAssignment_1633_);
                    v___x_1639_ = v_reuseFailAlloc_1646_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1623_ == 0 {
                    lean_ctor_set(v___x_1622_, 0, v___x_1639_);
                    v___x_1641_ = v___x_1622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1639_);
                    lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_cache_1617_);
                    lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_zetaDeltaFVarIds_1618_);
                    lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_postponed_1619_);
                    lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_diag_1620_);
                    v___x_1641_ = v_reuseFailAlloc_1645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1642_ = lean_st_ref_set(v___y_1613_, v___x_1641_);
                v___x_1643_ = lean_box(0);
                v___x_1644_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1644_, 0, v___x_1643_);
                return v___x_1644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(
    mut v_mvarId_1649_: *mut LeanObject,
    mut v_val_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1653_: *mut LeanObject = core::ptr::null_mut();
    v_res_1653_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(
        v_mvarId_1649_,
        v_val_1650_,
        v___y_1651_,
    );
    lean_dec(v___y_1651_);
    return v_res_1653_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(
    mut v_keys_1654_: *mut LeanObject,
    mut v_i_1655_: *mut LeanObject,
    mut v_k_1656_: *mut LeanObject,
) -> u8 {
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    let mut v_k_x27_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1657_ = lean_array_get_size(v_keys_1654_);
                v___x_1658_ = lean_nat_dec_lt(v_i_1655_, v___x_1657_);
                if v___x_1658_ == 0 {
                    lean_dec(v_i_1655_);
                    return v___x_1658_;
                } else {
                    v_k_x27_1659_ = lean_array_fget_borrowed(v_keys_1654_, v_i_1655_);
                    v___x_1660_ = l_Lean_instBEqMVarId_beq(v_k_1656_, v_k_x27_1659_);
                    if v___x_1660_ == 0 {
                        v___x_1661_ = lean_unsigned_to_nat(1);
                        v___x_1662_ = lean_nat_add(v_i_1655_, v___x_1661_);
                        lean_dec(v_i_1655_);
                        v_i_1655_ = v___x_1662_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_1655_);
                        return v___x_1660_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_keys_1664_: *mut LeanObject,
    mut v_i_1665_: *mut LeanObject,
    mut v_k_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1667_: u8 = 0;
    let mut v_r_1668_: *mut LeanObject = core::ptr::null_mut();
    v_res_1667_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_1664_, v_i_1665_, v_k_1666_);
    lean_dec(v_k_1666_);
    lean_dec_ref(v_keys_1664_);
    v_r_1668_ = lean_box((v_res_1667_) as usize);
    return v_r_1668_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(
    mut v_x_1669_: *mut LeanObject,
    mut v_x_1670_: usize,
    mut v_x_1671_: *mut LeanObject,
) -> u8 {
    let mut v_es_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: usize = 0;
    let mut v_j_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v_node_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: usize = 0;
    let mut v___x_1684_: u8 = 0;
    let mut v_ks_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1669_) == 0 {
                    v_es_1672_ = lean_ctor_get(v_x_1669_, 0);
                    v___x_1673_ = lean_box(2);
                    v___x_1674_ = 5usize;
                    v___x_1675_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1);
                    v___x_1676_ = lean_usize_land(v_x_1670_, v___x_1675_);
                    v_j_1677_ = lean_usize_to_nat(v___x_1676_);
                    v___x_1678_ = lean_array_get_borrowed(v___x_1673_, v_es_1672_, v_j_1677_);
                    lean_dec(v_j_1677_);
                    match lean_obj_tag(v___x_1678_) {
                        0 => {
                            v_key_1679_ = lean_ctor_get(v___x_1678_, 0);
                            v___x_1680_ = l_Lean_instBEqMVarId_beq(v_x_1671_, v_key_1679_);
                            return v___x_1680_;
                        }
                        1 => {
                            v_node_1681_ = lean_ctor_get(v___x_1678_, 0);
                            v___x_1682_ = lean_usize_shift_right(v_x_1670_, v___x_1674_);
                            v_x_1669_ = v_node_1681_;
                            v_x_1670_ = v___x_1682_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1684_ = 0;
                            return v___x_1684_;
                        }
                    }
                } else {
                    v_ks_1685_ = lean_ctor_get(v_x_1669_, 0);
                    v___x_1686_ = lean_unsigned_to_nat(0);
                    v___x_1687_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_ks_1685_, v___x_1686_, v_x_1671_);
                    return v___x_1687_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_1688_: *mut LeanObject,
    mut v_x_1689_: *mut LeanObject,
    mut v_x_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_34306__boxed_1691_: usize = 0;
    let mut v_res_1692_: u8 = 0;
    let mut v_r_1693_: *mut LeanObject = core::ptr::null_mut();
    v_x_34306__boxed_1691_ = lean_unbox_usize(v_x_1689_);
    lean_dec(v_x_1689_);
    v_res_1692_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_1688_, v_x_34306__boxed_1691_, v_x_1690_);
    lean_dec(v_x_1690_);
    lean_dec_ref(v_x_1688_);
    v_r_1693_ = lean_box((v_res_1692_) as usize);
    return v_r_1693_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(
    mut v_x_1694_: *mut LeanObject,
    mut v_x_1695_: *mut LeanObject,
) -> u8 {
    let mut v___x_1696_: u64 = 0;
    let mut v___x_1697_: usize = 0;
    let mut v___x_1698_: u8 = 0;
    v___x_1696_ = l_Lean_instHashableMVarId_hash(v_x_1695_);
    v___x_1697_ = lean_uint64_to_usize(v___x_1696_);
    v___x_1698_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_1694_, v___x_1697_, v_x_1695_);
    return v___x_1698_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg___boxed(
    mut v_x_1699_: *mut LeanObject,
    mut v_x_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1701_: u8 = 0;
    let mut v_r_1702_: *mut LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_1699_, v_x_1700_);
    lean_dec(v_x_1700_);
    lean_dec_ref(v_x_1699_);
    v_r_1702_ = lean_box((v_res_1701_) as usize);
    return v_r_1702_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(
    mut v_mvarId_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: u8 = 0;
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = lean_st_ref_get(v___y_1704_);
    v_mctx_1707_ = lean_ctor_get(v___x_1706_, 0);
    lean_inc_ref(v_mctx_1707_);
    lean_dec(v___x_1706_);
    v_eAssignment_1708_ = lean_ctor_get(v_mctx_1707_, 8);
    lean_inc_ref(v_eAssignment_1708_);
    lean_dec_ref(v_mctx_1707_);
    v___x_1709_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_eAssignment_1708_, v_mvarId_1703_);
    lean_dec_ref(v_eAssignment_1708_);
    v___x_1710_ = lean_box((v___x_1709_) as usize);
    v___x_1711_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1711_, 0, v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(
    mut v_mvarId_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1715_: *mut LeanObject = core::ptr::null_mut();
    v_res_1715_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(
            v_mvarId_1712_,
            v___y_1713_,
        );
    lean_dec(v___y_1713_);
    lean_dec(v_mvarId_1712_);
    return v_res_1715_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(
    mut v_upperBound_1716_: *mut LeanObject,
    mut v_d_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
    mut v_b_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_fst_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1745_: u8 = 0;
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: u8 = 0;
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___y_1761_: u8 = 0;
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v_contextDependent_1775_: u8 = 0;
    let mut v_proof_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_1777_: u8 = 0;
    let mut v___y_1779_: u8 = 0;
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut v_a_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1798_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut v___x_1803_: u8 = 0;
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v_a_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_a_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut v_a_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1841_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut v___x_1846_: u8 = 0;
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut v_unused_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1735_ = lean_nat_dec_lt(v_a_1718_, v_upperBound_1716_);
                if v___x_1735_ == 0 {
                    lean_dec(v_a_1718_);
                    lean_dec_ref(v_d_1717_);
                    v___x_1736_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1736_, 0, v_b_1719_);
                    return v___x_1736_;
                } else {
                    v_snd_1737_ = lean_ctor_get(v_b_1719_, 1);
                    v_isSharedCheck_1871_ = (!lean_is_exclusive(v_b_1719_)) as u8;
                    if v_isSharedCheck_1871_ == 0 {
                        v_unused_1872_ = lean_ctor_get(v_b_1719_, 0);
                        lean_dec(v_unused_1872_);
                        v___x_1739_ = v_b_1719_;
                        v_isShared_1740_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1737_);
                        lean_dec(v_b_1719_);
                        v___x_1739_ = lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1732_ = lean_unsigned_to_nat(1);
                v___x_1733_ = lean_nat_add(v_a_1718_, v___x_1732_);
                lean_dec(v_a_1718_);
                v_a_1718_ = v___x_1733_;
                v_b_1719_ = v_a_1731_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_1741_ = lean_ctor_get(v_snd_1737_, 0);
                v_snd_1742_ = lean_ctor_get(v_snd_1737_, 1);
                v_isSharedCheck_1870_ = (!lean_is_exclusive(v_snd_1737_)) as u8;
                if v_isSharedCheck_1870_ == 0 {
                    v___x_1744_ = v_snd_1737_;
                    v_isShared_1745_ = v_isSharedCheck_1870_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_1742_);
                    lean_inc(v_fst_1741_);
                    lean_dec(v_snd_1737_);
                    v___x_1744_ = lean_box(0);
                    v_isShared_1745_ = v_isSharedCheck_1870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1746_ = lean_box(0);
                v___x_1747_ = lean_array_fget_borrowed(v_fst_1741_, v_a_1718_);
                if lean_obj_tag(v___x_1747_) == 2 {
                    v_mvarId_1748_ = lean_ctor_get(v___x_1747_, 0);
                    v___x_1749_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_1748_, v___y_1726_);
                    if lean_obj_tag(v___x_1749_) == 0 {
                        v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
                        lean_inc(v_a_1750_);
                        lean_dec_ref_known(v___x_1749_, 1);
                        v___x_1751_ = (lean_unbox(v_a_1750_) as u8);
                        lean_dec(v_a_1750_);
                        if v___x_1751_ == 0 {
                            lean_inc(v_mvarId_1748_);
                            v___x_1752_ = l_Lean_MVarId_getDecl(
                                v_mvarId_1748_,
                                v___y_1725_,
                                v___y_1726_,
                                v___y_1727_,
                                v___y_1728_,
                            );
                            if lean_obj_tag(v___x_1752_) == 0 {
                                v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
                                lean_inc(v_a_1753_);
                                lean_dec_ref_known(v___x_1752_, 1);
                                v_type_1754_ = lean_ctor_get(v_a_1753_, 2);
                                lean_inc_ref(v_type_1754_);
                                lean_dec(v_a_1753_);
                                lean_inc_ref(v_d_1717_);
                                lean_inc(v___y_1728_);
                                lean_inc_ref(v___y_1727_);
                                lean_inc(v___y_1726_);
                                lean_inc_ref(v___y_1725_);
                                lean_inc(v___y_1724_);
                                lean_inc_ref(v___y_1723_);
                                lean_inc(v___y_1722_);
                                lean_inc_ref(v___y_1721_);
                                lean_inc(v___y_1720_);
                                v___x_1755_ = lean_apply_11(
                                    v_d_1717_,
                                    v_type_1754_,
                                    v___y_1720_,
                                    v___y_1721_,
                                    v___y_1722_,
                                    v___y_1723_,
                                    v___y_1724_,
                                    v___y_1725_,
                                    v___y_1726_,
                                    v___y_1727_,
                                    v___y_1728_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_1755_) == 0 {
                                    v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
                                    v_isSharedCheck_1804_ = (!lean_is_exclusive(v___x_1755_)) as u8;
                                    if v_isSharedCheck_1804_ == 0 {
                                        v___x_1758_ = v___x_1755_;
                                        v_isShared_1759_ = v_isSharedCheck_1804_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1756_);
                                        lean_dec(v___x_1755_);
                                        v___x_1758_ = lean_box(0);
                                        v_isShared_1759_ = v_isSharedCheck_1804_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_1744_);
                                    lean_dec(v_snd_1742_);
                                    lean_dec(v_fst_1741_);
                                    lean_del_object(v___x_1739_);
                                    lean_dec(v_a_1718_);
                                    lean_dec_ref(v_d_1717_);
                                    v_a_1805_ = lean_ctor_get(v___x_1755_, 0);
                                    v_isSharedCheck_1812_ = (!lean_is_exclusive(v___x_1755_)) as u8;
                                    if v_isSharedCheck_1812_ == 0 {
                                        v___x_1807_ = v___x_1755_;
                                        v_isShared_1808_ = v_isSharedCheck_1812_;
                                        state = 14;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1805_);
                                        lean_dec(v___x_1755_);
                                        v___x_1807_ = lean_box(0);
                                        v_isShared_1808_ = v_isSharedCheck_1812_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_1744_);
                                lean_dec(v_snd_1742_);
                                lean_dec(v_fst_1741_);
                                lean_del_object(v___x_1739_);
                                lean_dec(v_a_1718_);
                                lean_dec_ref(v_d_1717_);
                                v_a_1813_ = lean_ctor_get(v___x_1752_, 0);
                                v_isSharedCheck_1820_ = (!lean_is_exclusive(v___x_1752_)) as u8;
                                if v_isSharedCheck_1820_ == 0 {
                                    v___x_1815_ = v___x_1752_;
                                    v_isShared_1816_ = v_isSharedCheck_1820_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_1813_);
                                    lean_dec(v___x_1752_);
                                    v___x_1815_ = lean_box(0);
                                    v_isShared_1816_ = v_isSharedCheck_1820_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc_ref(v___x_1747_);
                            v___x_1821_ = l_Lean_Meta_Sym_instantiateMVarsS(
                                v___x_1747_,
                                v___y_1723_,
                                v___y_1724_,
                                v___y_1725_,
                                v___y_1726_,
                                v___y_1727_,
                                v___y_1728_,
                            );
                            if lean_obj_tag(v___x_1821_) == 0 {
                                v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
                                lean_inc(v_a_1822_);
                                lean_dec_ref_known(v___x_1821_, 1);
                                v___x_1823_ = lean_array_fset(v_fst_1741_, v_a_1718_, v_a_1822_);
                                if v_isShared_1745_ == 0 {
                                    lean_ctor_set(v___x_1744_, 0, v___x_1823_);
                                    v___x_1825_ = v___x_1744_;
                                    state = 18;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1823_);
                                    lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_snd_1742_);
                                    v___x_1825_ = v_reuseFailAlloc_1829_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_1744_);
                                lean_dec(v_snd_1742_);
                                lean_dec(v_fst_1741_);
                                lean_del_object(v___x_1739_);
                                lean_dec(v_a_1718_);
                                lean_dec_ref(v_d_1717_);
                                v_a_1830_ = lean_ctor_get(v___x_1821_, 0);
                                v_isSharedCheck_1837_ = (!lean_is_exclusive(v___x_1821_)) as u8;
                                if v_isSharedCheck_1837_ == 0 {
                                    v___x_1832_ = v___x_1821_;
                                    v_isShared_1833_ = v_isSharedCheck_1837_;
                                    state = 20;
                                    continue;
                                } else {
                                    lean_inc(v_a_1830_);
                                    lean_dec(v___x_1821_);
                                    v___x_1832_ = lean_box(0);
                                    v_isShared_1833_ = v_isSharedCheck_1837_;
                                    state = 20;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_1744_);
                        lean_dec(v_snd_1742_);
                        lean_dec(v_fst_1741_);
                        lean_del_object(v___x_1739_);
                        lean_dec(v_a_1718_);
                        lean_dec_ref(v_d_1717_);
                        v_a_1838_ = lean_ctor_get(v___x_1749_, 0);
                        v_isSharedCheck_1845_ = (!lean_is_exclusive(v___x_1749_)) as u8;
                        if v_isSharedCheck_1845_ == 0 {
                            v___x_1840_ = v___x_1749_;
                            v_isShared_1841_ = v_isSharedCheck_1845_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_1838_);
                            lean_dec(v___x_1749_);
                            v___x_1840_ = lean_box(0);
                            v_isShared_1841_ = v_isSharedCheck_1845_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    v___x_1846_ = l_Lean_Expr_hasMVar(v___x_1747_);
                    if v___x_1846_ == 0 {
                        if v_isShared_1745_ == 0 {
                            v___x_1848_ = v___x_1744_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_fst_1741_);
                            lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_snd_1742_);
                            v___x_1848_ = v_reuseFailAlloc_1852_;
                            state = 24;
                            continue;
                        }
                    } else {
                        lean_inc(v___x_1747_);
                        v___x_1853_ = l_Lean_Meta_Sym_instantiateMVarsS(
                            v___x_1747_,
                            v___y_1723_,
                            v___y_1724_,
                            v___y_1725_,
                            v___y_1726_,
                            v___y_1727_,
                            v___y_1728_,
                        );
                        if lean_obj_tag(v___x_1853_) == 0 {
                            v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
                            lean_inc(v_a_1854_);
                            lean_dec_ref_known(v___x_1853_, 1);
                            v___x_1855_ = lean_array_fset(v_fst_1741_, v_a_1718_, v_a_1854_);
                            if v_isShared_1745_ == 0 {
                                lean_ctor_set(v___x_1744_, 0, v___x_1855_);
                                v___x_1857_ = v___x_1744_;
                                state = 26;
                                continue;
                            } else {
                                v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1855_);
                                lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_snd_1742_);
                                v___x_1857_ = v_reuseFailAlloc_1861_;
                                state = 26;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1744_);
                            lean_dec(v_snd_1742_);
                            lean_dec(v_fst_1741_);
                            lean_del_object(v___x_1739_);
                            lean_dec(v_a_1718_);
                            lean_dec_ref(v_d_1717_);
                            v_a_1862_ = lean_ctor_get(v___x_1853_, 0);
                            v_isSharedCheck_1869_ = (!lean_is_exclusive(v___x_1853_)) as u8;
                            if v_isSharedCheck_1869_ == 0 {
                                v___x_1864_ = v___x_1853_;
                                v_isShared_1865_ = v_isSharedCheck_1869_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_1862_);
                                lean_dec(v___x_1853_);
                                v___x_1864_ = lean_box(0);
                                v_isShared_1865_ = v_isSharedCheck_1869_;
                                state = 28;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_1756_) == 0 {
                    lean_dec(v_a_1718_);
                    lean_dec_ref(v_d_1717_);
                    v___x_1774_ = (lean_unbox(v_snd_1742_) as u8);
                    lean_dec(v_snd_1742_);
                    if v___x_1774_ == 0 {
                        v_contextDependent_1775_ = lean_ctor_get_uint8(v_a_1756_, 0 as u32);
                        lean_dec_ref_known(v_a_1756_, 0);
                        v___y_1761_ = v_contextDependent_1775_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref_known(v_a_1756_, 0);
                        v___y_1761_ = v___x_1735_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1758_);
                    lean_del_object(v___x_1744_);
                    lean_del_object(v___x_1739_);
                    v_proof_1776_ = lean_ctor_get(v_a_1756_, 0);
                    lean_inc_ref(v_proof_1776_);
                    v_contextDependent_1777_ = lean_ctor_get_uint8(
                        v_a_1756_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_a_1756_, 1);
                    v___x_1803_ = (lean_unbox(v_snd_1742_) as u8);
                    lean_dec(v_snd_1742_);
                    if v___x_1803_ == 0 {
                        v___y_1779_ = v_contextDependent_1777_;
                        state = 9;
                        continue;
                    } else {
                        v___y_1779_ = v___x_1735_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1762_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_1761_);
                v___x_1763_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                v___x_1764_ = lean_box((v___y_1761_) as usize);
                if v_isShared_1745_ == 0 {
                    lean_ctor_set(v___x_1744_, 1, v___x_1764_);
                    v___x_1766_ = v___x_1744_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_fst_1741_);
                    lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1764_);
                    v___x_1766_ = v_reuseFailAlloc_1773_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 1, v___x_1766_);
                    lean_ctor_set(v___x_1739_, 0, v___x_1763_);
                    v___x_1768_ = v___x_1739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1763_);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1766_);
                    v___x_1768_ = v_reuseFailAlloc_1772_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1759_ == 0 {
                    lean_ctor_set(v___x_1758_, 0, v___x_1768_);
                    v___x_1770_ = v___x_1758_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
                    v___x_1770_ = v_reuseFailAlloc_1771_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1770_;
            }
            9 => {
                v___x_1780_ = l_Lean_Meta_Sym_instantiateMVarsS(
                    v_proof_1776_,
                    v___y_1723_,
                    v___y_1724_,
                    v___y_1725_,
                    v___y_1726_,
                    v___y_1727_,
                    v___y_1728_,
                );
                if lean_obj_tag(v___x_1780_) == 0 {
                    v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
                    lean_inc_n(v_a_1781_, 2);
                    lean_dec_ref_known(v___x_1780_, 1);
                    lean_inc(v_mvarId_1748_);
                    v___x_1782_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_1748_, v_a_1781_, v___y_1726_);
                    if lean_obj_tag(v___x_1782_) == 0 {
                        lean_dec_ref_known(v___x_1782_, 1);
                        v___x_1783_ = lean_array_fset(v_fst_1741_, v_a_1718_, v_a_1781_);
                        v___x_1784_ = lean_box((v___y_1779_) as usize);
                        v___x_1785_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1785_, 0, v___x_1783_);
                        lean_ctor_set(v___x_1785_, 1, v___x_1784_);
                        v___x_1786_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1786_, 0, v___x_1746_);
                        lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                        v_a_1731_ = v___x_1786_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_1781_);
                        lean_dec(v_fst_1741_);
                        lean_dec(v_a_1718_);
                        lean_dec_ref(v_d_1717_);
                        v_a_1787_ = lean_ctor_get(v___x_1782_, 0);
                        v_isSharedCheck_1794_ = (!lean_is_exclusive(v___x_1782_)) as u8;
                        if v_isSharedCheck_1794_ == 0 {
                            v___x_1789_ = v___x_1782_;
                            v_isShared_1790_ = v_isSharedCheck_1794_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1787_);
                            lean_dec(v___x_1782_);
                            v___x_1789_ = lean_box(0);
                            v_isShared_1790_ = v_isSharedCheck_1794_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_1741_);
                    lean_dec(v_a_1718_);
                    lean_dec_ref(v_d_1717_);
                    v_a_1795_ = lean_ctor_get(v___x_1780_, 0);
                    v_isSharedCheck_1802_ = (!lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1802_ == 0 {
                        v___x_1797_ = v___x_1780_;
                        v_isShared_1798_ = v_isSharedCheck_1802_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1795_);
                        lean_dec(v___x_1780_);
                        v___x_1797_ = lean_box(0);
                        v_isShared_1798_ = v_isSharedCheck_1802_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_1790_ == 0 {
                    v___x_1792_ = v___x_1789_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
                    v___x_1792_ = v_reuseFailAlloc_1793_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1792_;
            }
            12 => {
                if v_isShared_1798_ == 0 {
                    v___x_1800_ = v___x_1797_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
                    v___x_1800_ = v_reuseFailAlloc_1801_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1800_;
            }
            14 => {
                if v_isShared_1808_ == 0 {
                    v___x_1810_ = v___x_1807_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1810_;
            }
            16 => {
                if v_isShared_1816_ == 0 {
                    v___x_1818_ = v___x_1815_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
                    v___x_1818_ = v_reuseFailAlloc_1819_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1818_;
            }
            18 => {
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 1, v___x_1825_);
                    lean_ctor_set(v___x_1739_, 0, v___x_1746_);
                    v___x_1827_ = v___x_1739_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1746_);
                    lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1825_);
                    v___x_1827_ = v_reuseFailAlloc_1828_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v_a_1731_ = v___x_1827_;
                state = 1;
                continue;
            }
            20 => {
                if v_isShared_1833_ == 0 {
                    v___x_1835_ = v___x_1832_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
                    v___x_1835_ = v_reuseFailAlloc_1836_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1835_;
            }
            22 => {
                if v_isShared_1841_ == 0 {
                    v___x_1843_ = v___x_1840_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
                    v___x_1843_ = v_reuseFailAlloc_1844_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1843_;
            }
            24 => {
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 1, v___x_1848_);
                    lean_ctor_set(v___x_1739_, 0, v___x_1746_);
                    v___x_1850_ = v___x_1739_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1746_);
                    lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1848_);
                    v___x_1850_ = v_reuseFailAlloc_1851_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v_a_1731_ = v___x_1850_;
                state = 1;
                continue;
            }
            26 => {
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 1, v___x_1857_);
                    lean_ctor_set(v___x_1739_, 0, v___x_1746_);
                    v___x_1859_ = v___x_1739_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1746_);
                    lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___x_1857_);
                    v___x_1859_ = v_reuseFailAlloc_1860_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v_a_1731_ = v___x_1859_;
                state = 1;
                continue;
            }
            28 => {
                if v_isShared_1865_ == 0 {
                    v___x_1867_ = v___x_1864_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
                    v___x_1867_ = v_reuseFailAlloc_1868_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(
    mut v_upperBound_1873_: *mut LeanObject,
    mut v_d_1874_: *mut LeanObject,
    mut v_a_1875_: *mut LeanObject,
    mut v_b_1876_: *mut LeanObject,
    mut v___y_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
    mut v___y_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1887_: *mut LeanObject = core::ptr::null_mut();
    v_res_1887_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(
            v_upperBound_1873_,
            v_d_1874_,
            v_a_1875_,
            v_b_1876_,
            v___y_1877_,
            v___y_1878_,
            v___y_1879_,
            v___y_1880_,
            v___y_1881_,
            v___y_1882_,
            v___y_1883_,
            v___y_1884_,
            v___y_1885_,
        );
    lean_dec(v___y_1885_);
    lean_dec_ref(v___y_1884_);
    lean_dec(v___y_1883_);
    lean_dec_ref(v___y_1882_);
    lean_dec(v___y_1881_);
    lean_dec_ref(v___y_1880_);
    lean_dec(v___y_1879_);
    lean_dec_ref(v___y_1878_);
    lean_dec(v___y_1877_);
    lean_dec(v_upperBound_1873_);
    return v_res_1887_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(
    mut v_pattern_1890_: *mut LeanObject,
    mut v_e_1891_: *mut LeanObject,
    mut v___x_1892_: u8,
    mut v_d_1893_: *mut LeanObject,
    mut v_expr_1894_: *mut LeanObject,
    mut v_rhs_1895_: *mut LeanObject,
    mut v_perm_1896_: u8,
    mut v___y_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
    mut v___y_1903_: *mut LeanObject,
    mut v___y_1904_: *mut LeanObject,
    mut v___y_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v_val_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v_fst_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_a_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut v_a_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
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
    let mut v_reuseFailAlloc_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_a_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1891_);
                lean_inc_ref(v_pattern_1890_);
                v___x_1907_ = l_Lean_Meta_Sym_Pattern_match_x3f(
                    v_pattern_1890_,
                    v_e_1891_,
                    v___x_1892_,
                    v___y_1900_,
                    v___y_1901_,
                    v___y_1902_,
                    v___y_1903_,
                    v___y_1904_,
                    v___y_1905_,
                );
                if lean_obj_tag(v___x_1907_) == 0 {
                    v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
                    v_isSharedCheck_2024_ = (!lean_is_exclusive(v___x_1907_)) as u8;
                    if v_isSharedCheck_2024_ == 0 {
                        v___x_1910_ = v___x_1907_;
                        v_isShared_1911_ = v_isSharedCheck_2024_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1908_);
                        lean_dec(v___x_1907_);
                        v___x_1910_ = lean_box(0);
                        v_isShared_1911_ = v_isSharedCheck_2024_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_expr_1894_);
                    lean_dec_ref(v_d_1893_);
                    lean_dec_ref(v_e_1891_);
                    lean_dec_ref(v_pattern_1890_);
                    v_a_2025_ = lean_ctor_get(v___x_1907_, 0);
                    v_isSharedCheck_2032_ = (!lean_is_exclusive(v___x_1907_)) as u8;
                    if v_isSharedCheck_2032_ == 0 {
                        v___x_2027_ = v___x_1907_;
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_2025_);
                        lean_dec(v___x_1907_);
                        v___x_2027_ = lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1908_) == 1 {
                    lean_del_object(v___x_1910_);
                    v_val_1912_ = lean_ctor_get(v_a_1908_, 0);
                    lean_inc(v_val_1912_);
                    lean_dec_ref_known(v_a_1908_, 1);
                    v_us_1913_ = lean_ctor_get(v_val_1912_, 0);
                    v_args_1914_ = lean_ctor_get(v_val_1912_, 1);
                    v_isSharedCheck_2019_ = (!lean_is_exclusive(v_val_1912_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_1916_ = v_val_1912_;
                        v_isShared_1917_ = v_isSharedCheck_2019_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_args_1914_);
                        lean_inc(v_us_1913_);
                        lean_dec(v_val_1912_);
                        v___x_1916_ = lean_box(0);
                        v_isShared_1917_ = v_isSharedCheck_2019_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1908_);
                    lean_dec_ref(v_expr_1894_);
                    lean_dec_ref(v_d_1893_);
                    lean_dec_ref(v_e_1891_);
                    lean_dec_ref(v_pattern_1890_);
                    v___x_2020_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0;
                    if v_isShared_1911_ == 0 {
                        lean_ctor_set(v___x_1910_, 0, v___x_2020_);
                        v___x_2022_ = v___x_1910_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
                        v___x_2022_ = v_reuseFailAlloc_2023_;
                        state = 22;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1918_ = lean_box(0);
                v___x_1919_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(
                    v_us_1913_,
                    v___x_1918_,
                    v___y_1897_,
                    v___y_1898_,
                    v___y_1899_,
                    v___y_1900_,
                    v___y_1901_,
                    v___y_1902_,
                    v___y_1903_,
                    v___y_1904_,
                    v___y_1905_,
                );
                if lean_obj_tag(v___x_1919_) == 0 {
                    v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
                    lean_inc(v_a_1920_);
                    lean_dec_ref_known(v___x_1919_, 1);
                    v___x_1921_ = lean_array_get_size(v_args_1914_);
                    v___x_1922_ = lean_unsigned_to_nat(0);
                    v___x_1923_ = 0;
                    v___x_1924_ = lean_box(0);
                    v___x_1925_ = lean_box((v___x_1923_) as usize);
                    if v_isShared_1917_ == 0 {
                        lean_ctor_set(v___x_1916_, 1, v___x_1925_);
                        lean_ctor_set(v___x_1916_, 0, v_args_1914_);
                        v___x_1927_ = v___x_1916_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_args_1914_);
                        lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___x_1925_);
                        v___x_1927_ = v_reuseFailAlloc_2010_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1916_);
                    lean_dec_ref(v_args_1914_);
                    lean_dec_ref(v_expr_1894_);
                    lean_dec_ref(v_d_1893_);
                    lean_dec_ref(v_e_1891_);
                    lean_dec_ref(v_pattern_1890_);
                    v_a_2011_ = lean_ctor_get(v___x_1919_, 0);
                    v_isSharedCheck_2018_ = (!lean_is_exclusive(v___x_1919_)) as u8;
                    if v_isSharedCheck_2018_ == 0 {
                        v___x_2013_ = v___x_1919_;
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_2011_);
                        lean_dec(v___x_1919_);
                        v___x_2013_ = lean_box(0);
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 20;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1928_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1928_, 0, v___x_1924_);
                lean_ctor_set(v___x_1928_, 1, v___x_1927_);
                v___x_1929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v___x_1921_, v_d_1893_, v___x_1922_, v___x_1928_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
                if lean_obj_tag(v___x_1929_) == 0 {
                    v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
                    v_isSharedCheck_2001_ = (!lean_is_exclusive(v___x_1929_)) as u8;
                    if v_isSharedCheck_2001_ == 0 {
                        v___x_1932_ = v___x_1929_;
                        v_isShared_1933_ = v_isSharedCheck_2001_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1930_);
                        lean_dec(v___x_1929_);
                        v___x_1932_ = lean_box(0);
                        v_isShared_1933_ = v_isSharedCheck_2001_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1920_);
                    lean_dec_ref(v_expr_1894_);
                    lean_dec_ref(v_e_1891_);
                    lean_dec_ref(v_pattern_1890_);
                    v_a_2002_ = lean_ctor_get(v___x_1929_, 0);
                    v_isSharedCheck_2009_ = (!lean_is_exclusive(v___x_1929_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2004_ = v___x_1929_;
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_2002_);
                        lean_dec(v___x_1929_);
                        v___x_2004_ = lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 18;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_1934_ = lean_ctor_get(v_a_1930_, 0);
                if lean_obj_tag(v_fst_1934_) == 0 {
                    lean_del_object(v___x_1932_);
                    v_snd_1935_ = lean_ctor_get(v_a_1930_, 1);
                    lean_inc(v_snd_1935_);
                    lean_dec(v_a_1930_);
                    v_fst_1936_ = lean_ctor_get(v_snd_1935_, 0);
                    lean_inc(v_fst_1936_);
                    v_snd_1937_ = lean_ctor_get(v_snd_1935_, 1);
                    lean_inc(v_snd_1937_);
                    lean_dec(v_snd_1935_);
                    v_levelParams_1938_ = lean_ctor_get(v_pattern_1890_, 0);
                    lean_inc(v_levelParams_1938_);
                    lean_inc(v_a_1920_);
                    v___x_1939_ =
                        l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(
                            v_expr_1894_,
                            v_pattern_1890_,
                            v_a_1920_,
                            v_fst_1936_,
                        );
                    v___x_1940_ = l_Lean_Expr_instantiateLevelParams(
                        v_rhs_1895_,
                        v_levelParams_1938_,
                        v_a_1920_,
                    );
                    v___x_1941_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1940_, v___y_1901_);
                    if lean_obj_tag(v___x_1941_) == 0 {
                        v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
                        lean_inc(v_a_1942_);
                        lean_dec_ref_known(v___x_1941_, 1);
                        v___x_1943_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                            v_a_1942_,
                            v_fst_1936_,
                            v___y_1901_,
                        );
                        lean_dec(v_fst_1936_);
                        if lean_obj_tag(v___x_1943_) == 0 {
                            v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
                            v_isSharedCheck_1980_ = (!lean_is_exclusive(v___x_1943_)) as u8;
                            if v_isSharedCheck_1980_ == 0 {
                                v___x_1946_ = v___x_1943_;
                                v_isShared_1947_ = v_isSharedCheck_1980_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1944_);
                                lean_dec(v___x_1943_);
                                v___x_1946_ = lean_box(0);
                                v_isShared_1947_ = v_isSharedCheck_1980_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1939_);
                            lean_dec(v_snd_1937_);
                            lean_dec_ref(v_e_1891_);
                            v_a_1981_ = lean_ctor_get(v___x_1943_, 0);
                            v_isSharedCheck_1988_ = (!lean_is_exclusive(v___x_1943_)) as u8;
                            if v_isSharedCheck_1988_ == 0 {
                                v___x_1983_ = v___x_1943_;
                                v_isShared_1984_ = v_isSharedCheck_1988_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_1981_);
                                lean_dec(v___x_1943_);
                                v___x_1983_ = lean_box(0);
                                v_isShared_1984_ = v_isSharedCheck_1988_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1939_);
                        lean_dec(v_snd_1937_);
                        lean_dec(v_fst_1936_);
                        lean_dec_ref(v_e_1891_);
                        v_a_1989_ = lean_ctor_get(v___x_1941_, 0);
                        v_isSharedCheck_1996_ = (!lean_is_exclusive(v___x_1941_)) as u8;
                        if v_isSharedCheck_1996_ == 0 {
                            v___x_1991_ = v___x_1941_;
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_1989_);
                            lean_dec(v___x_1941_);
                            v___x_1991_ = lean_box(0);
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_inc_ref(v_fst_1934_);
                    lean_dec(v_a_1930_);
                    lean_dec(v_a_1920_);
                    lean_dec_ref(v_expr_1894_);
                    lean_dec_ref(v_e_1891_);
                    lean_dec_ref(v_pattern_1890_);
                    v_val_1997_ = lean_ctor_get(v_fst_1934_, 0);
                    lean_inc(v_val_1997_);
                    lean_dec_ref_known(v_fst_1934_, 1);
                    if v_isShared_1933_ == 0 {
                        lean_ctor_set(v___x_1932_, 0, v_val_1997_);
                        v___x_1999_ = v___x_1932_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1997_);
                        v___x_1999_ = v_reuseFailAlloc_2000_;
                        state = 17;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1948_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_1891_, v_a_1944_,
                    );
                if v___x_1948_ == 0 {
                    lean_inc(v_a_1944_);
                    v___x_1949_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_1896_, v_e_1891_, v_a_1944_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
                    if lean_obj_tag(v___x_1949_) == 0 {
                        v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
                        v_isSharedCheck_1966_ = (!lean_is_exclusive(v___x_1949_)) as u8;
                        if v_isSharedCheck_1966_ == 0 {
                            v___x_1952_ = v___x_1949_;
                            v_isShared_1953_ = v_isSharedCheck_1966_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1950_);
                            lean_dec(v___x_1949_);
                            v___x_1952_ = lean_box(0);
                            v_isShared_1953_ = v_isSharedCheck_1966_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1946_);
                        lean_dec(v_a_1944_);
                        lean_dec_ref(v___x_1939_);
                        lean_dec(v_snd_1937_);
                        v_a_1967_ = lean_ctor_get(v___x_1949_, 0);
                        v_isSharedCheck_1974_ = (!lean_is_exclusive(v___x_1949_)) as u8;
                        if v_isSharedCheck_1974_ == 0 {
                            v___x_1969_ = v___x_1949_;
                            v_isShared_1970_ = v_isSharedCheck_1974_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1967_);
                            lean_dec(v___x_1949_);
                            v___x_1969_ = lean_box(0);
                            v_isShared_1970_ = v_isSharedCheck_1974_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1944_);
                    lean_dec_ref(v___x_1939_);
                    lean_dec_ref(v_e_1891_);
                    v___x_1975_ = (lean_unbox(v_snd_1937_) as u8);
                    lean_dec(v_snd_1937_);
                    v___x_1976_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1975_);
                    if v_isShared_1947_ == 0 {
                        lean_ctor_set(v___x_1946_, 0, v___x_1976_);
                        v___x_1978_ = v___x_1946_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
                        v___x_1978_ = v_reuseFailAlloc_1979_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1960_ = (lean_unbox(v_a_1950_) as u8);
                lean_dec(v_a_1950_);
                if v___x_1960_ == 0 {
                    lean_del_object(v___x_1946_);
                    lean_dec(v_a_1944_);
                    lean_dec_ref(v___x_1939_);
                    state = 7;
                    continue;
                } else {
                    if v___x_1948_ == 0 {
                        lean_del_object(v___x_1952_);
                        v___x_1961_ = lean_alloc_ctor(1, 2, (2) as u32);
                        lean_ctor_set(v___x_1961_, 0, v_a_1944_);
                        lean_ctor_set(v___x_1961_, 1, v___x_1939_);
                        lean_ctor_set_uint8(
                            v___x_1961_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_1923_,
                        );
                        v___x_1962_ = (lean_unbox(v_snd_1937_) as u8);
                        lean_dec(v_snd_1937_);
                        lean_ctor_set_uint8(
                            v___x_1961_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                            v___x_1962_,
                        );
                        if v_isShared_1947_ == 0 {
                            lean_ctor_set(v___x_1946_, 0, v___x_1961_);
                            v___x_1964_ = v___x_1946_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1961_);
                            v___x_1964_ = v_reuseFailAlloc_1965_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1946_);
                        lean_dec(v_a_1944_);
                        lean_dec_ref(v___x_1939_);
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_1955_ = (lean_unbox(v_snd_1937_) as u8);
                lean_dec(v_snd_1937_);
                v___x_1956_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1955_);
                if v_isShared_1953_ == 0 {
                    lean_ctor_set(v___x_1952_, 0, v___x_1956_);
                    v___x_1958_ = v___x_1952_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
                    v___x_1958_ = v_reuseFailAlloc_1959_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1958_;
            }
            9 => {
                return v___x_1964_;
            }
            10 => {
                if v_isShared_1970_ == 0 {
                    v___x_1972_ = v___x_1969_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
                    v___x_1972_ = v_reuseFailAlloc_1973_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1972_;
            }
            12 => {
                return v___x_1978_;
            }
            13 => {
                if v_isShared_1984_ == 0 {
                    v___x_1986_ = v___x_1983_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
                    v___x_1986_ = v_reuseFailAlloc_1987_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1986_;
            }
            15 => {
                if v_isShared_1992_ == 0 {
                    v___x_1994_ = v___x_1991_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
                    v___x_1994_ = v_reuseFailAlloc_1995_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1994_;
            }
            17 => {
                return v___x_1999_;
            }
            18 => {
                if v_isShared_2005_ == 0 {
                    v___x_2007_ = v___x_2004_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2007_;
            }
            20 => {
                if v_isShared_2014_ == 0 {
                    v___x_2016_ = v___x_2013_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
                    v___x_2016_ = v_reuseFailAlloc_2017_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2016_;
            }
            22 => {
                return v___x_2022_;
            }
            23 => {
                if v_isShared_2028_ == 0 {
                    v___x_2030_ = v___x_2027_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
                    v___x_2030_ = v_reuseFailAlloc_2031_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pattern_2033_: *mut LeanObject = *_args.add(0);
    let mut v_e_2034_: *mut LeanObject = *_args.add(1);
    let mut v___x_2035_: *mut LeanObject = *_args.add(2);
    let mut v_d_2036_: *mut LeanObject = *_args.add(3);
    let mut v_expr_2037_: *mut LeanObject = *_args.add(4);
    let mut v_rhs_2038_: *mut LeanObject = *_args.add(5);
    let mut v_perm_2039_: *mut LeanObject = *_args.add(6);
    let mut v___y_2040_: *mut LeanObject = *_args.add(7);
    let mut v___y_2041_: *mut LeanObject = *_args.add(8);
    let mut v___y_2042_: *mut LeanObject = *_args.add(9);
    let mut v___y_2043_: *mut LeanObject = *_args.add(10);
    let mut v___y_2044_: *mut LeanObject = *_args.add(11);
    let mut v___y_2045_: *mut LeanObject = *_args.add(12);
    let mut v___y_2046_: *mut LeanObject = *_args.add(13);
    let mut v___y_2047_: *mut LeanObject = *_args.add(14);
    let mut v___y_2048_: *mut LeanObject = *_args.add(15);
    let mut v___y_2049_: *mut LeanObject = *_args.add(16);
    let mut v___x_34692__boxed_2050_: u8 = 0;
    let mut v_perm_boxed_2051_: u8 = 0;
    let mut v_res_2052_: *mut LeanObject = core::ptr::null_mut();
    v___x_34692__boxed_2050_ = (lean_unbox(v___x_2035_) as u8);
    v_perm_boxed_2051_ = (lean_unbox(v_perm_2039_) as u8);
    v_res_2052_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(
        v_pattern_2033_,
        v_e_2034_,
        v___x_34692__boxed_2050_,
        v_d_2036_,
        v_expr_2037_,
        v_rhs_2038_,
        v_perm_boxed_2051_,
        v___y_2040_,
        v___y_2041_,
        v___y_2042_,
        v___y_2043_,
        v___y_2044_,
        v___y_2045_,
        v___y_2046_,
        v___y_2047_,
        v___y_2048_,
    );
    lean_dec(v___y_2048_);
    lean_dec_ref(v___y_2047_);
    lean_dec(v___y_2046_);
    lean_dec_ref(v___y_2045_);
    lean_dec(v___y_2044_);
    lean_dec_ref(v___y_2043_);
    lean_dec(v___y_2042_);
    lean_dec_ref(v___y_2041_);
    lean_dec(v___y_2040_);
    lean_dec_ref(v_rhs_2038_);
    return v_res_2052_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_rewrite(
    mut v_thm_2053_: *mut LeanObject,
    mut v_e_2054_: *mut LeanObject,
    mut v_d_2055_: *mut LeanObject,
    mut v_a_2056_: *mut LeanObject,
    mut v_a_2057_: *mut LeanObject,
    mut v_a_2058_: *mut LeanObject,
    mut v_a_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expr_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pattern_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perm_2069_: u8 = 0;
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    v_expr_2066_ = lean_ctor_get(v_thm_2053_, 0);
    lean_inc_ref(v_expr_2066_);
    v_pattern_2067_ = lean_ctor_get(v_thm_2053_, 1);
    lean_inc_ref(v_pattern_2067_);
    v_rhs_2068_ = lean_ctor_get(v_thm_2053_, 2);
    lean_inc_ref(v_rhs_2068_);
    v_perm_2069_ = lean_ctor_get_uint8(
        v_thm_2053_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_thm_2053_);
    v___x_2070_ = 1;
    v___x_2071_ = lean_box((v___x_2070_) as usize);
    v___x_2072_ = lean_box((v_perm_2069_) as usize);
    v___f_2073_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed as *mut core::ffi::c_void,
        17,
        7,
    );
    lean_closure_set(v___f_2073_, 0, v_pattern_2067_);
    lean_closure_set(v___f_2073_, 1, v_e_2054_);
    lean_closure_set(v___f_2073_, 2, v___x_2071_);
    lean_closure_set(v___f_2073_, 3, v_d_2055_);
    lean_closure_set(v___f_2073_, 4, v_expr_2066_);
    lean_closure_set(v___f_2073_, 5, v_rhs_2068_);
    lean_closure_set(v___f_2073_, 6, v___x_2072_);
    v___x_2074_ = 0;
    v___x_2075_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(
            v___f_2073_,
            v___x_2074_,
            v_a_2056_,
            v_a_2057_,
            v_a_2058_,
            v_a_2059_,
            v_a_2060_,
            v_a_2061_,
            v_a_2062_,
            v_a_2063_,
            v_a_2064_,
        );
    return v___x_2075_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(
    mut v_thm_2076_: *mut LeanObject,
    mut v_e_2077_: *mut LeanObject,
    mut v_d_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_a_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2089_: *mut LeanObject = core::ptr::null_mut();
    v_res_2089_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(
        v_thm_2076_,
        v_e_2077_,
        v_d_2078_,
        v_a_2079_,
        v_a_2080_,
        v_a_2081_,
        v_a_2082_,
        v_a_2083_,
        v_a_2084_,
        v_a_2085_,
        v_a_2086_,
        v_a_2087_,
    );
    lean_dec(v_a_2087_);
    lean_dec_ref(v_a_2086_);
    lean_dec(v_a_2085_);
    lean_dec_ref(v_a_2084_);
    lean_dec(v_a_2083_);
    lean_dec_ref(v_a_2082_);
    lean_dec(v_a_2081_);
    lean_dec_ref(v_a_2080_);
    lean_dec(v_a_2079_);
    return v_res_2089_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(
    mut v_mvarId_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(
            v_mvarId_2090_,
            v___y_2097_,
        );
    return v___x_2101_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(
    mut v_mvarId_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
    mut v___y_2108_: *mut LeanObject,
    mut v___y_2109_: *mut LeanObject,
    mut v___y_2110_: *mut LeanObject,
    mut v___y_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2113_: *mut LeanObject = core::ptr::null_mut();
    v_res_2113_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(
        v_mvarId_2102_,
        v___y_2103_,
        v___y_2104_,
        v___y_2105_,
        v___y_2106_,
        v___y_2107_,
        v___y_2108_,
        v___y_2109_,
        v___y_2110_,
        v___y_2111_,
    );
    lean_dec(v___y_2111_);
    lean_dec_ref(v___y_2110_);
    lean_dec(v___y_2109_);
    lean_dec_ref(v___y_2108_);
    lean_dec(v___y_2107_);
    lean_dec_ref(v___y_2106_);
    lean_dec(v___y_2105_);
    lean_dec_ref(v___y_2104_);
    lean_dec(v___y_2103_);
    lean_dec(v_mvarId_2102_);
    return v_res_2113_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(
    mut v_mvarId_2114_: *mut LeanObject,
    mut v_val_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
    mut v___y_2121_: *mut LeanObject,
    mut v___y_2122_: *mut LeanObject,
    mut v___y_2123_: *mut LeanObject,
    mut v___y_2124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(
        v_mvarId_2114_,
        v_val_2115_,
        v___y_2122_,
    );
    return v___x_2126_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(
    mut v_mvarId_2127_: *mut LeanObject,
    mut v_val_2128_: *mut LeanObject,
    mut v___y_2129_: *mut LeanObject,
    mut v___y_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2139_: *mut LeanObject = core::ptr::null_mut();
    v_res_2139_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(
        v_mvarId_2127_,
        v_val_2128_,
        v___y_2129_,
        v___y_2130_,
        v___y_2131_,
        v___y_2132_,
        v___y_2133_,
        v___y_2134_,
        v___y_2135_,
        v___y_2136_,
        v___y_2137_,
    );
    lean_dec(v___y_2137_);
    lean_dec_ref(v___y_2136_);
    lean_dec(v___y_2135_);
    lean_dec_ref(v___y_2134_);
    lean_dec(v___y_2133_);
    lean_dec_ref(v___y_2132_);
    lean_dec(v___y_2131_);
    lean_dec_ref(v___y_2130_);
    lean_dec(v___y_2129_);
    return v_res_2139_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(
    mut v_upperBound_2140_: *mut LeanObject,
    mut v_d_2141_: *mut LeanObject,
    mut v___x_2142_: *mut LeanObject,
    mut v_inst_2143_: *mut LeanObject,
    mut v_R_2144_: *mut LeanObject,
    mut v_a_2145_: *mut LeanObject,
    mut v_b_2146_: *mut LeanObject,
    mut v_c_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    v___x_2158_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(
            v_upperBound_2140_,
            v_d_2141_,
            v_a_2145_,
            v_b_2146_,
            v___y_2148_,
            v___y_2149_,
            v___y_2150_,
            v___y_2151_,
            v___y_2152_,
            v___y_2153_,
            v___y_2154_,
            v___y_2155_,
            v___y_2156_,
        );
    return v___x_2158_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_2159_: *mut LeanObject = *_args.add(0);
    let mut v_d_2160_: *mut LeanObject = *_args.add(1);
    let mut v___x_2161_: *mut LeanObject = *_args.add(2);
    let mut v_inst_2162_: *mut LeanObject = *_args.add(3);
    let mut v_R_2163_: *mut LeanObject = *_args.add(4);
    let mut v_a_2164_: *mut LeanObject = *_args.add(5);
    let mut v_b_2165_: *mut LeanObject = *_args.add(6);
    let mut v_c_2166_: *mut LeanObject = *_args.add(7);
    let mut v___y_2167_: *mut LeanObject = *_args.add(8);
    let mut v___y_2168_: *mut LeanObject = *_args.add(9);
    let mut v___y_2169_: *mut LeanObject = *_args.add(10);
    let mut v___y_2170_: *mut LeanObject = *_args.add(11);
    let mut v___y_2171_: *mut LeanObject = *_args.add(12);
    let mut v___y_2172_: *mut LeanObject = *_args.add(13);
    let mut v___y_2173_: *mut LeanObject = *_args.add(14);
    let mut v___y_2174_: *mut LeanObject = *_args.add(15);
    let mut v___y_2175_: *mut LeanObject = *_args.add(16);
    let mut v___y_2176_: *mut LeanObject = *_args.add(17);
    let mut v_res_2177_: *mut LeanObject = core::ptr::null_mut();
    v_res_2177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(
        v_upperBound_2159_,
        v_d_2160_,
        v___x_2161_,
        v_inst_2162_,
        v_R_2163_,
        v_a_2164_,
        v_b_2165_,
        v_c_2166_,
        v___y_2167_,
        v___y_2168_,
        v___y_2169_,
        v___y_2170_,
        v___y_2171_,
        v___y_2172_,
        v___y_2173_,
        v___y_2174_,
        v___y_2175_,
    );
    lean_dec(v___y_2175_);
    lean_dec_ref(v___y_2174_);
    lean_dec(v___y_2173_);
    lean_dec_ref(v___y_2172_);
    lean_dec(v___y_2171_);
    lean_dec_ref(v___y_2170_);
    lean_dec(v___y_2169_);
    lean_dec_ref(v___y_2168_);
    lean_dec(v___y_2167_);
    lean_dec(v___x_2161_);
    lean_dec(v_upperBound_2159_);
    return v_res_2177_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(
    mut v_00_u03b2_2178_: *mut LeanObject,
    mut v_x_2179_: *mut LeanObject,
    mut v_x_2180_: *mut LeanObject,
) -> u8 {
    let mut v___x_2181_: u8 = 0;
    v___x_2181_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_2179_, v_x_2180_);
    return v___x_2181_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(
    mut v_00_u03b2_2182_: *mut LeanObject,
    mut v_x_2183_: *mut LeanObject,
    mut v_x_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2185_: u8 = 0;
    let mut v_r_2186_: *mut LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_2182_, v_x_2183_, v_x_2184_);
    lean_dec(v_x_2184_);
    lean_dec_ref(v_x_2183_);
    v_r_2186_ = lean_box((v_res_2185_) as usize);
    return v_r_2186_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(
    mut v_00_u03b2_2187_: *mut LeanObject,
    mut v_x_2188_: *mut LeanObject,
    mut v_x_2189_: *mut LeanObject,
    mut v_x_2190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_2188_, v_x_2189_, v_x_2190_);
    return v___x_2191_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(
    mut v_00_u03b2_2192_: *mut LeanObject,
    mut v_x_2193_: *mut LeanObject,
    mut v_x_2194_: usize,
    mut v_x_2195_: *mut LeanObject,
) -> u8 {
    let mut v___x_2196_: u8 = 0;
    v___x_2196_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_2193_, v_x_2194_, v_x_2195_);
    return v___x_2196_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_2197_: *mut LeanObject,
    mut v_x_2198_: *mut LeanObject,
    mut v_x_2199_: *mut LeanObject,
    mut v_x_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_35102__boxed_2201_: usize = 0;
    let mut v_res_2202_: u8 = 0;
    let mut v_r_2203_: *mut LeanObject = core::ptr::null_mut();
    v_x_35102__boxed_2201_ = lean_unbox_usize(v_x_2199_);
    lean_dec(v_x_2199_);
    v_res_2202_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(v_00_u03b2_2197_, v_x_2198_, v_x_35102__boxed_2201_, v_x_2200_);
    lean_dec(v_x_2200_);
    lean_dec_ref(v_x_2198_);
    v_r_2203_ = lean_box((v_res_2202_) as usize);
    return v_r_2203_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(
    mut v_00_u03b2_2204_: *mut LeanObject,
    mut v_x_2205_: *mut LeanObject,
    mut v_x_2206_: usize,
    mut v_x_2207_: usize,
    mut v_x_2208_: *mut LeanObject,
    mut v_x_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_2205_, v_x_2206_, v_x_2207_, v_x_2208_, v_x_2209_);
    return v___x_2210_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___boxed(
    mut v_00_u03b2_2211_: *mut LeanObject,
    mut v_x_2212_: *mut LeanObject,
    mut v_x_2213_: *mut LeanObject,
    mut v_x_2214_: *mut LeanObject,
    mut v_x_2215_: *mut LeanObject,
    mut v_x_2216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_35113__boxed_2217_: usize = 0;
    let mut v_x_35114__boxed_2218_: usize = 0;
    let mut v_res_2219_: *mut LeanObject = core::ptr::null_mut();
    v_x_35113__boxed_2217_ = lean_unbox_usize(v_x_2213_);
    lean_dec(v_x_2213_);
    v_x_35114__boxed_2218_ = lean_unbox_usize(v_x_2214_);
    lean_dec(v_x_2214_);
    v_res_2219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(v_00_u03b2_2211_, v_x_2212_, v_x_35113__boxed_2217_, v_x_35114__boxed_2218_, v_x_2215_, v_x_2216_);
    return v_res_2219_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(
    mut v_00_u03b2_2220_: *mut LeanObject,
    mut v_keys_2221_: *mut LeanObject,
    mut v_vals_2222_: *mut LeanObject,
    mut v_heq_2223_: *mut LeanObject,
    mut v_i_2224_: *mut LeanObject,
    mut v_k_2225_: *mut LeanObject,
) -> u8 {
    let mut v___x_2226_: u8 = 0;
    v___x_2226_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_2221_, v_i_2224_, v_k_2225_);
    return v___x_2226_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_2227_: *mut LeanObject,
    mut v_keys_2228_: *mut LeanObject,
    mut v_vals_2229_: *mut LeanObject,
    mut v_heq_2230_: *mut LeanObject,
    mut v_i_2231_: *mut LeanObject,
    mut v_k_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2233_: u8 = 0;
    let mut v_r_2234_: *mut LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(v_00_u03b2_2227_, v_keys_2228_, v_vals_2229_, v_heq_2230_, v_i_2231_, v_k_2232_);
    lean_dec(v_k_2232_);
    lean_dec_ref(v_vals_2229_);
    lean_dec_ref(v_keys_2228_);
    v_r_2234_ = lean_box((v_res_2233_) as usize);
    return v_r_2234_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10(
    mut v_00_u03b2_2235_: *mut LeanObject,
    mut v_n_2236_: *mut LeanObject,
    mut v_k_2237_: *mut LeanObject,
    mut v_v_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    v___x_2239_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v_n_2236_, v_k_2237_, v_v_2238_);
    return v___x_2239_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(
    mut v_00_u03b2_2240_: *mut LeanObject,
    mut v_depth_2241_: usize,
    mut v_keys_2242_: *mut LeanObject,
    mut v_vals_2243_: *mut LeanObject,
    mut v_heq_2244_: *mut LeanObject,
    mut v_i_2245_: *mut LeanObject,
    mut v_entries_2246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    v___x_2247_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_2241_, v_keys_2242_, v_vals_2243_, v_i_2245_, v_entries_2246_);
    return v___x_2247_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___boxed(
    mut v_00_u03b2_2248_: *mut LeanObject,
    mut v_depth_2249_: *mut LeanObject,
    mut v_keys_2250_: *mut LeanObject,
    mut v_vals_2251_: *mut LeanObject,
    mut v_heq_2252_: *mut LeanObject,
    mut v_i_2253_: *mut LeanObject,
    mut v_entries_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2255_: usize = 0;
    let mut v_res_2256_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2255_ = lean_unbox_usize(v_depth_2249_);
    lean_dec(v_depth_2249_);
    v_res_2256_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_2248_, v_depth_boxed_2255_, v_keys_2250_, v_vals_2251_, v_heq_2252_, v_i_2253_, v_entries_2254_);
    lean_dec_ref(v_vals_2251_);
    lean_dec_ref(v_keys_2250_);
    return v_res_2256_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11(
    mut v_00_u03b2_2257_: *mut LeanObject,
    mut v_x_2258_: *mut LeanObject,
    mut v_x_2259_: *mut LeanObject,
    mut v_x_2260_: *mut LeanObject,
    mut v_x_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    v___x_2262_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_x_2258_, v_x_2259_, v_x_2260_, v_x_2261_);
    return v___x_2262_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(
    mut v_fst_2263_: *mut LeanObject,
    mut v_d_2264_: *mut LeanObject,
    mut v_x_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
    mut v___y_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
    mut v___y_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(
        v_fst_2263_,
        v_x_2265_,
        v_d_2264_,
        v___y_2266_,
        v___y_2267_,
        v___y_2268_,
        v___y_2269_,
        v___y_2270_,
        v___y_2271_,
        v___y_2272_,
        v___y_2273_,
        v___y_2274_,
    );
    return v___x_2276_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(
    mut v_fst_2277_: *mut LeanObject,
    mut v_d_2278_: *mut LeanObject,
    mut v_x_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2290_: *mut LeanObject = core::ptr::null_mut();
    v_res_2290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_2277_, v_d_2278_, v_x_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
    lean_dec(v___y_2288_);
    lean_dec_ref(v___y_2287_);
    lean_dec(v___y_2286_);
    lean_dec_ref(v___y_2285_);
    lean_dec(v___y_2284_);
    lean_dec_ref(v___y_2283_);
    lean_dec(v___y_2282_);
    lean_dec_ref(v___y_2281_);
    lean_dec(v___y_2280_);
    return v_res_2290_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(
    mut v_d_2291_: *mut LeanObject,
    mut v_e_2292_: *mut LeanObject,
    mut v_as_2293_: *mut LeanObject,
    mut v_sz_2294_: usize,
    mut v_i_2295_: usize,
    mut v_b_2296_: *mut LeanObject,
    mut v___y_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
    mut v___y_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2308_: u8 = 0;
    let mut v___y_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2316_: u8 = 0;
    let mut v___y_2317_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: u8 = 0;
    let mut v___y_2322_: u8 = 0;
    let mut v___y_2323_: u8 = 0;
    let mut v___y_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: u8 = 0;
    let mut v___y_2327_: u8 = 0;
    let mut v_contextDependent_2328_: u8 = 0;
    let mut v_contextDependent_2329_: u8 = 0;
    let mut v___y_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2332_: u8 = 0;
    let mut v___x_2333_: u8 = 0;
    let mut v___x_2334_: u8 = 0;
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2346_: u8 = 0;
    let mut v___y_2347_: u8 = 0;
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v_reuseFailAlloc_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v_result_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u8 = 0;
    let mut v_done_2359_: u8 = 0;
    let mut v_contextDependent_2360_: u8 = 0;
    let mut v_contextDependent_2361_: u8 = 0;
    let mut v_done_2362_: u8 = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: u8 = 0;
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___f_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut v_unused_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = lean_usize_dec_lt(v_i_2295_, v_sz_2294_);
                if v___x_2334_ == 0 {
                    lean_dec_ref(v_e_2292_);
                    lean_dec_ref(v_d_2291_);
                    v___x_2335_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2335_, 0, v_b_2296_);
                    return v___x_2335_;
                } else {
                    v_a_2336_ = lean_array_uget_borrowed(v_as_2293_, v_i_2295_);
                    v_fst_2337_ = lean_ctor_get(v_a_2336_, 0);
                    v_snd_2338_ = lean_ctor_get(v_a_2336_, 1);
                    v_snd_2339_ = lean_ctor_get(v_b_2296_, 1);
                    v_isSharedCheck_2388_ = (!lean_is_exclusive(v_b_2296_)) as u8;
                    if v_isSharedCheck_2388_ == 0 {
                        v_unused_2389_ = lean_ctor_get(v_b_2296_, 0);
                        lean_dec(v_unused_2389_);
                        v___x_2341_ = v_b_2296_;
                        v_isShared_2342_ = v_isSharedCheck_2388_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_2339_);
                        lean_dec(v_b_2296_);
                        v___x_2341_ = lean_box(0);
                        v_isShared_2342_ = v_isSharedCheck_2388_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2310_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2310_, 0, v___y_2309_);
                v___x_2311_ = lean_box((v___y_2308_) as usize);
                v___x_2312_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2312_, 0, v___x_2310_);
                lean_ctor_set(v___x_2312_, 1, v___x_2311_);
                v___x_2313_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2313_, 0, v___x_2312_);
                return v___x_2313_;
            }
            2 => {
                if v___y_2317_ == 0 {
                    v___y_2308_ = v___y_2316_;
                    v___y_2309_ = v___y_2315_;
                    state = 1;
                    continue;
                } else {
                    v___x_2318_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2315_);
                    v___y_2308_ = v___y_2316_;
                    v___y_2309_ = v___x_2318_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2323_ == 0 {
                    v___y_2315_ = v___y_2320_;
                    v___y_2316_ = v___y_2322_;
                    v___y_2317_ = v___y_2322_;
                    state = 2;
                    continue;
                } else {
                    v___y_2315_ = v___y_2320_;
                    v___y_2316_ = v___y_2322_;
                    v___y_2317_ = v___y_2321_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v___y_2326_ == 0 {
                    v___y_2308_ = v___y_2326_;
                    v___y_2309_ = v___y_2325_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v___y_2325_) == 0 {
                        v_contextDependent_2328_ = lean_ctor_get_uint8(v___y_2325_, 1 as u32);
                        v___y_2320_ = v___y_2325_;
                        v___y_2321_ = v___y_2327_;
                        v___y_2322_ = v___y_2326_;
                        v___y_2323_ = v_contextDependent_2328_;
                        state = 3;
                        continue;
                    } else {
                        v_contextDependent_2329_ = lean_ctor_get_uint8(
                            v___y_2325_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v___y_2320_ = v___y_2325_;
                        v___y_2321_ = v___y_2327_;
                        v___y_2322_ = v___y_2326_;
                        v___y_2323_ = v_contextDependent_2329_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2333_ = 0;
                v___y_2325_ = v___y_2331_;
                v___y_2326_ = v___y_2332_;
                v___y_2327_ = v___x_2333_;
                state = 4;
                continue;
            }
            6 => {
                v___x_2343_ = lean_box(0);
                v___x_2365_ = lean_unsigned_to_nat(0);
                v___x_2366_ = lean_nat_dec_eq(v_snd_2338_, v___x_2365_);
                if v___x_2366_ == 0 {
                    lean_inc_ref(v_d_2291_);
                    lean_inc(v_fst_2337_);
                    v___f_2367_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                    lean_closure_set(v___f_2367_, 0, v_fst_2337_);
                    lean_closure_set(v___f_2367_, 1, v_d_2291_);
                    lean_inc_ref(v_e_2292_);
                    v___x_2368_ = l_Lean_Meta_Sym_Simp_simpOverApplied(
                        v_e_2292_,
                        v_snd_2338_,
                        v___f_2367_,
                        v___y_2297_,
                        v___y_2298_,
                        v___y_2299_,
                        v___y_2300_,
                        v___y_2301_,
                        v___y_2302_,
                        v___y_2303_,
                        v___y_2304_,
                        v___y_2305_,
                    );
                    if lean_obj_tag(v___x_2368_) == 0 {
                        v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
                        lean_inc(v_a_2369_);
                        lean_dec_ref_known(v___x_2368_, 1);
                        v_result_2357_ = v_a_2369_;
                        state = 9;
                        continue;
                    } else {
                        lean_del_object(v___x_2341_);
                        lean_dec(v_snd_2339_);
                        lean_dec_ref(v_e_2292_);
                        lean_dec_ref(v_d_2291_);
                        v_a_2370_ = lean_ctor_get(v___x_2368_, 0);
                        v_isSharedCheck_2377_ = (!lean_is_exclusive(v___x_2368_)) as u8;
                        if v_isSharedCheck_2377_ == 0 {
                            v___x_2372_ = v___x_2368_;
                            v_isShared_2373_ = v_isSharedCheck_2377_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2370_);
                            lean_dec(v___x_2368_);
                            v___x_2372_ = lean_box(0);
                            v_isShared_2373_ = v_isSharedCheck_2377_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_inc_ref(v_d_2291_);
                    lean_inc_ref(v_e_2292_);
                    lean_inc(v_fst_2337_);
                    v___x_2378_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(
                        v_fst_2337_,
                        v_e_2292_,
                        v_d_2291_,
                        v___y_2297_,
                        v___y_2298_,
                        v___y_2299_,
                        v___y_2300_,
                        v___y_2301_,
                        v___y_2302_,
                        v___y_2303_,
                        v___y_2304_,
                        v___y_2305_,
                    );
                    if lean_obj_tag(v___x_2378_) == 0 {
                        v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
                        lean_inc(v_a_2379_);
                        lean_dec_ref_known(v___x_2378_, 1);
                        v_result_2357_ = v_a_2379_;
                        state = 9;
                        continue;
                    } else {
                        lean_del_object(v___x_2341_);
                        lean_dec(v_snd_2339_);
                        lean_dec_ref(v_e_2292_);
                        lean_dec_ref(v_d_2291_);
                        v_a_2380_ = lean_ctor_get(v___x_2378_, 0);
                        v_isSharedCheck_2387_ = (!lean_is_exclusive(v___x_2378_)) as u8;
                        if v_isSharedCheck_2387_ == 0 {
                            v___x_2382_ = v___x_2378_;
                            v_isShared_2383_ = v_isSharedCheck_2387_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2380_);
                            lean_dec(v___x_2378_);
                            v___x_2382_ = lean_box(0);
                            v_isShared_2383_ = v_isSharedCheck_2387_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_done_2346_ == 0 {
                    lean_dec_ref(v___y_2345_);
                    v___x_2348_ = lean_box((v___y_2347_) as usize);
                    if v_isShared_2342_ == 0 {
                        lean_ctor_set(v___x_2341_, 1, v___x_2348_);
                        lean_ctor_set(v___x_2341_, 0, v___x_2343_);
                        v___x_2350_ = v___x_2341_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2343_);
                        lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2348_);
                        v___x_2350_ = v_reuseFailAlloc_2354_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2341_);
                    lean_dec_ref(v_e_2292_);
                    lean_dec_ref(v_d_2291_);
                    v___x_2355_ = 0;
                    v___y_2325_ = v___y_2345_;
                    v___y_2326_ = v___y_2347_;
                    v___y_2327_ = v___x_2355_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_2351_ = 1usize;
                v___x_2352_ = lean_usize_add(v_i_2295_, v___x_2351_);
                v_i_2295_ = v___x_2352_;
                v_b_2296_ = v___x_2350_;
                state = 0;
                continue;
            }
            9 => {
                v___x_2358_ = (lean_unbox(v_snd_2339_) as u8);
                if v___x_2358_ == 0 {
                    lean_dec(v_snd_2339_);
                    if lean_obj_tag(v_result_2357_) == 0 {
                        v_done_2359_ = lean_ctor_get_uint8(v_result_2357_, 0 as u32);
                        v_contextDependent_2360_ = lean_ctor_get_uint8(v_result_2357_, 1 as u32);
                        v___y_2345_ = v_result_2357_;
                        v_done_2346_ = v_done_2359_;
                        v___y_2347_ = v_contextDependent_2360_;
                        state = 7;
                        continue;
                    } else {
                        lean_del_object(v___x_2341_);
                        lean_dec_ref(v_e_2292_);
                        lean_dec_ref(v_d_2291_);
                        v_contextDependent_2361_ = lean_ctor_get_uint8(
                            v_result_2357_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v___y_2331_ = v_result_2357_;
                        v___y_2332_ = v_contextDependent_2361_;
                        state = 5;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_result_2357_) == 0 {
                        v_done_2362_ = lean_ctor_get_uint8(v_result_2357_, 0 as u32);
                        v___x_2363_ = (lean_unbox(v_snd_2339_) as u8);
                        lean_dec(v_snd_2339_);
                        v___y_2345_ = v_result_2357_;
                        v_done_2346_ = v_done_2362_;
                        v___y_2347_ = v___x_2363_;
                        state = 7;
                        continue;
                    } else {
                        lean_del_object(v___x_2341_);
                        lean_dec_ref(v_e_2292_);
                        lean_dec_ref(v_d_2291_);
                        v___x_2364_ = (lean_unbox(v_snd_2339_) as u8);
                        lean_dec(v_snd_2339_);
                        v___y_2331_ = v_result_2357_;
                        v___y_2332_ = v___x_2364_;
                        state = 5;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_2373_ == 0 {
                    v___x_2375_ = v___x_2372_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
                    v___x_2375_ = v_reuseFailAlloc_2376_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2375_;
            }
            12 => {
                if v_isShared_2383_ == 0 {
                    v___x_2385_ = v___x_2382_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(
    mut v_d_2390_: *mut LeanObject,
    mut v_e_2391_: *mut LeanObject,
    mut v_as_2392_: *mut LeanObject,
    mut v_sz_2393_: *mut LeanObject,
    mut v_i_2394_: *mut LeanObject,
    mut v_b_2395_: *mut LeanObject,
    mut v___y_2396_: *mut LeanObject,
    mut v___y_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2406_: usize = 0;
    let mut v_i_boxed_2407_: usize = 0;
    let mut v_res_2408_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2406_ = lean_unbox_usize(v_sz_2393_);
    lean_dec(v_sz_2393_);
    v_i_boxed_2407_ = lean_unbox_usize(v_i_2394_);
    lean_dec(v_i_2394_);
    v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_2390_, v_e_2391_, v_as_2392_, v_sz_boxed_2406_, v_i_boxed_2407_, v_b_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
    lean_dec(v___y_2404_);
    lean_dec_ref(v___y_2403_);
    lean_dec(v___y_2402_);
    lean_dec_ref(v___y_2401_);
    lean_dec(v___y_2400_);
    lean_dec_ref(v___y_2399_);
    lean_dec(v___y_2398_);
    lean_dec_ref(v___y_2397_);
    lean_dec(v___y_2396_);
    lean_dec_ref(v_as_2392_);
    return v_res_2408_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorems_rewrite(
    mut v_thms_2413_: *mut LeanObject,
    mut v_d_2414_: *mut LeanObject,
    mut v_e_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
    mut v_a_2421_: *mut LeanObject,
    mut v_a_2422_: *mut LeanObject,
    mut v_a_2423_: *mut LeanObject,
    mut v_a_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2428_: usize = 0;
    let mut v___x_2429_: usize = 0;
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v_fst_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v_a_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2426_ =
                    l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_2413_, v_e_2415_);
                v___x_2427_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0;
                v_sz_2428_ = lean_array_size(v___x_2426_);
                v___x_2429_ = 0usize;
                v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_2414_, v_e_2415_, v___x_2426_, v_sz_2428_, v___x_2429_, v___x_2427_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
                lean_dec_ref(v___x_2426_);
                if lean_obj_tag(v___x_2430_) == 0 {
                    v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
                    v_isSharedCheck_2446_ = (!lean_is_exclusive(v___x_2430_)) as u8;
                    if v_isSharedCheck_2446_ == 0 {
                        v___x_2433_ = v___x_2430_;
                        v_isShared_2434_ = v_isSharedCheck_2446_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2431_);
                        lean_dec(v___x_2430_);
                        v___x_2433_ = lean_box(0);
                        v_isShared_2434_ = v_isSharedCheck_2446_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2447_ = lean_ctor_get(v___x_2430_, 0);
                    v_isSharedCheck_2454_ = (!lean_is_exclusive(v___x_2430_)) as u8;
                    if v_isSharedCheck_2454_ == 0 {
                        v___x_2449_ = v___x_2430_;
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2447_);
                        lean_dec(v___x_2430_);
                        v___x_2449_ = lean_box(0);
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2435_ = lean_ctor_get(v_a_2431_, 0);
                if lean_obj_tag(v_fst_2435_) == 0 {
                    v_snd_2436_ = lean_ctor_get(v_a_2431_, 1);
                    lean_inc(v_snd_2436_);
                    lean_dec(v_a_2431_);
                    v___x_2437_ = (lean_unbox(v_snd_2436_) as u8);
                    lean_dec(v_snd_2436_);
                    v___x_2438_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_2437_);
                    if v_isShared_2434_ == 0 {
                        lean_ctor_set(v___x_2433_, 0, v___x_2438_);
                        v___x_2440_ = v___x_2433_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
                        v___x_2440_ = v_reuseFailAlloc_2441_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2435_);
                    lean_dec(v_a_2431_);
                    v_val_2442_ = lean_ctor_get(v_fst_2435_, 0);
                    lean_inc(v_val_2442_);
                    lean_dec_ref_known(v_fst_2435_, 1);
                    if v_isShared_2434_ == 0 {
                        lean_ctor_set(v___x_2433_, 0, v_val_2442_);
                        v___x_2444_ = v___x_2433_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_val_2442_);
                        v___x_2444_ = v_reuseFailAlloc_2445_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2440_;
            }
            3 => {
                return v___x_2444_;
            }
            4 => {
                if v_isShared_2450_ == 0 {
                    v___x_2452_ = v___x_2449_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
                    v___x_2452_ = v_reuseFailAlloc_2453_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(
    mut v_thms_2455_: *mut LeanObject,
    mut v_d_2456_: *mut LeanObject,
    mut v_e_2457_: *mut LeanObject,
    mut v_a_2458_: *mut LeanObject,
    mut v_a_2459_: *mut LeanObject,
    mut v_a_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
    mut v_a_2462_: *mut LeanObject,
    mut v_a_2463_: *mut LeanObject,
    mut v_a_2464_: *mut LeanObject,
    mut v_a_2465_: *mut LeanObject,
    mut v_a_2466_: *mut LeanObject,
    mut v_a_2467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2468_: *mut LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(
        v_thms_2455_,
        v_d_2456_,
        v_e_2457_,
        v_a_2458_,
        v_a_2459_,
        v_a_2460_,
        v_a_2461_,
        v_a_2462_,
        v_a_2463_,
        v_a_2464_,
        v_a_2465_,
        v_a_2466_,
    );
    lean_dec(v_a_2466_);
    lean_dec_ref(v_a_2465_);
    lean_dec(v_a_2464_);
    lean_dec_ref(v_a_2463_);
    lean_dec(v_a_2462_);
    lean_dec_ref(v_a_2461_);
    lean_dec(v_a_2460_);
    lean_dec_ref(v_a_2459_);
    lean_dec(v_a_2458_);
    lean_dec_ref(v_thms_2455_);
    return v_res_2468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ACLt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ACLt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
}
