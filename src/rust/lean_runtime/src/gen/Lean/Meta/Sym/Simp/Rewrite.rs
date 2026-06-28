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
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(
    mut v_expr_1235_: *mut crate::leanh::LeanObject,
    mut v_pattern_1236_: *mut crate::leanh::LeanObject,
    mut v_us_1237_: *mut crate::leanh::LeanObject,
    mut v_args_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_levelParams_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_expr_1235_) == 4 {
                    v_us_1243_ = crate::leanh::lean_ctor_get(v_expr_1235_, 1);
                    if crate::leanh::lean_obj_tag(v_us_1243_) == 0 {
                        crate::leanh::lean_dec_ref(v_pattern_1236_);
                        v_declName_1244_ = crate::leanh::lean_ctor_get(v_expr_1235_, 0);
                        crate::leanh::lean_inc(v_declName_1244_);
                        crate::leanh::lean_dec_ref_known(v_expr_1235_, 2);
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
                v_levelParams_1240_ = crate::leanh::lean_ctor_get(v_pattern_1236_, 0);
                crate::leanh::lean_inc(v_levelParams_1240_);
                crate::leanh::lean_dec_ref(v_pattern_1236_);
                v___x_1241_ = l_Lean_Expr_instantiateLevelParams(
                    v_expr_1235_,
                    v_levelParams_1240_,
                    v_us_1237_,
                );
                crate::leanh::lean_dec_ref(v_expr_1235_);
                v___x_1242_ = l_Lean_mkAppN(v___x_1241_, v_args_1238_);
                return v___x_1242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue___boxed(
    mut v_expr_1247_: *mut crate::leanh::LeanObject,
    mut v_pattern_1248_: *mut crate::leanh::LeanObject,
    mut v_us_1249_: *mut crate::leanh::LeanObject,
    mut v_args_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(
        v_expr_1247_,
        v_pattern_1248_,
        v_us_1249_,
        v_args_1250_,
    );
    crate::leanh::lean_dec_ref(v_args_1250_);
    return v_res_1251_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(
    mut v_perm_1252_: u8,
    mut v_e_1253_: *mut crate::leanh::LeanObject,
    mut v_result_1254_: *mut crate::leanh::LeanObject,
    mut v_a_1255_: *mut crate::leanh::LeanObject,
    mut v_a_1256_: *mut crate::leanh::LeanObject,
    mut v_a_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_perm_1252_ == 0 {
        let mut v___x_1260_: u8 = 0;
        let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_result_1254_);
        crate::leanh::lean_dec_ref(v_e_1253_);
        v___x_1260_ = 1;
        v___x_1261_ = crate::leanh::lean_box((v___x_1260_) as usize);
        v___x_1262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1262_, 0, v___x_1261_);
        return v___x_1262_;
    } else {
        let mut v___x_1263_: u8 = 0;
        let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_perm_1265_: *mut crate::leanh::LeanObject,
    mut v_e_1266_: *mut crate::leanh::LeanObject,
    mut v_result_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_perm_boxed_1273_: u8 = 0;
    let mut v_res_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_perm_boxed_1273_ = (crate::leanh::lean_unbox(v_perm_1265_) as u8);
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
    crate::leanh::lean_dec(v_a_1271_);
    crate::leanh::lean_dec_ref(v_a_1270_);
    crate::leanh::lean_dec(v_a_1269_);
    crate::leanh::lean_dec_ref(v_a_1268_);
    return v_res_1274_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(
    mut v_l_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v_unused_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1278_ = lean_st_ref_get(v___y_1276_);
                v_mctx_1279_ = crate::leanh::lean_ctor_get(v___x_1278_, 0);
                crate::leanh::lean_inc_ref(v_mctx_1279_);
                crate::leanh::lean_dec(v___x_1278_);
                v___x_1280_ = lean_instantiate_level_mvars(v_mctx_1279_, v_l_1275_);
                v_fst_1281_ = crate::leanh::lean_ctor_get(v___x_1280_, 0);
                crate::leanh::lean_inc(v_fst_1281_);
                v_snd_1282_ = crate::leanh::lean_ctor_get(v___x_1280_, 1);
                crate::leanh::lean_inc(v_snd_1282_);
                crate::leanh::lean_dec_ref(v___x_1280_);
                v___x_1283_ = lean_st_ref_take(v___y_1276_);
                v_cache_1284_ = crate::leanh::lean_ctor_get(v___x_1283_, 1);
                v_zetaDeltaFVarIds_1285_ = crate::leanh::lean_ctor_get(v___x_1283_, 2);
                v_postponed_1286_ = crate::leanh::lean_ctor_get(v___x_1283_, 3);
                v_diag_1287_ = crate::leanh::lean_ctor_get(v___x_1283_, 4);
                v_isSharedCheck_1296_ = (!crate::leanh::lean_is_exclusive(v___x_1283_)) as u8;
                if v_isSharedCheck_1296_ == 0 {
                    v_unused_1297_ = crate::leanh::lean_ctor_get(v___x_1283_, 0);
                    crate::leanh::lean_dec(v_unused_1297_);
                    v___x_1289_ = v___x_1283_;
                    v_isShared_1290_ = v_isSharedCheck_1296_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1287_);
                    crate::leanh::lean_inc(v_postponed_1286_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1285_);
                    crate::leanh::lean_inc(v_cache_1284_);
                    crate::leanh::lean_dec(v___x_1283_);
                    v___x_1289_ = crate::leanh::lean_box(0);
                    v_isShared_1290_ = v_isSharedCheck_1296_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v_fst_1281_);
                    v___x_1292_ = v___x_1289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_fst_1281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_cache_1284_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1295_,
                        2,
                        v_zetaDeltaFVarIds_1285_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_postponed_1286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_diag_1287_);
                    v___x_1292_ = v_reuseFailAlloc_1295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1293_ = lean_st_ref_set(v___y_1276_, v___x_1292_);
                v___x_1294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1294_, 0, v_snd_1282_);
                return v___x_1294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg___boxed(
    mut v_l_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(
            v_l_1298_,
            v___y_1299_,
        );
    crate::leanh::lean_dec(v___y_1299_);
    return v_res_1301_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(
    mut v_l_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(
            v_l_1302_,
            v___y_1309_,
        );
    return v___x_1313_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___boxed(
    mut v_l_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1323_);
    crate::leanh::lean_dec_ref(v___y_1322_);
    crate::leanh::lean_dec(v___y_1321_);
    crate::leanh::lean_dec_ref(v___y_1320_);
    crate::leanh::lean_dec(v___y_1319_);
    crate::leanh::lean_dec_ref(v___y_1318_);
    crate::leanh::lean_dec(v___y_1317_);
    crate::leanh::lean_dec_ref(v___y_1316_);
    crate::leanh::lean_dec(v___y_1315_);
    return v_res_1325_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(
    mut v_k_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
    mut v___y_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1331_);
    crate::leanh::lean_inc_ref(v___y_1330_);
    crate::leanh::lean_inc(v___y_1329_);
    crate::leanh::lean_inc_ref(v___y_1328_);
    crate::leanh::lean_inc(v___y_1327_);
    v___x_1337_ = crate::leanh::lean_apply_10(
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
        crate::leanh::lean_box(0),
    );
    return v___x_1337_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(
    mut v_k_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1349_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_k_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
    crate::leanh::lean_dec(v___y_1343_);
    crate::leanh::lean_dec_ref(v___y_1342_);
    crate::leanh::lean_dec(v___y_1341_);
    crate::leanh::lean_dec_ref(v___y_1340_);
    crate::leanh::lean_dec(v___y_1339_);
    return v_res_1349_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(
    mut v_k_1350_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1351_: u8,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
    mut v___y_1353_: *mut crate::leanh::LeanObject,
    mut v___y_1354_: *mut crate::leanh::LeanObject,
    mut v___y_1355_: *mut crate::leanh::LeanObject,
    mut v___y_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1356_);
                crate::leanh::lean_inc_ref(v___y_1355_);
                crate::leanh::lean_inc(v___y_1354_);
                crate::leanh::lean_inc_ref(v___y_1353_);
                crate::leanh::lean_inc(v___y_1352_);
                v___f_1362_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                crate::leanh::lean_closure_set(v___f_1362_, 0, v_k_1350_);
                crate::leanh::lean_closure_set(v___f_1362_, 1, v___y_1352_);
                crate::leanh::lean_closure_set(v___f_1362_, 2, v___y_1353_);
                crate::leanh::lean_closure_set(v___f_1362_, 3, v___y_1354_);
                crate::leanh::lean_closure_set(v___f_1362_, 4, v___y_1355_);
                crate::leanh::lean_closure_set(v___f_1362_, 5, v___y_1356_);
                v___x_1363_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_1351_,
                    v___f_1362_,
                    v___y_1357_,
                    v___y_1358_,
                    v___y_1359_,
                    v___y_1360_,
                );
                if crate::leanh::lean_obj_tag(v___x_1363_) == 0 {
                    return v___x_1363_;
                } else {
                    v_a_1364_ = crate::leanh::lean_ctor_get(v___x_1363_, 0);
                    v_isSharedCheck_1371_ = (!crate::leanh::lean_is_exclusive(v___x_1363_)) as u8;
                    if v_isSharedCheck_1371_ == 0 {
                        v___x_1366_ = v___x_1363_;
                        v_isShared_1367_ = v_isSharedCheck_1371_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1364_);
                        crate::leanh::lean_dec(v___x_1363_);
                        v___x_1366_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
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
    mut v_k_1372_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_1384_: u8 = 0;
    let mut v_res_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1384_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_1373_) as u8);
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
    crate::leanh::lean_dec(v___y_1382_);
    crate::leanh::lean_dec_ref(v___y_1381_);
    crate::leanh::lean_dec(v___y_1380_);
    crate::leanh::lean_dec_ref(v___y_1379_);
    crate::leanh::lean_dec(v___y_1378_);
    crate::leanh::lean_dec_ref(v___y_1377_);
    crate::leanh::lean_dec(v___y_1376_);
    crate::leanh::lean_dec_ref(v___y_1375_);
    crate::leanh::lean_dec(v___y_1374_);
    return v_res_1385_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(
    mut v_00_u03b1_1386_: *mut crate::leanh::LeanObject,
    mut v_k_1387_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1388_: u8,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
    mut v___y_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
    mut v___y_1393_: *mut crate::leanh::LeanObject,
    mut v___y_1394_: *mut crate::leanh::LeanObject,
    mut v___y_1395_: *mut crate::leanh::LeanObject,
    mut v___y_1396_: *mut crate::leanh::LeanObject,
    mut v___y_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1400_: *mut crate::leanh::LeanObject,
    mut v_k_1401_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1402_: *mut crate::leanh::LeanObject,
    mut v___y_1403_: *mut crate::leanh::LeanObject,
    mut v___y_1404_: *mut crate::leanh::LeanObject,
    mut v___y_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_1413_: u8 = 0;
    let mut v_res_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1413_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_1402_) as u8);
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
    crate::leanh::lean_dec(v___y_1411_);
    crate::leanh::lean_dec_ref(v___y_1410_);
    crate::leanh::lean_dec(v___y_1409_);
    crate::leanh::lean_dec_ref(v___y_1408_);
    crate::leanh::lean_dec(v___y_1407_);
    crate::leanh::lean_dec_ref(v___y_1406_);
    crate::leanh::lean_dec(v___y_1405_);
    crate::leanh::lean_dec_ref(v___y_1404_);
    crate::leanh::lean_dec(v___y_1403_);
    return v_res_1414_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(
    mut v_x_1415_: *mut crate::leanh::LeanObject,
    mut v_x_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
    mut v___y_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1415_) == 0 {
                    v___x_1427_ = l_List_reverse___redArg(v_x_1416_);
                    v___x_1428_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1428_, 0, v___x_1427_);
                    return v___x_1428_;
                } else {
                    v_head_1429_ = crate::leanh::lean_ctor_get(v_x_1415_, 0);
                    v_tail_1430_ = crate::leanh::lean_ctor_get(v_x_1415_, 1);
                    v_isSharedCheck_1440_ = (!crate::leanh::lean_is_exclusive(v_x_1415_)) as u8;
                    if v_isSharedCheck_1440_ == 0 {
                        v___x_1432_ = v_x_1415_;
                        v_isShared_1433_ = v_isSharedCheck_1440_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1430_);
                        crate::leanh::lean_inc(v_head_1429_);
                        crate::leanh::lean_dec(v_x_1415_);
                        v___x_1432_ = crate::leanh::lean_box(0);
                        v_isShared_1433_ = v_isSharedCheck_1440_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1434_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_1429_, v___y_1423_);
                v_a_1435_ = crate::leanh::lean_ctor_get(v___x_1434_, 0);
                crate::leanh::lean_inc(v_a_1435_);
                crate::leanh::lean_dec_ref(v___x_1434_);
                if v_isShared_1433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1432_, 1, v_x_1416_);
                    crate::leanh::lean_ctor_set(v___x_1432_, 0, v_a_1435_);
                    v___x_1437_ = v___x_1432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1439_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_x_1416_);
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
    mut v_x_1441_: *mut crate::leanh::LeanObject,
    mut v_x_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1451_);
    crate::leanh::lean_dec_ref(v___y_1450_);
    crate::leanh::lean_dec(v___y_1449_);
    crate::leanh::lean_dec_ref(v___y_1448_);
    crate::leanh::lean_dec(v___y_1447_);
    crate::leanh::lean_dec_ref(v___y_1446_);
    crate::leanh::lean_dec(v___y_1445_);
    crate::leanh::lean_dec_ref(v___y_1444_);
    crate::leanh::lean_dec(v___y_1443_);
    return v_res_1453_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(
    mut v_x_1454_: *mut crate::leanh::LeanObject,
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v_x_1456_: *mut crate::leanh::LeanObject,
    mut v_x_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1462_: u8 = 0;
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1458_ = crate::leanh::lean_ctor_get(v_x_1454_, 0);
                v_vs_1459_ = crate::leanh::lean_ctor_get(v_x_1454_, 1);
                v_isSharedCheck_1483_ = (!crate::leanh::lean_is_exclusive(v_x_1454_)) as u8;
                if v_isSharedCheck_1483_ == 0 {
                    v___x_1461_ = v_x_1454_;
                    v_isShared_1462_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1459_);
                    crate::leanh::lean_inc(v_ks_1458_);
                    crate::leanh::lean_dec(v_x_1454_);
                    v___x_1461_ = crate::leanh::lean_box(0);
                    v_isShared_1462_ = v_isSharedCheck_1483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1463_ = lean_array_get_size(v_ks_1458_);
                v___x_1464_ = lean_nat_dec_lt(v_x_1455_, v___x_1463_);
                if v___x_1464_ == 0 {
                    crate::leanh::lean_dec(v_x_1455_);
                    v___x_1465_ = lean_array_push(v_ks_1458_, v_x_1456_);
                    v___x_1466_ = lean_array_push(v_vs_1459_, v_x_1457_);
                    if v_isShared_1462_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1461_, 1, v___x_1466_);
                        crate::leanh::lean_ctor_set(v___x_1461_, 0, v___x_1465_);
                        v___x_1468_ = v___x_1461_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1469_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1465_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1466_);
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
                            v_reuseFailAlloc_1477_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_ks_1458_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_vs_1459_);
                            v___x_1473_ = v_reuseFailAlloc_1477_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1478_ = lean_array_fset(v_ks_1458_, v_x_1455_, v_x_1456_);
                        v___x_1479_ = lean_array_fset(v_vs_1459_, v_x_1455_, v_x_1457_);
                        crate::leanh::lean_dec(v_x_1455_);
                        if v_isShared_1462_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1461_, 1, v___x_1479_);
                            crate::leanh::lean_ctor_set(v___x_1461_, 0, v___x_1478_);
                            v___x_1481_ = v___x_1461_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1482_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1478_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1479_);
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
                v___x_1474_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1475_ = lean_nat_add(v_x_1455_, v___x_1474_);
                crate::leanh::lean_dec(v_x_1455_);
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
    mut v_n_1484_: *mut crate::leanh::LeanObject,
    mut v_k_1485_: *mut crate::leanh::LeanObject,
    mut v_v_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = crate::leanh::lean_unsigned_to_nat(0);
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
    v___x_1493_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0);
    v___x_1494_ = lean_usize_sub(v___x_1493_, v___x_1492_);
    return v___x_1494_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1495_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(
    mut v_x_1496_: *mut crate::leanh::LeanObject,
    mut v_x_1497_: usize,
    mut v_x_1498_: usize,
    mut v_x_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: usize = 0;
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: usize = 0;
    let mut v___x_1505_: usize = 0;
    let mut v_j_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v_v_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1532_: u8 = 0;
    let mut v_node_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: usize = 0;
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v_unused_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: u8 = 0;
    let mut v_ks_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: usize = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: u8 = 0;
    let mut v_reuseFailAlloc_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1496_) == 0 {
                    v_es_1501_ = crate::leanh::lean_ctor_get(v_x_1496_, 0);
                    v___x_1502_ = 5usize;
                    v___x_1503_ = 1usize;
                    v___x_1504_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1);
                    v___x_1505_ = lean_usize_land(v_x_1497_, v___x_1504_);
                    v_j_1506_ = lean_usize_to_nat(v___x_1505_);
                    v___x_1507_ = lean_array_get_size(v_es_1501_);
                    v___x_1508_ = lean_nat_dec_lt(v_j_1506_, v___x_1507_);
                    if v___x_1508_ == 0 {
                        crate::leanh::lean_dec(v_j_1506_);
                        crate::leanh::lean_dec(v_x_1500_);
                        crate::leanh::lean_dec(v_x_1499_);
                        return v_x_1496_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1501_);
                        v_isSharedCheck_1545_ = (!crate::leanh::lean_is_exclusive(v_x_1496_)) as u8;
                        if v_isSharedCheck_1545_ == 0 {
                            v_unused_1546_ = crate::leanh::lean_ctor_get(v_x_1496_, 0);
                            crate::leanh::lean_dec(v_unused_1546_);
                            v___x_1510_ = v_x_1496_;
                            v_isShared_1511_ = v_isSharedCheck_1545_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1496_);
                            v___x_1510_ = crate::leanh::lean_box(0);
                            v_isShared_1511_ = v_isSharedCheck_1545_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1547_ = crate::leanh::lean_ctor_get(v_x_1496_, 0);
                    v_vs_1548_ = crate::leanh::lean_ctor_get(v_x_1496_, 1);
                    v_isSharedCheck_1568_ = (!crate::leanh::lean_is_exclusive(v_x_1496_)) as u8;
                    if v_isSharedCheck_1568_ == 0 {
                        v___x_1550_ = v_x_1496_;
                        v_isShared_1551_ = v_isSharedCheck_1568_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1548_);
                        crate::leanh::lean_inc(v_ks_1547_);
                        crate::leanh::lean_dec(v_x_1496_);
                        v___x_1550_ = crate::leanh::lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1568_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1512_ = lean_array_fget(v_es_1501_, v_j_1506_);
                v___x_1513_ = crate::leanh::lean_box(0);
                v_xs_x27_1514_ = lean_array_fset(v_es_1501_, v_j_1506_, v___x_1513_);
                match crate::leanh::lean_obj_tag(v_v_1512_) {
                    0 => {
                        v_key_1521_ = crate::leanh::lean_ctor_get(v_v_1512_, 0);
                        v_val_1522_ = crate::leanh::lean_ctor_get(v_v_1512_, 1);
                        v_isSharedCheck_1532_ = (!crate::leanh::lean_is_exclusive(v_v_1512_)) as u8;
                        if v_isSharedCheck_1532_ == 0 {
                            v___x_1524_ = v_v_1512_;
                            v_isShared_1525_ = v_isSharedCheck_1532_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1522_);
                            crate::leanh::lean_inc(v_key_1521_);
                            crate::leanh::lean_dec(v_v_1512_);
                            v___x_1524_ = crate::leanh::lean_box(0);
                            v_isShared_1525_ = v_isSharedCheck_1532_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1533_ = crate::leanh::lean_ctor_get(v_v_1512_, 0);
                        v_isSharedCheck_1543_ = (!crate::leanh::lean_is_exclusive(v_v_1512_)) as u8;
                        if v_isSharedCheck_1543_ == 0 {
                            v___x_1535_ = v_v_1512_;
                            v_isShared_1536_ = v_isSharedCheck_1543_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1533_);
                            crate::leanh::lean_dec(v_v_1512_);
                            v___x_1535_ = crate::leanh::lean_box(0);
                            v_isShared_1536_ = v_isSharedCheck_1543_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1544_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1544_, 0, v_x_1499_);
                        crate::leanh::lean_ctor_set(v___x_1544_, 1, v_x_1500_);
                        v___y_1516_ = v___x_1544_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1517_ = lean_array_fset(v_xs_x27_1514_, v_j_1506_, v___y_1516_);
                crate::leanh::lean_dec(v_j_1506_);
                if v_isShared_1511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1517_);
                    v___x_1519_ = v___x_1510_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
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
                    crate::leanh::lean_del_object(v___x_1524_);
                    v___x_1527_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1521_,
                        v_val_1522_,
                        v_x_1499_,
                        v_x_1500_,
                    );
                    v___x_1528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1527_);
                    v___y_1516_ = v___x_1528_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1522_);
                    crate::leanh::lean_dec(v_key_1521_);
                    if v_isShared_1525_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1524_, 1, v_x_1500_);
                        crate::leanh::lean_ctor_set(v___x_1524_, 0, v_x_1499_);
                        v___x_1530_ = v___x_1524_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_x_1499_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_x_1500_);
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
                    crate::leanh::lean_ctor_set(v___x_1535_, 0, v___x_1539_);
                    v___x_1541_ = v___x_1535_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
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
                    v_reuseFailAlloc_1567_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_ks_1547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_vs_1548_);
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
                    v___x_1565_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1566_ = lean_nat_dec_lt(v___x_1564_, v___x_1565_);
                    crate::leanh::lean_dec(v___x_1564_);
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
                    v_ks_1557_ = crate::leanh::lean_ctor_get(v_newNode_1554_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1557_);
                    v_vs_1558_ = crate::leanh::lean_ctor_get(v_newNode_1554_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1558_);
                    crate::leanh::lean_dec_ref(v_newNode_1554_);
                    v___x_1559_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1560_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2);
                    v___x_1561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_x_1498_, v_ks_1557_, v_vs_1558_, v___x_1559_, v___x_1560_);
                    crate::leanh::lean_dec_ref(v_vs_1558_);
                    crate::leanh::lean_dec_ref(v_ks_1557_);
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
    mut v_keys_1570_: *mut crate::leanh::LeanObject,
    mut v_vals_1571_: *mut crate::leanh::LeanObject,
    mut v_i_1572_: *mut crate::leanh::LeanObject,
    mut v_entries_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v_k_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u64 = 0;
    let mut v_h_1579_: usize = 0;
    let mut v___x_1580_: usize = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1584_: usize = 0;
    let mut v_h_1585_: usize = 0;
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1574_ = lean_array_get_size(v_keys_1570_);
                v___x_1575_ = lean_nat_dec_lt(v_i_1572_, v___x_1574_);
                if v___x_1575_ == 0 {
                    crate::leanh::lean_dec(v_i_1572_);
                    return v_entries_1573_;
                } else {
                    v_k_1576_ = lean_array_fget_borrowed(v_keys_1570_, v_i_1572_);
                    v_v_1577_ = lean_array_fget_borrowed(v_vals_1571_, v_i_1572_);
                    v___x_1578_ = l_Lean_instHashableMVarId_hash(v_k_1576_);
                    v_h_1579_ = lean_uint64_to_usize(v___x_1578_);
                    v___x_1580_ = 5usize;
                    v___x_1581_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1582_ = 1usize;
                    v___x_1583_ = lean_usize_sub(v_depth_1569_, v___x_1582_);
                    v___x_1584_ = lean_usize_mul(v___x_1580_, v___x_1583_);
                    v_h_1585_ = lean_usize_shift_right(v_h_1579_, v___x_1584_);
                    v___x_1586_ = lean_nat_add(v_i_1572_, v___x_1581_);
                    crate::leanh::lean_dec(v_i_1572_);
                    crate::leanh::lean_inc(v_v_1577_);
                    crate::leanh::lean_inc(v_k_1576_);
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
    mut v_depth_1589_: *mut crate::leanh::LeanObject,
    mut v_keys_1590_: *mut crate::leanh::LeanObject,
    mut v_vals_1591_: *mut crate::leanh::LeanObject,
    mut v_i_1592_: *mut crate::leanh::LeanObject,
    mut v_entries_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1594_: usize = 0;
    let mut v_res_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1594_ = crate::leanh::lean_unbox_usize(v_depth_1589_);
    crate::leanh::lean_dec(v_depth_1589_);
    v_res_1595_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_boxed_1594_, v_keys_1590_, v_vals_1591_, v_i_1592_, v_entries_1593_);
    crate::leanh::lean_dec_ref(v_vals_1591_);
    crate::leanh::lean_dec_ref(v_keys_1590_);
    return v_res_1595_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___boxed(
    mut v_x_1596_: *mut crate::leanh::LeanObject,
    mut v_x_1597_: *mut crate::leanh::LeanObject,
    mut v_x_1598_: *mut crate::leanh::LeanObject,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
    mut v_x_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_34068__boxed_1601_: usize = 0;
    let mut v_x_34069__boxed_1602_: usize = 0;
    let mut v_res_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_34068__boxed_1601_ = crate::leanh::lean_unbox_usize(v_x_1597_);
    crate::leanh::lean_dec(v_x_1597_);
    v_x_34069__boxed_1602_ = crate::leanh::lean_unbox_usize(v_x_1598_);
    crate::leanh::lean_dec(v_x_1598_);
    v_res_1603_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_1596_, v_x_34068__boxed_1601_, v_x_34069__boxed_1602_, v_x_1599_, v_x_1600_);
    return v_res_1603_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(
    mut v_x_1604_: *mut crate::leanh::LeanObject,
    mut v_x_1605_: *mut crate::leanh::LeanObject,
    mut v_x_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: u64 = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: usize = 0;
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = l_Lean_instHashableMVarId_hash(v_x_1605_);
    v___x_1608_ = lean_uint64_to_usize(v___x_1607_);
    v___x_1609_ = 1usize;
    v___x_1610_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_1604_, v___x_1608_, v___x_1609_, v_x_1605_, v_x_1606_);
    return v___x_1610_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(
    mut v_mvarId_1611_: *mut crate::leanh::LeanObject,
    mut v_val_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v_depth_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1636_: u8 = 0;
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut v_isSharedCheck_1648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1615_ = lean_st_ref_take(v___y_1613_);
                v_mctx_1616_ = crate::leanh::lean_ctor_get(v___x_1615_, 0);
                v_cache_1617_ = crate::leanh::lean_ctor_get(v___x_1615_, 1);
                v_zetaDeltaFVarIds_1618_ = crate::leanh::lean_ctor_get(v___x_1615_, 2);
                v_postponed_1619_ = crate::leanh::lean_ctor_get(v___x_1615_, 3);
                v_diag_1620_ = crate::leanh::lean_ctor_get(v___x_1615_, 4);
                v_isSharedCheck_1648_ = (!crate::leanh::lean_is_exclusive(v___x_1615_)) as u8;
                if v_isSharedCheck_1648_ == 0 {
                    v___x_1622_ = v___x_1615_;
                    v_isShared_1623_ = v_isSharedCheck_1648_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1620_);
                    crate::leanh::lean_inc(v_postponed_1619_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1618_);
                    crate::leanh::lean_inc(v_cache_1617_);
                    crate::leanh::lean_inc(v_mctx_1616_);
                    crate::leanh::lean_dec(v___x_1615_);
                    v___x_1622_ = crate::leanh::lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1648_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1624_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 0);
                v_levelAssignDepth_1625_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 1);
                v_lmvarCounter_1626_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 2);
                v_mvarCounter_1627_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 3);
                v_lDecls_1628_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 4);
                v_decls_1629_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 5);
                v_userNames_1630_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 6);
                v_lAssignment_1631_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 7);
                v_eAssignment_1632_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 8);
                v_dAssignment_1633_ = crate::leanh::lean_ctor_get(v_mctx_1616_, 9);
                v_isSharedCheck_1647_ = (!crate::leanh::lean_is_exclusive(v_mctx_1616_)) as u8;
                if v_isSharedCheck_1647_ == 0 {
                    v___x_1635_ = v_mctx_1616_;
                    v_isShared_1636_ = v_isSharedCheck_1647_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1633_);
                    crate::leanh::lean_inc(v_eAssignment_1632_);
                    crate::leanh::lean_inc(v_lAssignment_1631_);
                    crate::leanh::lean_inc(v_userNames_1630_);
                    crate::leanh::lean_inc(v_decls_1629_);
                    crate::leanh::lean_inc(v_lDecls_1628_);
                    crate::leanh::lean_inc(v_mvarCounter_1627_);
                    crate::leanh::lean_inc(v_lmvarCounter_1626_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1625_);
                    crate::leanh::lean_inc(v_depth_1624_);
                    crate::leanh::lean_dec(v_mctx_1616_);
                    v___x_1635_ = crate::leanh::lean_box(0);
                    v_isShared_1636_ = v_isSharedCheck_1647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1637_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_1632_, v_mvarId_1611_, v_val_1612_);
                if v_isShared_1636_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1635_, 8, v___x_1637_);
                    v___x_1639_ = v___x_1635_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_depth_1624_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1646_,
                        1,
                        v_levelAssignDepth_1625_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_lmvarCounter_1626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_mvarCounter_1627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_lDecls_1628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 5, v_decls_1629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 6, v_userNames_1630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 7, v_lAssignment_1631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 8, v___x_1637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 9, v_dAssignment_1633_);
                    v___x_1639_ = v_reuseFailAlloc_1646_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1623_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1622_, 0, v___x_1639_);
                    v___x_1641_ = v___x_1622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_cache_1617_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1645_,
                        2,
                        v_zetaDeltaFVarIds_1618_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_postponed_1619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_diag_1620_);
                    v___x_1641_ = v_reuseFailAlloc_1645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1642_ = lean_st_ref_set(v___y_1613_, v___x_1641_);
                v___x_1643_ = crate::leanh::lean_box(0);
                v___x_1644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1644_, 0, v___x_1643_);
                return v___x_1644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(
    mut v_mvarId_1649_: *mut crate::leanh::LeanObject,
    mut v_val_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1653_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(
        v_mvarId_1649_,
        v_val_1650_,
        v___y_1651_,
    );
    crate::leanh::lean_dec(v___y_1651_);
    return v_res_1653_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(
    mut v_keys_1654_: *mut crate::leanh::LeanObject,
    mut v_i_1655_: *mut crate::leanh::LeanObject,
    mut v_k_1656_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    let mut v_k_x27_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1657_ = lean_array_get_size(v_keys_1654_);
                v___x_1658_ = lean_nat_dec_lt(v_i_1655_, v___x_1657_);
                if v___x_1658_ == 0 {
                    crate::leanh::lean_dec(v_i_1655_);
                    return v___x_1658_;
                } else {
                    v_k_x27_1659_ = lean_array_fget_borrowed(v_keys_1654_, v_i_1655_);
                    v___x_1660_ = l_Lean_instBEqMVarId_beq(v_k_1656_, v_k_x27_1659_);
                    if v___x_1660_ == 0 {
                        v___x_1661_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1662_ = lean_nat_add(v_i_1655_, v___x_1661_);
                        crate::leanh::lean_dec(v_i_1655_);
                        v_i_1655_ = v___x_1662_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1655_);
                        return v___x_1660_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_keys_1664_: *mut crate::leanh::LeanObject,
    mut v_i_1665_: *mut crate::leanh::LeanObject,
    mut v_k_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1667_: u8 = 0;
    let mut v_r_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1667_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_1664_, v_i_1665_, v_k_1666_);
    crate::leanh::lean_dec(v_k_1666_);
    crate::leanh::lean_dec_ref(v_keys_1664_);
    v_r_1668_ = crate::leanh::lean_box((v_res_1667_) as usize);
    return v_r_1668_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(
    mut v_x_1669_: *mut crate::leanh::LeanObject,
    mut v_x_1670_: usize,
    mut v_x_1671_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: usize = 0;
    let mut v_j_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v_node_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: usize = 0;
    let mut v___x_1684_: u8 = 0;
    let mut v_ks_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1669_) == 0 {
                    v_es_1672_ = crate::leanh::lean_ctor_get(v_x_1669_, 0);
                    v___x_1673_ = crate::leanh::lean_box(2);
                    v___x_1674_ = 5usize;
                    v___x_1675_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1);
                    v___x_1676_ = lean_usize_land(v_x_1670_, v___x_1675_);
                    v_j_1677_ = lean_usize_to_nat(v___x_1676_);
                    v___x_1678_ = lean_array_get_borrowed(v___x_1673_, v_es_1672_, v_j_1677_);
                    crate::leanh::lean_dec(v_j_1677_);
                    match crate::leanh::lean_obj_tag(v___x_1678_) {
                        0 => {
                            v_key_1679_ = crate::leanh::lean_ctor_get(v___x_1678_, 0);
                            v___x_1680_ = l_Lean_instBEqMVarId_beq(v_x_1671_, v_key_1679_);
                            return v___x_1680_;
                        }
                        1 => {
                            v_node_1681_ = crate::leanh::lean_ctor_get(v___x_1678_, 0);
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
                    v_ks_1685_ = crate::leanh::lean_ctor_get(v_x_1669_, 0);
                    v___x_1686_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1687_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_ks_1685_, v___x_1686_, v_x_1671_);
                    return v___x_1687_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_1688_: *mut crate::leanh::LeanObject,
    mut v_x_1689_: *mut crate::leanh::LeanObject,
    mut v_x_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_34306__boxed_1691_: usize = 0;
    let mut v_res_1692_: u8 = 0;
    let mut v_r_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_34306__boxed_1691_ = crate::leanh::lean_unbox_usize(v_x_1689_);
    crate::leanh::lean_dec(v_x_1689_);
    v_res_1692_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_1688_, v_x_34306__boxed_1691_, v_x_1690_);
    crate::leanh::lean_dec(v_x_1690_);
    crate::leanh::lean_dec_ref(v_x_1688_);
    v_r_1693_ = crate::leanh::lean_box((v_res_1692_) as usize);
    return v_r_1693_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(
    mut v_x_1694_: *mut crate::leanh::LeanObject,
    mut v_x_1695_: *mut crate::leanh::LeanObject,
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
    mut v_x_1699_: *mut crate::leanh::LeanObject,
    mut v_x_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1701_: u8 = 0;
    let mut v_r_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_1699_, v_x_1700_);
    crate::leanh::lean_dec(v_x_1700_);
    crate::leanh::lean_dec_ref(v_x_1699_);
    v_r_1702_ = crate::leanh::lean_box((v_res_1701_) as usize);
    return v_r_1702_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(
    mut v_mvarId_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: u8 = 0;
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = lean_st_ref_get(v___y_1704_);
    v_mctx_1707_ = crate::leanh::lean_ctor_get(v___x_1706_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1707_);
    crate::leanh::lean_dec(v___x_1706_);
    v_eAssignment_1708_ = crate::leanh::lean_ctor_get(v_mctx_1707_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_1708_);
    crate::leanh::lean_dec_ref(v_mctx_1707_);
    v___x_1709_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_eAssignment_1708_, v_mvarId_1703_);
    crate::leanh::lean_dec_ref(v_eAssignment_1708_);
    v___x_1710_ = crate::leanh::lean_box((v___x_1709_) as usize);
    v___x_1711_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1711_, 0, v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(
    mut v_mvarId_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(
            v_mvarId_1712_,
            v___y_1713_,
        );
    crate::leanh::lean_dec(v___y_1713_);
    crate::leanh::lean_dec(v_mvarId_1712_);
    return v_res_1715_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(
    mut v_upperBound_1716_: *mut crate::leanh::LeanObject,
    mut v_d_1717_: *mut crate::leanh::LeanObject,
    mut v_a_1718_: *mut crate::leanh::LeanObject,
    mut v_b_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
    mut v___y_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_fst_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1745_: u8 = 0;
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___y_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v_contextDependent_1775_: u8 = 0;
    let mut v_proof_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_1777_: u8 = 0;
    let mut v___y_1779_: u8 = 0;
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut v_a_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1798_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut v___x_1803_: u8 = 0;
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v_a_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_a_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut v_a_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1841_: u8 = 0;
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut v___x_1846_: u8 = 0;
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut v_unused_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1735_ = lean_nat_dec_lt(v_a_1718_, v_upperBound_1716_);
                if v___x_1735_ == 0 {
                    crate::leanh::lean_dec(v_a_1718_);
                    crate::leanh::lean_dec_ref(v_d_1717_);
                    v___x_1736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1736_, 0, v_b_1719_);
                    return v___x_1736_;
                } else {
                    v_snd_1737_ = crate::leanh::lean_ctor_get(v_b_1719_, 1);
                    v_isSharedCheck_1871_ = (!crate::leanh::lean_is_exclusive(v_b_1719_)) as u8;
                    if v_isSharedCheck_1871_ == 0 {
                        v_unused_1872_ = crate::leanh::lean_ctor_get(v_b_1719_, 0);
                        crate::leanh::lean_dec(v_unused_1872_);
                        v___x_1739_ = v_b_1719_;
                        v_isShared_1740_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1737_);
                        crate::leanh::lean_dec(v_b_1719_);
                        v___x_1739_ = crate::leanh::lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1732_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1733_ = lean_nat_add(v_a_1718_, v___x_1732_);
                crate::leanh::lean_dec(v_a_1718_);
                v_a_1718_ = v___x_1733_;
                v_b_1719_ = v_a_1731_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_1741_ = crate::leanh::lean_ctor_get(v_snd_1737_, 0);
                v_snd_1742_ = crate::leanh::lean_ctor_get(v_snd_1737_, 1);
                v_isSharedCheck_1870_ = (!crate::leanh::lean_is_exclusive(v_snd_1737_)) as u8;
                if v_isSharedCheck_1870_ == 0 {
                    v___x_1744_ = v_snd_1737_;
                    v_isShared_1745_ = v_isSharedCheck_1870_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1742_);
                    crate::leanh::lean_inc(v_fst_1741_);
                    crate::leanh::lean_dec(v_snd_1737_);
                    v___x_1744_ = crate::leanh::lean_box(0);
                    v_isShared_1745_ = v_isSharedCheck_1870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1746_ = crate::leanh::lean_box(0);
                v___x_1747_ = lean_array_fget_borrowed(v_fst_1741_, v_a_1718_);
                if crate::leanh::lean_obj_tag(v___x_1747_) == 2 {
                    v_mvarId_1748_ = crate::leanh::lean_ctor_get(v___x_1747_, 0);
                    v___x_1749_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_1748_, v___y_1726_);
                    if crate::leanh::lean_obj_tag(v___x_1749_) == 0 {
                        v_a_1750_ = crate::leanh::lean_ctor_get(v___x_1749_, 0);
                        crate::leanh::lean_inc(v_a_1750_);
                        crate::leanh::lean_dec_ref_known(v___x_1749_, 1);
                        v___x_1751_ = (crate::leanh::lean_unbox(v_a_1750_) as u8);
                        crate::leanh::lean_dec(v_a_1750_);
                        if v___x_1751_ == 0 {
                            crate::leanh::lean_inc(v_mvarId_1748_);
                            v___x_1752_ = l_Lean_MVarId_getDecl(
                                v_mvarId_1748_,
                                v___y_1725_,
                                v___y_1726_,
                                v___y_1727_,
                                v___y_1728_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1752_) == 0 {
                                v_a_1753_ = crate::leanh::lean_ctor_get(v___x_1752_, 0);
                                crate::leanh::lean_inc(v_a_1753_);
                                crate::leanh::lean_dec_ref_known(v___x_1752_, 1);
                                v_type_1754_ = crate::leanh::lean_ctor_get(v_a_1753_, 2);
                                crate::leanh::lean_inc_ref(v_type_1754_);
                                crate::leanh::lean_dec(v_a_1753_);
                                crate::leanh::lean_inc_ref(v_d_1717_);
                                crate::leanh::lean_inc(v___y_1728_);
                                crate::leanh::lean_inc_ref(v___y_1727_);
                                crate::leanh::lean_inc(v___y_1726_);
                                crate::leanh::lean_inc_ref(v___y_1725_);
                                crate::leanh::lean_inc(v___y_1724_);
                                crate::leanh::lean_inc_ref(v___y_1723_);
                                crate::leanh::lean_inc(v___y_1722_);
                                crate::leanh::lean_inc_ref(v___y_1721_);
                                crate::leanh::lean_inc(v___y_1720_);
                                v___x_1755_ = crate::leanh::lean_apply_11(
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
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_1755_) == 0 {
                                    v_a_1756_ = crate::leanh::lean_ctor_get(v___x_1755_, 0);
                                    v_isSharedCheck_1804_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1755_)) as u8;
                                    if v_isSharedCheck_1804_ == 0 {
                                        v___x_1758_ = v___x_1755_;
                                        v_isShared_1759_ = v_isSharedCheck_1804_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1756_);
                                        crate::leanh::lean_dec(v___x_1755_);
                                        v___x_1758_ = crate::leanh::lean_box(0);
                                        v_isShared_1759_ = v_isSharedCheck_1804_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_1744_);
                                    crate::leanh::lean_dec(v_snd_1742_);
                                    crate::leanh::lean_dec(v_fst_1741_);
                                    crate::leanh::lean_del_object(v___x_1739_);
                                    crate::leanh::lean_dec(v_a_1718_);
                                    crate::leanh::lean_dec_ref(v_d_1717_);
                                    v_a_1805_ = crate::leanh::lean_ctor_get(v___x_1755_, 0);
                                    v_isSharedCheck_1812_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1755_)) as u8;
                                    if v_isSharedCheck_1812_ == 0 {
                                        v___x_1807_ = v___x_1755_;
                                        v_isShared_1808_ = v_isSharedCheck_1812_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1805_);
                                        crate::leanh::lean_dec(v___x_1755_);
                                        v___x_1807_ = crate::leanh::lean_box(0);
                                        v_isShared_1808_ = v_isSharedCheck_1812_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1744_);
                                crate::leanh::lean_dec(v_snd_1742_);
                                crate::leanh::lean_dec(v_fst_1741_);
                                crate::leanh::lean_del_object(v___x_1739_);
                                crate::leanh::lean_dec(v_a_1718_);
                                crate::leanh::lean_dec_ref(v_d_1717_);
                                v_a_1813_ = crate::leanh::lean_ctor_get(v___x_1752_, 0);
                                v_isSharedCheck_1820_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1752_)) as u8;
                                if v_isSharedCheck_1820_ == 0 {
                                    v___x_1815_ = v___x_1752_;
                                    v_isShared_1816_ = v_isSharedCheck_1820_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1813_);
                                    crate::leanh::lean_dec(v___x_1752_);
                                    v___x_1815_ = crate::leanh::lean_box(0);
                                    v_isShared_1816_ = v_isSharedCheck_1820_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v___x_1747_);
                            v___x_1821_ = l_Lean_Meta_Sym_instantiateMVarsS(
                                v___x_1747_,
                                v___y_1723_,
                                v___y_1724_,
                                v___y_1725_,
                                v___y_1726_,
                                v___y_1727_,
                                v___y_1728_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1821_) == 0 {
                                v_a_1822_ = crate::leanh::lean_ctor_get(v___x_1821_, 0);
                                crate::leanh::lean_inc(v_a_1822_);
                                crate::leanh::lean_dec_ref_known(v___x_1821_, 1);
                                v___x_1823_ = lean_array_fset(v_fst_1741_, v_a_1718_, v_a_1822_);
                                if v_isShared_1745_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1744_, 0, v___x_1823_);
                                    v___x_1825_ = v___x_1744_;
                                    state = 18;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1829_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1829_,
                                        0,
                                        v___x_1823_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1829_,
                                        1,
                                        v_snd_1742_,
                                    );
                                    v___x_1825_ = v_reuseFailAlloc_1829_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1744_);
                                crate::leanh::lean_dec(v_snd_1742_);
                                crate::leanh::lean_dec(v_fst_1741_);
                                crate::leanh::lean_del_object(v___x_1739_);
                                crate::leanh::lean_dec(v_a_1718_);
                                crate::leanh::lean_dec_ref(v_d_1717_);
                                v_a_1830_ = crate::leanh::lean_ctor_get(v___x_1821_, 0);
                                v_isSharedCheck_1837_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1821_)) as u8;
                                if v_isSharedCheck_1837_ == 0 {
                                    v___x_1832_ = v___x_1821_;
                                    v_isShared_1833_ = v_isSharedCheck_1837_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1830_);
                                    crate::leanh::lean_dec(v___x_1821_);
                                    v___x_1832_ = crate::leanh::lean_box(0);
                                    v_isShared_1833_ = v_isSharedCheck_1837_;
                                    state = 20;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1744_);
                        crate::leanh::lean_dec(v_snd_1742_);
                        crate::leanh::lean_dec(v_fst_1741_);
                        crate::leanh::lean_del_object(v___x_1739_);
                        crate::leanh::lean_dec(v_a_1718_);
                        crate::leanh::lean_dec_ref(v_d_1717_);
                        v_a_1838_ = crate::leanh::lean_ctor_get(v___x_1749_, 0);
                        v_isSharedCheck_1845_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1749_)) as u8;
                        if v_isSharedCheck_1845_ == 0 {
                            v___x_1840_ = v___x_1749_;
                            v_isShared_1841_ = v_isSharedCheck_1845_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1838_);
                            crate::leanh::lean_dec(v___x_1749_);
                            v___x_1840_ = crate::leanh::lean_box(0);
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
                            v_reuseFailAlloc_1852_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_fst_1741_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_snd_1742_);
                            v___x_1848_ = v_reuseFailAlloc_1852_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v___x_1747_);
                        v___x_1853_ = l_Lean_Meta_Sym_instantiateMVarsS(
                            v___x_1747_,
                            v___y_1723_,
                            v___y_1724_,
                            v___y_1725_,
                            v___y_1726_,
                            v___y_1727_,
                            v___y_1728_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1853_) == 0 {
                            v_a_1854_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
                            crate::leanh::lean_inc(v_a_1854_);
                            crate::leanh::lean_dec_ref_known(v___x_1853_, 1);
                            v___x_1855_ = lean_array_fset(v_fst_1741_, v_a_1718_, v_a_1854_);
                            if v_isShared_1745_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1744_, 0, v___x_1855_);
                                v___x_1857_ = v___x_1744_;
                                state = 26;
                                continue;
                            } else {
                                v_reuseFailAlloc_1861_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1855_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_snd_1742_);
                                v___x_1857_ = v_reuseFailAlloc_1861_;
                                state = 26;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1744_);
                            crate::leanh::lean_dec(v_snd_1742_);
                            crate::leanh::lean_dec(v_fst_1741_);
                            crate::leanh::lean_del_object(v___x_1739_);
                            crate::leanh::lean_dec(v_a_1718_);
                            crate::leanh::lean_dec_ref(v_d_1717_);
                            v_a_1862_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
                            v_isSharedCheck_1869_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1853_)) as u8;
                            if v_isSharedCheck_1869_ == 0 {
                                v___x_1864_ = v___x_1853_;
                                v_isShared_1865_ = v_isSharedCheck_1869_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1862_);
                                crate::leanh::lean_dec(v___x_1853_);
                                v___x_1864_ = crate::leanh::lean_box(0);
                                v_isShared_1865_ = v_isSharedCheck_1869_;
                                state = 28;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_1756_) == 0 {
                    crate::leanh::lean_dec(v_a_1718_);
                    crate::leanh::lean_dec_ref(v_d_1717_);
                    v___x_1774_ = (crate::leanh::lean_unbox(v_snd_1742_) as u8);
                    crate::leanh::lean_dec(v_snd_1742_);
                    if v___x_1774_ == 0 {
                        v_contextDependent_1775_ =
                            crate::leanh::lean_ctor_get_uint8(v_a_1756_, 0 as u32);
                        crate::leanh::lean_dec_ref_known(v_a_1756_, 0);
                        v___y_1761_ = v_contextDependent_1775_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_1756_, 0);
                        v___y_1761_ = v___x_1735_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1758_);
                    crate::leanh::lean_del_object(v___x_1744_);
                    crate::leanh::lean_del_object(v___x_1739_);
                    v_proof_1776_ = crate::leanh::lean_ctor_get(v_a_1756_, 0);
                    crate::leanh::lean_inc_ref(v_proof_1776_);
                    v_contextDependent_1777_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_1756_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_a_1756_, 1);
                    v___x_1803_ = (crate::leanh::lean_unbox(v_snd_1742_) as u8);
                    crate::leanh::lean_dec(v_snd_1742_);
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
                v___x_1763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                v___x_1764_ = crate::leanh::lean_box((v___y_1761_) as usize);
                if v_isShared_1745_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1744_, 1, v___x_1764_);
                    v___x_1766_ = v___x_1744_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1773_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_fst_1741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1764_);
                    v___x_1766_ = v_reuseFailAlloc_1773_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1739_, 1, v___x_1766_);
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1763_);
                    v___x_1768_ = v___x_1739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1766_);
                    v___x_1768_ = v_reuseFailAlloc_1772_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1768_);
                    v___x_1770_ = v___x_1758_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
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
                if crate::leanh::lean_obj_tag(v___x_1780_) == 0 {
                    v_a_1781_ = crate::leanh::lean_ctor_get(v___x_1780_, 0);
                    crate::leanh::lean_inc_n(v_a_1781_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1780_, 1);
                    crate::leanh::lean_inc(v_mvarId_1748_);
                    v___x_1782_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_1748_, v_a_1781_, v___y_1726_);
                    if crate::leanh::lean_obj_tag(v___x_1782_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1782_, 1);
                        v___x_1783_ = lean_array_fset(v_fst_1741_, v_a_1718_, v_a_1781_);
                        v___x_1784_ = crate::leanh::lean_box((v___y_1779_) as usize);
                        v___x_1785_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1785_, 0, v___x_1783_);
                        crate::leanh::lean_ctor_set(v___x_1785_, 1, v___x_1784_);
                        v___x_1786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1786_, 0, v___x_1746_);
                        crate::leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                        v_a_1731_ = v___x_1786_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1781_);
                        crate::leanh::lean_dec(v_fst_1741_);
                        crate::leanh::lean_dec(v_a_1718_);
                        crate::leanh::lean_dec_ref(v_d_1717_);
                        v_a_1787_ = crate::leanh::lean_ctor_get(v___x_1782_, 0);
                        v_isSharedCheck_1794_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1782_)) as u8;
                        if v_isSharedCheck_1794_ == 0 {
                            v___x_1789_ = v___x_1782_;
                            v_isShared_1790_ = v_isSharedCheck_1794_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1787_);
                            crate::leanh::lean_dec(v___x_1782_);
                            v___x_1789_ = crate::leanh::lean_box(0);
                            v_isShared_1790_ = v_isSharedCheck_1794_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1741_);
                    crate::leanh::lean_dec(v_a_1718_);
                    crate::leanh::lean_dec_ref(v_d_1717_);
                    v_a_1795_ = crate::leanh::lean_ctor_get(v___x_1780_, 0);
                    v_isSharedCheck_1802_ = (!crate::leanh::lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1802_ == 0 {
                        v___x_1797_ = v___x_1780_;
                        v_isShared_1798_ = v_isSharedCheck_1802_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1795_);
                        crate::leanh::lean_dec(v___x_1780_);
                        v___x_1797_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
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
                    v_reuseFailAlloc_1801_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
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
                    v_reuseFailAlloc_1811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
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
                    v_reuseFailAlloc_1819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
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
                    crate::leanh::lean_ctor_set(v___x_1739_, 1, v___x_1825_);
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1746_);
                    v___x_1827_ = v___x_1739_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1828_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1825_);
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
                    v_reuseFailAlloc_1836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
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
                    v_reuseFailAlloc_1844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
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
                    crate::leanh::lean_ctor_set(v___x_1739_, 1, v___x_1848_);
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1746_);
                    v___x_1850_ = v___x_1739_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1851_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1848_);
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
                    crate::leanh::lean_ctor_set(v___x_1739_, 1, v___x_1857_);
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1746_);
                    v___x_1859_ = v___x_1739_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___x_1857_);
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
                    v_reuseFailAlloc_1868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
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
    mut v_upperBound_1873_: *mut crate::leanh::LeanObject,
    mut v_d_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
    mut v_b_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1885_);
    crate::leanh::lean_dec_ref(v___y_1884_);
    crate::leanh::lean_dec(v___y_1883_);
    crate::leanh::lean_dec_ref(v___y_1882_);
    crate::leanh::lean_dec(v___y_1881_);
    crate::leanh::lean_dec_ref(v___y_1880_);
    crate::leanh::lean_dec(v___y_1879_);
    crate::leanh::lean_dec_ref(v___y_1878_);
    crate::leanh::lean_dec(v___y_1877_);
    crate::leanh::lean_dec(v_upperBound_1873_);
    return v_res_1887_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(
    mut v_pattern_1890_: *mut crate::leanh::LeanObject,
    mut v_e_1891_: *mut crate::leanh::LeanObject,
    mut v___x_1892_: u8,
    mut v_d_1893_: *mut crate::leanh::LeanObject,
    mut v_expr_1894_: *mut crate::leanh::LeanObject,
    mut v_rhs_1895_: *mut crate::leanh::LeanObject,
    mut v_perm_1896_: u8,
    mut v___y_1897_: *mut crate::leanh::LeanObject,
    mut v___y_1898_: *mut crate::leanh::LeanObject,
    mut v___y_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
    mut v___y_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v_val_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v_fst_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_a_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut v_a_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
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
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_a_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1891_);
                crate::leanh::lean_inc_ref(v_pattern_1890_);
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
                if crate::leanh::lean_obj_tag(v___x_1907_) == 0 {
                    v_a_1908_ = crate::leanh::lean_ctor_get(v___x_1907_, 0);
                    v_isSharedCheck_2024_ = (!crate::leanh::lean_is_exclusive(v___x_1907_)) as u8;
                    if v_isSharedCheck_2024_ == 0 {
                        v___x_1910_ = v___x_1907_;
                        v_isShared_1911_ = v_isSharedCheck_2024_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1908_);
                        crate::leanh::lean_dec(v___x_1907_);
                        v___x_1910_ = crate::leanh::lean_box(0);
                        v_isShared_1911_ = v_isSharedCheck_2024_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_expr_1894_);
                    crate::leanh::lean_dec_ref(v_d_1893_);
                    crate::leanh::lean_dec_ref(v_e_1891_);
                    crate::leanh::lean_dec_ref(v_pattern_1890_);
                    v_a_2025_ = crate::leanh::lean_ctor_get(v___x_1907_, 0);
                    v_isSharedCheck_2032_ = (!crate::leanh::lean_is_exclusive(v___x_1907_)) as u8;
                    if v_isSharedCheck_2032_ == 0 {
                        v___x_2027_ = v___x_1907_;
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2025_);
                        crate::leanh::lean_dec(v___x_1907_);
                        v___x_2027_ = crate::leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1908_) == 1 {
                    crate::leanh::lean_del_object(v___x_1910_);
                    v_val_1912_ = crate::leanh::lean_ctor_get(v_a_1908_, 0);
                    crate::leanh::lean_inc(v_val_1912_);
                    crate::leanh::lean_dec_ref_known(v_a_1908_, 1);
                    v_us_1913_ = crate::leanh::lean_ctor_get(v_val_1912_, 0);
                    v_args_1914_ = crate::leanh::lean_ctor_get(v_val_1912_, 1);
                    v_isSharedCheck_2019_ = (!crate::leanh::lean_is_exclusive(v_val_1912_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_1916_ = v_val_1912_;
                        v_isShared_1917_ = v_isSharedCheck_2019_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_1914_);
                        crate::leanh::lean_inc(v_us_1913_);
                        crate::leanh::lean_dec(v_val_1912_);
                        v___x_1916_ = crate::leanh::lean_box(0);
                        v_isShared_1917_ = v_isSharedCheck_2019_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1908_);
                    crate::leanh::lean_dec_ref(v_expr_1894_);
                    crate::leanh::lean_dec_ref(v_d_1893_);
                    crate::leanh::lean_dec_ref(v_e_1891_);
                    crate::leanh::lean_dec_ref(v_pattern_1890_);
                    v___x_2020_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0;
                    if v_isShared_1911_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1910_, 0, v___x_2020_);
                        v___x_2022_ = v___x_1910_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_2023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
                        v___x_2022_ = v_reuseFailAlloc_2023_;
                        state = 22;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1918_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_1919_) == 0 {
                    v_a_1920_ = crate::leanh::lean_ctor_get(v___x_1919_, 0);
                    crate::leanh::lean_inc(v_a_1920_);
                    crate::leanh::lean_dec_ref_known(v___x_1919_, 1);
                    v___x_1921_ = lean_array_get_size(v_args_1914_);
                    v___x_1922_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1923_ = 0;
                    v___x_1924_ = crate::leanh::lean_box(0);
                    v___x_1925_ = crate::leanh::lean_box((v___x_1923_) as usize);
                    if v_isShared_1917_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1916_, 1, v___x_1925_);
                        crate::leanh::lean_ctor_set(v___x_1916_, 0, v_args_1914_);
                        v___x_1927_ = v___x_1916_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_args_1914_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___x_1925_);
                        v___x_1927_ = v_reuseFailAlloc_2010_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1916_);
                    crate::leanh::lean_dec_ref(v_args_1914_);
                    crate::leanh::lean_dec_ref(v_expr_1894_);
                    crate::leanh::lean_dec_ref(v_d_1893_);
                    crate::leanh::lean_dec_ref(v_e_1891_);
                    crate::leanh::lean_dec_ref(v_pattern_1890_);
                    v_a_2011_ = crate::leanh::lean_ctor_get(v___x_1919_, 0);
                    v_isSharedCheck_2018_ = (!crate::leanh::lean_is_exclusive(v___x_1919_)) as u8;
                    if v_isSharedCheck_2018_ == 0 {
                        v___x_2013_ = v___x_1919_;
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2011_);
                        crate::leanh::lean_dec(v___x_1919_);
                        v___x_2013_ = crate::leanh::lean_box(0);
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 20;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1928_, 0, v___x_1924_);
                crate::leanh::lean_ctor_set(v___x_1928_, 1, v___x_1927_);
                v___x_1929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v___x_1921_, v_d_1893_, v___x_1922_, v___x_1928_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
                if crate::leanh::lean_obj_tag(v___x_1929_) == 0 {
                    v_a_1930_ = crate::leanh::lean_ctor_get(v___x_1929_, 0);
                    v_isSharedCheck_2001_ = (!crate::leanh::lean_is_exclusive(v___x_1929_)) as u8;
                    if v_isSharedCheck_2001_ == 0 {
                        v___x_1932_ = v___x_1929_;
                        v_isShared_1933_ = v_isSharedCheck_2001_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1930_);
                        crate::leanh::lean_dec(v___x_1929_);
                        v___x_1932_ = crate::leanh::lean_box(0);
                        v_isShared_1933_ = v_isSharedCheck_2001_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1920_);
                    crate::leanh::lean_dec_ref(v_expr_1894_);
                    crate::leanh::lean_dec_ref(v_e_1891_);
                    crate::leanh::lean_dec_ref(v_pattern_1890_);
                    v_a_2002_ = crate::leanh::lean_ctor_get(v___x_1929_, 0);
                    v_isSharedCheck_2009_ = (!crate::leanh::lean_is_exclusive(v___x_1929_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2004_ = v___x_1929_;
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2002_);
                        crate::leanh::lean_dec(v___x_1929_);
                        v___x_2004_ = crate::leanh::lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 18;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_1934_ = crate::leanh::lean_ctor_get(v_a_1930_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1934_) == 0 {
                    crate::leanh::lean_del_object(v___x_1932_);
                    v_snd_1935_ = crate::leanh::lean_ctor_get(v_a_1930_, 1);
                    crate::leanh::lean_inc(v_snd_1935_);
                    crate::leanh::lean_dec(v_a_1930_);
                    v_fst_1936_ = crate::leanh::lean_ctor_get(v_snd_1935_, 0);
                    crate::leanh::lean_inc(v_fst_1936_);
                    v_snd_1937_ = crate::leanh::lean_ctor_get(v_snd_1935_, 1);
                    crate::leanh::lean_inc(v_snd_1937_);
                    crate::leanh::lean_dec(v_snd_1935_);
                    v_levelParams_1938_ = crate::leanh::lean_ctor_get(v_pattern_1890_, 0);
                    crate::leanh::lean_inc(v_levelParams_1938_);
                    crate::leanh::lean_inc(v_a_1920_);
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
                    if crate::leanh::lean_obj_tag(v___x_1941_) == 0 {
                        v_a_1942_ = crate::leanh::lean_ctor_get(v___x_1941_, 0);
                        crate::leanh::lean_inc(v_a_1942_);
                        crate::leanh::lean_dec_ref_known(v___x_1941_, 1);
                        v___x_1943_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                            v_a_1942_,
                            v_fst_1936_,
                            v___y_1901_,
                        );
                        crate::leanh::lean_dec(v_fst_1936_);
                        if crate::leanh::lean_obj_tag(v___x_1943_) == 0 {
                            v_a_1944_ = crate::leanh::lean_ctor_get(v___x_1943_, 0);
                            v_isSharedCheck_1980_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1943_)) as u8;
                            if v_isSharedCheck_1980_ == 0 {
                                v___x_1946_ = v___x_1943_;
                                v_isShared_1947_ = v_isSharedCheck_1980_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1944_);
                                crate::leanh::lean_dec(v___x_1943_);
                                v___x_1946_ = crate::leanh::lean_box(0);
                                v_isShared_1947_ = v_isSharedCheck_1980_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1939_);
                            crate::leanh::lean_dec(v_snd_1937_);
                            crate::leanh::lean_dec_ref(v_e_1891_);
                            v_a_1981_ = crate::leanh::lean_ctor_get(v___x_1943_, 0);
                            v_isSharedCheck_1988_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1943_)) as u8;
                            if v_isSharedCheck_1988_ == 0 {
                                v___x_1983_ = v___x_1943_;
                                v_isShared_1984_ = v_isSharedCheck_1988_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1981_);
                                crate::leanh::lean_dec(v___x_1943_);
                                v___x_1983_ = crate::leanh::lean_box(0);
                                v_isShared_1984_ = v_isSharedCheck_1988_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1939_);
                        crate::leanh::lean_dec(v_snd_1937_);
                        crate::leanh::lean_dec(v_fst_1936_);
                        crate::leanh::lean_dec_ref(v_e_1891_);
                        v_a_1989_ = crate::leanh::lean_ctor_get(v___x_1941_, 0);
                        v_isSharedCheck_1996_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1941_)) as u8;
                        if v_isSharedCheck_1996_ == 0 {
                            v___x_1991_ = v___x_1941_;
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1989_);
                            crate::leanh::lean_dec(v___x_1941_);
                            v___x_1991_ = crate::leanh::lean_box(0);
                            v_isShared_1992_ = v_isSharedCheck_1996_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1934_);
                    crate::leanh::lean_dec(v_a_1930_);
                    crate::leanh::lean_dec(v_a_1920_);
                    crate::leanh::lean_dec_ref(v_expr_1894_);
                    crate::leanh::lean_dec_ref(v_e_1891_);
                    crate::leanh::lean_dec_ref(v_pattern_1890_);
                    v_val_1997_ = crate::leanh::lean_ctor_get(v_fst_1934_, 0);
                    crate::leanh::lean_inc(v_val_1997_);
                    crate::leanh::lean_dec_ref_known(v_fst_1934_, 1);
                    if v_isShared_1933_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1932_, 0, v_val_1997_);
                        v___x_1999_ = v___x_1932_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1997_);
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
                    crate::leanh::lean_inc(v_a_1944_);
                    v___x_1949_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_1896_, v_e_1891_, v_a_1944_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
                    if crate::leanh::lean_obj_tag(v___x_1949_) == 0 {
                        v_a_1950_ = crate::leanh::lean_ctor_get(v___x_1949_, 0);
                        v_isSharedCheck_1966_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1949_)) as u8;
                        if v_isSharedCheck_1966_ == 0 {
                            v___x_1952_ = v___x_1949_;
                            v_isShared_1953_ = v_isSharedCheck_1966_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1950_);
                            crate::leanh::lean_dec(v___x_1949_);
                            v___x_1952_ = crate::leanh::lean_box(0);
                            v_isShared_1953_ = v_isSharedCheck_1966_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1946_);
                        crate::leanh::lean_dec(v_a_1944_);
                        crate::leanh::lean_dec_ref(v___x_1939_);
                        crate::leanh::lean_dec(v_snd_1937_);
                        v_a_1967_ = crate::leanh::lean_ctor_get(v___x_1949_, 0);
                        v_isSharedCheck_1974_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1949_)) as u8;
                        if v_isSharedCheck_1974_ == 0 {
                            v___x_1969_ = v___x_1949_;
                            v_isShared_1970_ = v_isSharedCheck_1974_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1967_);
                            crate::leanh::lean_dec(v___x_1949_);
                            v___x_1969_ = crate::leanh::lean_box(0);
                            v_isShared_1970_ = v_isSharedCheck_1974_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1944_);
                    crate::leanh::lean_dec_ref(v___x_1939_);
                    crate::leanh::lean_dec_ref(v_e_1891_);
                    v___x_1975_ = (crate::leanh::lean_unbox(v_snd_1937_) as u8);
                    crate::leanh::lean_dec(v_snd_1937_);
                    v___x_1976_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1975_);
                    if v_isShared_1947_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1946_, 0, v___x_1976_);
                        v___x_1978_ = v___x_1946_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1979_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
                        v___x_1978_ = v_reuseFailAlloc_1979_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1960_ = (crate::leanh::lean_unbox(v_a_1950_) as u8);
                crate::leanh::lean_dec(v_a_1950_);
                if v___x_1960_ == 0 {
                    crate::leanh::lean_del_object(v___x_1946_);
                    crate::leanh::lean_dec(v_a_1944_);
                    crate::leanh::lean_dec_ref(v___x_1939_);
                    state = 7;
                    continue;
                } else {
                    if v___x_1948_ == 0 {
                        crate::leanh::lean_del_object(v___x_1952_);
                        v___x_1961_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_1961_, 0, v_a_1944_);
                        crate::leanh::lean_ctor_set(v___x_1961_, 1, v___x_1939_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1961_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_1923_,
                        );
                        v___x_1962_ = (crate::leanh::lean_unbox(v_snd_1937_) as u8);
                        crate::leanh::lean_dec(v_snd_1937_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1961_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v___x_1962_,
                        );
                        if v_isShared_1947_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1946_, 0, v___x_1961_);
                            v___x_1964_ = v___x_1946_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_1965_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1961_);
                            v___x_1964_ = v_reuseFailAlloc_1965_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1946_);
                        crate::leanh::lean_dec(v_a_1944_);
                        crate::leanh::lean_dec_ref(v___x_1939_);
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_1955_ = (crate::leanh::lean_unbox(v_snd_1937_) as u8);
                crate::leanh::lean_dec(v_snd_1937_);
                v___x_1956_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1955_);
                if v_isShared_1953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1952_, 0, v___x_1956_);
                    v___x_1958_ = v___x_1952_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
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
                    v_reuseFailAlloc_1973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
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
                    v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
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
                    v_reuseFailAlloc_1995_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
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
                    v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
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
                    v_reuseFailAlloc_2017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
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
                    v_reuseFailAlloc_2031_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pattern_2033_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_e_2034_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2035_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_d_2036_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_expr_2037_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_rhs_2038_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_perm_2039_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2040_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2041_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2042_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2043_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2044_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2045_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2046_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2047_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2048_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2049_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_34692__boxed_2050_: u8 = 0;
    let mut v_perm_boxed_2051_: u8 = 0;
    let mut v_res_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34692__boxed_2050_ = (crate::leanh::lean_unbox(v___x_2035_) as u8);
    v_perm_boxed_2051_ = (crate::leanh::lean_unbox(v_perm_2039_) as u8);
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
    crate::leanh::lean_dec(v___y_2048_);
    crate::leanh::lean_dec_ref(v___y_2047_);
    crate::leanh::lean_dec(v___y_2046_);
    crate::leanh::lean_dec_ref(v___y_2045_);
    crate::leanh::lean_dec(v___y_2044_);
    crate::leanh::lean_dec_ref(v___y_2043_);
    crate::leanh::lean_dec(v___y_2042_);
    crate::leanh::lean_dec_ref(v___y_2041_);
    crate::leanh::lean_dec(v___y_2040_);
    crate::leanh::lean_dec_ref(v_rhs_2038_);
    return v_res_2052_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_rewrite(
    mut v_thm_2053_: *mut crate::leanh::LeanObject,
    mut v_e_2054_: *mut crate::leanh::LeanObject,
    mut v_d_2055_: *mut crate::leanh::LeanObject,
    mut v_a_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_a_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expr_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_perm_2069_: u8 = 0;
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_expr_2066_ = crate::leanh::lean_ctor_get(v_thm_2053_, 0);
    crate::leanh::lean_inc_ref(v_expr_2066_);
    v_pattern_2067_ = crate::leanh::lean_ctor_get(v_thm_2053_, 1);
    crate::leanh::lean_inc_ref(v_pattern_2067_);
    v_rhs_2068_ = crate::leanh::lean_ctor_get(v_thm_2053_, 2);
    crate::leanh::lean_inc_ref(v_rhs_2068_);
    v_perm_2069_ = crate::leanh::lean_ctor_get_uint8(
        v_thm_2053_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_thm_2053_);
    v___x_2070_ = 1;
    v___x_2071_ = crate::leanh::lean_box((v___x_2070_) as usize);
    v___x_2072_ = crate::leanh::lean_box((v_perm_2069_) as usize);
    v___f_2073_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed as *mut core::ffi::c_void,
        17,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2073_, 0, v_pattern_2067_);
    crate::leanh::lean_closure_set(v___f_2073_, 1, v_e_2054_);
    crate::leanh::lean_closure_set(v___f_2073_, 2, v___x_2071_);
    crate::leanh::lean_closure_set(v___f_2073_, 3, v_d_2055_);
    crate::leanh::lean_closure_set(v___f_2073_, 4, v_expr_2066_);
    crate::leanh::lean_closure_set(v___f_2073_, 5, v_rhs_2068_);
    crate::leanh::lean_closure_set(v___f_2073_, 6, v___x_2072_);
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
    mut v_thm_2076_: *mut crate::leanh::LeanObject,
    mut v_e_2077_: *mut crate::leanh::LeanObject,
    mut v_d_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
    mut v_a_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
    mut v_a_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2087_);
    crate::leanh::lean_dec_ref(v_a_2086_);
    crate::leanh::lean_dec(v_a_2085_);
    crate::leanh::lean_dec_ref(v_a_2084_);
    crate::leanh::lean_dec(v_a_2083_);
    crate::leanh::lean_dec_ref(v_a_2082_);
    crate::leanh::lean_dec(v_a_2081_);
    crate::leanh::lean_dec_ref(v_a_2080_);
    crate::leanh::lean_dec(v_a_2079_);
    return v_res_2089_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(
    mut v_mvarId_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
    mut v___y_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(
            v_mvarId_2090_,
            v___y_2097_,
        );
    return v___x_2101_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(
    mut v_mvarId_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
    mut v___y_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
    mut v___y_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
    mut v___y_2109_: *mut crate::leanh::LeanObject,
    mut v___y_2110_: *mut crate::leanh::LeanObject,
    mut v___y_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2111_);
    crate::leanh::lean_dec_ref(v___y_2110_);
    crate::leanh::lean_dec(v___y_2109_);
    crate::leanh::lean_dec_ref(v___y_2108_);
    crate::leanh::lean_dec(v___y_2107_);
    crate::leanh::lean_dec_ref(v___y_2106_);
    crate::leanh::lean_dec(v___y_2105_);
    crate::leanh::lean_dec_ref(v___y_2104_);
    crate::leanh::lean_dec(v___y_2103_);
    crate::leanh::lean_dec(v_mvarId_2102_);
    return v_res_2113_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(
    mut v_mvarId_2114_: *mut crate::leanh::LeanObject,
    mut v_val_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
    mut v___y_2120_: *mut crate::leanh::LeanObject,
    mut v___y_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
    mut v___y_2123_: *mut crate::leanh::LeanObject,
    mut v___y_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(
        v_mvarId_2114_,
        v_val_2115_,
        v___y_2122_,
    );
    return v___x_2126_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(
    mut v_mvarId_2127_: *mut crate::leanh::LeanObject,
    mut v_val_2128_: *mut crate::leanh::LeanObject,
    mut v___y_2129_: *mut crate::leanh::LeanObject,
    mut v___y_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2137_);
    crate::leanh::lean_dec_ref(v___y_2136_);
    crate::leanh::lean_dec(v___y_2135_);
    crate::leanh::lean_dec_ref(v___y_2134_);
    crate::leanh::lean_dec(v___y_2133_);
    crate::leanh::lean_dec_ref(v___y_2132_);
    crate::leanh::lean_dec(v___y_2131_);
    crate::leanh::lean_dec_ref(v___y_2130_);
    crate::leanh::lean_dec(v___y_2129_);
    return v_res_2139_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(
    mut v_upperBound_2140_: *mut crate::leanh::LeanObject,
    mut v_d_2141_: *mut crate::leanh::LeanObject,
    mut v___x_2142_: *mut crate::leanh::LeanObject,
    mut v_inst_2143_: *mut crate::leanh::LeanObject,
    mut v_R_2144_: *mut crate::leanh::LeanObject,
    mut v_a_2145_: *mut crate::leanh::LeanObject,
    mut v_b_2146_: *mut crate::leanh::LeanObject,
    mut v_c_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_2159_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_d_2160_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2161_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_2162_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_R_2163_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_2164_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_b_2165_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_c_2166_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2167_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2168_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2169_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2170_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2171_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2172_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2173_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2174_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2175_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2176_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2175_);
    crate::leanh::lean_dec_ref(v___y_2174_);
    crate::leanh::lean_dec(v___y_2173_);
    crate::leanh::lean_dec_ref(v___y_2172_);
    crate::leanh::lean_dec(v___y_2171_);
    crate::leanh::lean_dec_ref(v___y_2170_);
    crate::leanh::lean_dec(v___y_2169_);
    crate::leanh::lean_dec_ref(v___y_2168_);
    crate::leanh::lean_dec(v___y_2167_);
    crate::leanh::lean_dec(v___x_2161_);
    crate::leanh::lean_dec(v_upperBound_2159_);
    return v_res_2177_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(
    mut v_00_u03b2_2178_: *mut crate::leanh::LeanObject,
    mut v_x_2179_: *mut crate::leanh::LeanObject,
    mut v_x_2180_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2181_: u8 = 0;
    v___x_2181_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_2179_, v_x_2180_);
    return v___x_2181_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(
    mut v_00_u03b2_2182_: *mut crate::leanh::LeanObject,
    mut v_x_2183_: *mut crate::leanh::LeanObject,
    mut v_x_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2185_: u8 = 0;
    let mut v_r_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_2182_, v_x_2183_, v_x_2184_);
    crate::leanh::lean_dec(v_x_2184_);
    crate::leanh::lean_dec_ref(v_x_2183_);
    v_r_2186_ = crate::leanh::lean_box((v_res_2185_) as usize);
    return v_r_2186_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(
    mut v_00_u03b2_2187_: *mut crate::leanh::LeanObject,
    mut v_x_2188_: *mut crate::leanh::LeanObject,
    mut v_x_2189_: *mut crate::leanh::LeanObject,
    mut v_x_2190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_2188_, v_x_2189_, v_x_2190_);
    return v___x_2191_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(
    mut v_00_u03b2_2192_: *mut crate::leanh::LeanObject,
    mut v_x_2193_: *mut crate::leanh::LeanObject,
    mut v_x_2194_: usize,
    mut v_x_2195_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2196_: u8 = 0;
    v___x_2196_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_2193_, v_x_2194_, v_x_2195_);
    return v___x_2196_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_2197_: *mut crate::leanh::LeanObject,
    mut v_x_2198_: *mut crate::leanh::LeanObject,
    mut v_x_2199_: *mut crate::leanh::LeanObject,
    mut v_x_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_35102__boxed_2201_: usize = 0;
    let mut v_res_2202_: u8 = 0;
    let mut v_r_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_35102__boxed_2201_ = crate::leanh::lean_unbox_usize(v_x_2199_);
    crate::leanh::lean_dec(v_x_2199_);
    v_res_2202_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(v_00_u03b2_2197_, v_x_2198_, v_x_35102__boxed_2201_, v_x_2200_);
    crate::leanh::lean_dec(v_x_2200_);
    crate::leanh::lean_dec_ref(v_x_2198_);
    v_r_2203_ = crate::leanh::lean_box((v_res_2202_) as usize);
    return v_r_2203_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(
    mut v_00_u03b2_2204_: *mut crate::leanh::LeanObject,
    mut v_x_2205_: *mut crate::leanh::LeanObject,
    mut v_x_2206_: usize,
    mut v_x_2207_: usize,
    mut v_x_2208_: *mut crate::leanh::LeanObject,
    mut v_x_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_2205_, v_x_2206_, v_x_2207_, v_x_2208_, v_x_2209_);
    return v___x_2210_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___boxed(
    mut v_00_u03b2_2211_: *mut crate::leanh::LeanObject,
    mut v_x_2212_: *mut crate::leanh::LeanObject,
    mut v_x_2213_: *mut crate::leanh::LeanObject,
    mut v_x_2214_: *mut crate::leanh::LeanObject,
    mut v_x_2215_: *mut crate::leanh::LeanObject,
    mut v_x_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_35113__boxed_2217_: usize = 0;
    let mut v_x_35114__boxed_2218_: usize = 0;
    let mut v_res_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_35113__boxed_2217_ = crate::leanh::lean_unbox_usize(v_x_2213_);
    crate::leanh::lean_dec(v_x_2213_);
    v_x_35114__boxed_2218_ = crate::leanh::lean_unbox_usize(v_x_2214_);
    crate::leanh::lean_dec(v_x_2214_);
    v_res_2219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(v_00_u03b2_2211_, v_x_2212_, v_x_35113__boxed_2217_, v_x_35114__boxed_2218_, v_x_2215_, v_x_2216_);
    return v_res_2219_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(
    mut v_00_u03b2_2220_: *mut crate::leanh::LeanObject,
    mut v_keys_2221_: *mut crate::leanh::LeanObject,
    mut v_vals_2222_: *mut crate::leanh::LeanObject,
    mut v_heq_2223_: *mut crate::leanh::LeanObject,
    mut v_i_2224_: *mut crate::leanh::LeanObject,
    mut v_k_2225_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2226_: u8 = 0;
    v___x_2226_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_2221_, v_i_2224_, v_k_2225_);
    return v___x_2226_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_2227_: *mut crate::leanh::LeanObject,
    mut v_keys_2228_: *mut crate::leanh::LeanObject,
    mut v_vals_2229_: *mut crate::leanh::LeanObject,
    mut v_heq_2230_: *mut crate::leanh::LeanObject,
    mut v_i_2231_: *mut crate::leanh::LeanObject,
    mut v_k_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2233_: u8 = 0;
    let mut v_r_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(v_00_u03b2_2227_, v_keys_2228_, v_vals_2229_, v_heq_2230_, v_i_2231_, v_k_2232_);
    crate::leanh::lean_dec(v_k_2232_);
    crate::leanh::lean_dec_ref(v_vals_2229_);
    crate::leanh::lean_dec_ref(v_keys_2228_);
    v_r_2234_ = crate::leanh::lean_box((v_res_2233_) as usize);
    return v_r_2234_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10(
    mut v_00_u03b2_2235_: *mut crate::leanh::LeanObject,
    mut v_n_2236_: *mut crate::leanh::LeanObject,
    mut v_k_2237_: *mut crate::leanh::LeanObject,
    mut v_v_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2239_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v_n_2236_, v_k_2237_, v_v_2238_);
    return v___x_2239_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(
    mut v_00_u03b2_2240_: *mut crate::leanh::LeanObject,
    mut v_depth_2241_: usize,
    mut v_keys_2242_: *mut crate::leanh::LeanObject,
    mut v_vals_2243_: *mut crate::leanh::LeanObject,
    mut v_heq_2244_: *mut crate::leanh::LeanObject,
    mut v_i_2245_: *mut crate::leanh::LeanObject,
    mut v_entries_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2247_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_2241_, v_keys_2242_, v_vals_2243_, v_i_2245_, v_entries_2246_);
    return v___x_2247_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___boxed(
    mut v_00_u03b2_2248_: *mut crate::leanh::LeanObject,
    mut v_depth_2249_: *mut crate::leanh::LeanObject,
    mut v_keys_2250_: *mut crate::leanh::LeanObject,
    mut v_vals_2251_: *mut crate::leanh::LeanObject,
    mut v_heq_2252_: *mut crate::leanh::LeanObject,
    mut v_i_2253_: *mut crate::leanh::LeanObject,
    mut v_entries_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2255_: usize = 0;
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2255_ = crate::leanh::lean_unbox_usize(v_depth_2249_);
    crate::leanh::lean_dec(v_depth_2249_);
    v_res_2256_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_2248_, v_depth_boxed_2255_, v_keys_2250_, v_vals_2251_, v_heq_2252_, v_i_2253_, v_entries_2254_);
    crate::leanh::lean_dec_ref(v_vals_2251_);
    crate::leanh::lean_dec_ref(v_keys_2250_);
    return v_res_2256_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11(
    mut v_00_u03b2_2257_: *mut crate::leanh::LeanObject,
    mut v_x_2258_: *mut crate::leanh::LeanObject,
    mut v_x_2259_: *mut crate::leanh::LeanObject,
    mut v_x_2260_: *mut crate::leanh::LeanObject,
    mut v_x_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2262_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_x_2258_, v_x_2259_, v_x_2260_, v_x_2261_);
    return v___x_2262_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(
    mut v_fst_2263_: *mut crate::leanh::LeanObject,
    mut v_d_2264_: *mut crate::leanh::LeanObject,
    mut v_x_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_fst_2277_: *mut crate::leanh::LeanObject,
    mut v_d_2278_: *mut crate::leanh::LeanObject,
    mut v_x_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_2277_, v_d_2278_, v_x_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
    crate::leanh::lean_dec(v___y_2288_);
    crate::leanh::lean_dec_ref(v___y_2287_);
    crate::leanh::lean_dec(v___y_2286_);
    crate::leanh::lean_dec_ref(v___y_2285_);
    crate::leanh::lean_dec(v___y_2284_);
    crate::leanh::lean_dec_ref(v___y_2283_);
    crate::leanh::lean_dec(v___y_2282_);
    crate::leanh::lean_dec_ref(v___y_2281_);
    crate::leanh::lean_dec(v___y_2280_);
    return v_res_2290_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(
    mut v_d_2291_: *mut crate::leanh::LeanObject,
    mut v_e_2292_: *mut crate::leanh::LeanObject,
    mut v_as_2293_: *mut crate::leanh::LeanObject,
    mut v_sz_2294_: usize,
    mut v_i_2295_: usize,
    mut v_b_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2308_: u8 = 0;
    let mut v___y_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2316_: u8 = 0;
    let mut v___y_2317_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: u8 = 0;
    let mut v___y_2322_: u8 = 0;
    let mut v___y_2323_: u8 = 0;
    let mut v___y_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: u8 = 0;
    let mut v___y_2327_: u8 = 0;
    let mut v_contextDependent_2328_: u8 = 0;
    let mut v_contextDependent_2329_: u8 = 0;
    let mut v___y_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2332_: u8 = 0;
    let mut v___x_2333_: u8 = 0;
    let mut v___x_2334_: u8 = 0;
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_2346_: u8 = 0;
    let mut v___y_2347_: u8 = 0;
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v_reuseFailAlloc_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v_result_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u8 = 0;
    let mut v_done_2359_: u8 = 0;
    let mut v_contextDependent_2360_: u8 = 0;
    let mut v_contextDependent_2361_: u8 = 0;
    let mut v_done_2362_: u8 = 0;
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: u8 = 0;
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___f_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut v_unused_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = lean_usize_dec_lt(v_i_2295_, v_sz_2294_);
                if v___x_2334_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2292_);
                    crate::leanh::lean_dec_ref(v_d_2291_);
                    v___x_2335_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2335_, 0, v_b_2296_);
                    return v___x_2335_;
                } else {
                    v_a_2336_ = lean_array_uget_borrowed(v_as_2293_, v_i_2295_);
                    v_fst_2337_ = crate::leanh::lean_ctor_get(v_a_2336_, 0);
                    v_snd_2338_ = crate::leanh::lean_ctor_get(v_a_2336_, 1);
                    v_snd_2339_ = crate::leanh::lean_ctor_get(v_b_2296_, 1);
                    v_isSharedCheck_2388_ = (!crate::leanh::lean_is_exclusive(v_b_2296_)) as u8;
                    if v_isSharedCheck_2388_ == 0 {
                        v_unused_2389_ = crate::leanh::lean_ctor_get(v_b_2296_, 0);
                        crate::leanh::lean_dec(v_unused_2389_);
                        v___x_2341_ = v_b_2296_;
                        v_isShared_2342_ = v_isSharedCheck_2388_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2339_);
                        crate::leanh::lean_dec(v_b_2296_);
                        v___x_2341_ = crate::leanh::lean_box(0);
                        v_isShared_2342_ = v_isSharedCheck_2388_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2310_, 0, v___y_2309_);
                v___x_2311_ = crate::leanh::lean_box((v___y_2308_) as usize);
                v___x_2312_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2312_, 0, v___x_2310_);
                crate::leanh::lean_ctor_set(v___x_2312_, 1, v___x_2311_);
                v___x_2313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2313_, 0, v___x_2312_);
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
                    if crate::leanh::lean_obj_tag(v___y_2325_) == 0 {
                        v_contextDependent_2328_ =
                            crate::leanh::lean_ctor_get_uint8(v___y_2325_, 1 as u32);
                        v___y_2320_ = v___y_2325_;
                        v___y_2321_ = v___y_2327_;
                        v___y_2322_ = v___y_2326_;
                        v___y_2323_ = v_contextDependent_2328_;
                        state = 3;
                        continue;
                    } else {
                        v_contextDependent_2329_ = crate::leanh::lean_ctor_get_uint8(
                            v___y_2325_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
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
                v___x_2343_ = crate::leanh::lean_box(0);
                v___x_2365_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2366_ = lean_nat_dec_eq(v_snd_2338_, v___x_2365_);
                if v___x_2366_ == 0 {
                    crate::leanh::lean_inc_ref(v_d_2291_);
                    crate::leanh::lean_inc(v_fst_2337_);
                    v___f_2367_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                    crate::leanh::lean_closure_set(v___f_2367_, 0, v_fst_2337_);
                    crate::leanh::lean_closure_set(v___f_2367_, 1, v_d_2291_);
                    crate::leanh::lean_inc_ref(v_e_2292_);
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
                    if crate::leanh::lean_obj_tag(v___x_2368_) == 0 {
                        v_a_2369_ = crate::leanh::lean_ctor_get(v___x_2368_, 0);
                        crate::leanh::lean_inc(v_a_2369_);
                        crate::leanh::lean_dec_ref_known(v___x_2368_, 1);
                        v_result_2357_ = v_a_2369_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_2341_);
                        crate::leanh::lean_dec(v_snd_2339_);
                        crate::leanh::lean_dec_ref(v_e_2292_);
                        crate::leanh::lean_dec_ref(v_d_2291_);
                        v_a_2370_ = crate::leanh::lean_ctor_get(v___x_2368_, 0);
                        v_isSharedCheck_2377_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2368_)) as u8;
                        if v_isSharedCheck_2377_ == 0 {
                            v___x_2372_ = v___x_2368_;
                            v_isShared_2373_ = v_isSharedCheck_2377_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2370_);
                            crate::leanh::lean_dec(v___x_2368_);
                            v___x_2372_ = crate::leanh::lean_box(0);
                            v_isShared_2373_ = v_isSharedCheck_2377_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_d_2291_);
                    crate::leanh::lean_inc_ref(v_e_2292_);
                    crate::leanh::lean_inc(v_fst_2337_);
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
                    if crate::leanh::lean_obj_tag(v___x_2378_) == 0 {
                        v_a_2379_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                        crate::leanh::lean_inc(v_a_2379_);
                        crate::leanh::lean_dec_ref_known(v___x_2378_, 1);
                        v_result_2357_ = v_a_2379_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_2341_);
                        crate::leanh::lean_dec(v_snd_2339_);
                        crate::leanh::lean_dec_ref(v_e_2292_);
                        crate::leanh::lean_dec_ref(v_d_2291_);
                        v_a_2380_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                        v_isSharedCheck_2387_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2378_)) as u8;
                        if v_isSharedCheck_2387_ == 0 {
                            v___x_2382_ = v___x_2378_;
                            v_isShared_2383_ = v_isSharedCheck_2387_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2380_);
                            crate::leanh::lean_dec(v___x_2378_);
                            v___x_2382_ = crate::leanh::lean_box(0);
                            v_isShared_2383_ = v_isSharedCheck_2387_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_done_2346_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2345_);
                    v___x_2348_ = crate::leanh::lean_box((v___y_2347_) as usize);
                    if v_isShared_2342_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2341_, 1, v___x_2348_);
                        crate::leanh::lean_ctor_set(v___x_2341_, 0, v___x_2343_);
                        v___x_2350_ = v___x_2341_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2343_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2348_);
                        v___x_2350_ = v_reuseFailAlloc_2354_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2341_);
                    crate::leanh::lean_dec_ref(v_e_2292_);
                    crate::leanh::lean_dec_ref(v_d_2291_);
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
                v___x_2358_ = (crate::leanh::lean_unbox(v_snd_2339_) as u8);
                if v___x_2358_ == 0 {
                    crate::leanh::lean_dec(v_snd_2339_);
                    if crate::leanh::lean_obj_tag(v_result_2357_) == 0 {
                        v_done_2359_ = crate::leanh::lean_ctor_get_uint8(v_result_2357_, 0 as u32);
                        v_contextDependent_2360_ =
                            crate::leanh::lean_ctor_get_uint8(v_result_2357_, 1 as u32);
                        v___y_2345_ = v_result_2357_;
                        v_done_2346_ = v_done_2359_;
                        v___y_2347_ = v_contextDependent_2360_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_2341_);
                        crate::leanh::lean_dec_ref(v_e_2292_);
                        crate::leanh::lean_dec_ref(v_d_2291_);
                        v_contextDependent_2361_ = crate::leanh::lean_ctor_get_uint8(
                            v_result_2357_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        v___y_2331_ = v_result_2357_;
                        v___y_2332_ = v_contextDependent_2361_;
                        state = 5;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_result_2357_) == 0 {
                        v_done_2362_ = crate::leanh::lean_ctor_get_uint8(v_result_2357_, 0 as u32);
                        v___x_2363_ = (crate::leanh::lean_unbox(v_snd_2339_) as u8);
                        crate::leanh::lean_dec(v_snd_2339_);
                        v___y_2345_ = v_result_2357_;
                        v_done_2346_ = v_done_2362_;
                        v___y_2347_ = v___x_2363_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_2341_);
                        crate::leanh::lean_dec_ref(v_e_2292_);
                        crate::leanh::lean_dec_ref(v_d_2291_);
                        v___x_2364_ = (crate::leanh::lean_unbox(v_snd_2339_) as u8);
                        crate::leanh::lean_dec(v_snd_2339_);
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
                    v_reuseFailAlloc_2376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
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
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
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
    mut v_d_2390_: *mut crate::leanh::LeanObject,
    mut v_e_2391_: *mut crate::leanh::LeanObject,
    mut v_as_2392_: *mut crate::leanh::LeanObject,
    mut v_sz_2393_: *mut crate::leanh::LeanObject,
    mut v_i_2394_: *mut crate::leanh::LeanObject,
    mut v_b_2395_: *mut crate::leanh::LeanObject,
    mut v___y_2396_: *mut crate::leanh::LeanObject,
    mut v___y_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2406_: usize = 0;
    let mut v_i_boxed_2407_: usize = 0;
    let mut v_res_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2406_ = crate::leanh::lean_unbox_usize(v_sz_2393_);
    crate::leanh::lean_dec(v_sz_2393_);
    v_i_boxed_2407_ = crate::leanh::lean_unbox_usize(v_i_2394_);
    crate::leanh::lean_dec(v_i_2394_);
    v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_2390_, v_e_2391_, v_as_2392_, v_sz_boxed_2406_, v_i_boxed_2407_, v_b_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
    crate::leanh::lean_dec(v___y_2404_);
    crate::leanh::lean_dec_ref(v___y_2403_);
    crate::leanh::lean_dec(v___y_2402_);
    crate::leanh::lean_dec_ref(v___y_2401_);
    crate::leanh::lean_dec(v___y_2400_);
    crate::leanh::lean_dec_ref(v___y_2399_);
    crate::leanh::lean_dec(v___y_2398_);
    crate::leanh::lean_dec_ref(v___y_2397_);
    crate::leanh::lean_dec(v___y_2396_);
    crate::leanh::lean_dec_ref(v_as_2392_);
    return v_res_2408_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorems_rewrite(
    mut v_thms_2413_: *mut crate::leanh::LeanObject,
    mut v_d_2414_: *mut crate::leanh::LeanObject,
    mut v_e_2415_: *mut crate::leanh::LeanObject,
    mut v_a_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
    mut v_a_2421_: *mut crate::leanh::LeanObject,
    mut v_a_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2428_: usize = 0;
    let mut v___x_2429_: usize = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v_fst_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: u8 = 0;
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v_a_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                crate::leanh::lean_dec_ref(v___x_2426_);
                if crate::leanh::lean_obj_tag(v___x_2430_) == 0 {
                    v_a_2431_ = crate::leanh::lean_ctor_get(v___x_2430_, 0);
                    v_isSharedCheck_2446_ = (!crate::leanh::lean_is_exclusive(v___x_2430_)) as u8;
                    if v_isSharedCheck_2446_ == 0 {
                        v___x_2433_ = v___x_2430_;
                        v_isShared_2434_ = v_isSharedCheck_2446_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2431_);
                        crate::leanh::lean_dec(v___x_2430_);
                        v___x_2433_ = crate::leanh::lean_box(0);
                        v_isShared_2434_ = v_isSharedCheck_2446_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2447_ = crate::leanh::lean_ctor_get(v___x_2430_, 0);
                    v_isSharedCheck_2454_ = (!crate::leanh::lean_is_exclusive(v___x_2430_)) as u8;
                    if v_isSharedCheck_2454_ == 0 {
                        v___x_2449_ = v___x_2430_;
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2447_);
                        crate::leanh::lean_dec(v___x_2430_);
                        v___x_2449_ = crate::leanh::lean_box(0);
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2435_ = crate::leanh::lean_ctor_get(v_a_2431_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2435_) == 0 {
                    v_snd_2436_ = crate::leanh::lean_ctor_get(v_a_2431_, 1);
                    crate::leanh::lean_inc(v_snd_2436_);
                    crate::leanh::lean_dec(v_a_2431_);
                    v___x_2437_ = (crate::leanh::lean_unbox(v_snd_2436_) as u8);
                    crate::leanh::lean_dec(v_snd_2436_);
                    v___x_2438_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_2437_);
                    if v_isShared_2434_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2433_, 0, v___x_2438_);
                        v___x_2440_ = v___x_2433_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2441_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
                        v___x_2440_ = v_reuseFailAlloc_2441_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2435_);
                    crate::leanh::lean_dec(v_a_2431_);
                    v_val_2442_ = crate::leanh::lean_ctor_get(v_fst_2435_, 0);
                    crate::leanh::lean_inc(v_val_2442_);
                    crate::leanh::lean_dec_ref_known(v_fst_2435_, 1);
                    if v_isShared_2434_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2433_, 0, v_val_2442_);
                        v___x_2444_ = v___x_2433_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_val_2442_);
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
                    v_reuseFailAlloc_2453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
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
    mut v_thms_2455_: *mut crate::leanh::LeanObject,
    mut v_d_2456_: *mut crate::leanh::LeanObject,
    mut v_e_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
    mut v_a_2464_: *mut crate::leanh::LeanObject,
    mut v_a_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2466_);
    crate::leanh::lean_dec_ref(v_a_2465_);
    crate::leanh::lean_dec(v_a_2464_);
    crate::leanh::lean_dec_ref(v_a_2463_);
    crate::leanh::lean_dec(v_a_2462_);
    crate::leanh::lean_dec_ref(v_a_2461_);
    crate::leanh::lean_dec(v_a_2460_);
    crate::leanh::lean_dec_ref(v_a_2459_);
    crate::leanh::lean_dec(v_a_2458_);
    crate::leanh::lean_dec_ref(v_thms_2455_);
    return v_res_2468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ACLt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Rewrite(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Rewrite(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_ACLt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
}
