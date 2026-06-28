// Lean compiler output
// Module: Lean.Meta.Tactic.UnifyEq
// Imports: Lean.Meta.Tactic.Injection Init.Data.Nat.Linear
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_mkArrow};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_contains;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_index, l_Lean_LocalDecl_toExpr,
    l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAdd, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqOfHEq,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Offset::{l_Lean_Meta_evalNat, l_Lean_Meta_isOffset_x3f};
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assert;
use crate::r#gen::Lean::Meta::Tactic::Clear::{l_Lean_MVarId_clear, l_Lean_MVarId_tryClear};
use crate::r#gen::Lean::Meta::Tactic::Injection::{
    initialize_Lean_Meta_Tactic_Injection, l_Lean_Meta_injectionCore,
    runtime_initialize_Lean_Meta_Tactic_Injection,
};
use crate::r#gen::Lean::Meta::Tactic::Subst::l_Lean_Meta_substCore___boxed;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Recognizers::l_Lean_Expr_isHEq;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [68, 101, 112, 101, 110, 100, 101, 110, 116, 32, 101, 108, 105, 109, 105, 110, 97, 116, 105, 111, 110, 32, 102, 97, 105, 108, 101, 100, 58, 32, 70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 111, 108, 118, 101, 32, 101, 113, 117, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 97, 116, 32, 99, 97, 115, 101, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_unifyEq_x3f___lam__0___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_unifyEq_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [101, 108, 105, 109, 79, 102, 102, 115, 101, 116, 0],
    };
static mut l_Lean_Meta_unifyEq_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__0___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__0___closed__1_value) as *mut LeanObject,
        18023680755638061071 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_unifyEq_x3f___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_unifyEq_x3f___lam__1___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_unifyEq_x3f___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_unifyEq_x3f___lam__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__1___closed__0_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_unifyEq_x3f___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_unifyEq_x3f___lam__1___closed__2_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105,
            116, 121, 44, 32, 98, 117, 116, 32, 102, 111, 117, 110, 100, 0,
        ],
    };
static mut l_Lean_Meta_unifyEq_x3f___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unifyEq_x3f___lam__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_unifyEq_x3f___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unifyEq_x3f___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(
    mut v_mvarId_1286_: *mut LeanObject,
    mut v_eqDecl_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
    mut v_a_1289_: *mut LeanObject,
    mut v_a_1290_: *mut LeanObject,
    mut v_a_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1309_: u8 = 0;
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1313_: u8 = 0;
    let mut v_a_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1317_: u8 = 0;
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_a_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1293_ = l_Lean_LocalDecl_fvarId(v_eqDecl_1287_);
                lean_inc(v___x_1293_);
                v___x_1294_ = l_Lean_mkFVar(v___x_1293_);
                v___x_1295_ = 1;
                v___x_1296_ = l_Lean_Meta_mkEqOfHEq(
                    v___x_1294_,
                    v___x_1295_,
                    v_a_1288_,
                    v_a_1289_,
                    v_a_1290_,
                    v_a_1291_,
                );
                if lean_obj_tag(v___x_1296_) == 0 {
                    v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
                    lean_inc_n(v_a_1297_, 2);
                    lean_dec_ref_known(v___x_1296_, 1);
                    lean_inc(v_a_1291_);
                    lean_inc_ref(v_a_1290_);
                    lean_inc(v_a_1289_);
                    lean_inc_ref(v_a_1288_);
                    v___x_1298_ =
                        lean_infer_type(v_a_1297_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
                    if lean_obj_tag(v___x_1298_) == 0 {
                        v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
                        lean_inc(v_a_1299_);
                        lean_dec_ref_known(v___x_1298_, 1);
                        lean_inc(v_a_1291_);
                        lean_inc_ref(v_a_1290_);
                        lean_inc(v_a_1289_);
                        lean_inc_ref(v_a_1288_);
                        v___x_1300_ =
                            lean_whnf(v_a_1299_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
                        if lean_obj_tag(v___x_1300_) == 0 {
                            v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
                            lean_inc(v_a_1301_);
                            lean_dec_ref_known(v___x_1300_, 1);
                            v___x_1302_ = l_Lean_LocalDecl_userName(v_eqDecl_1287_);
                            v___x_1303_ = l_Lean_MVarId_assert(
                                v_mvarId_1286_,
                                v___x_1302_,
                                v_a_1301_,
                                v_a_1297_,
                                v_a_1288_,
                                v_a_1289_,
                                v_a_1290_,
                                v_a_1291_,
                            );
                            if lean_obj_tag(v___x_1303_) == 0 {
                                v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
                                lean_inc(v_a_1304_);
                                lean_dec_ref_known(v___x_1303_, 1);
                                v___x_1305_ = l_Lean_MVarId_clear(
                                    v_a_1304_,
                                    v___x_1293_,
                                    v_a_1288_,
                                    v_a_1289_,
                                    v_a_1290_,
                                    v_a_1291_,
                                );
                                return v___x_1305_;
                            } else {
                                lean_dec(v___x_1293_);
                                return v___x_1303_;
                            }
                        } else {
                            lean_dec(v_a_1297_);
                            lean_dec(v___x_1293_);
                            lean_dec(v_mvarId_1286_);
                            v_a_1306_ = lean_ctor_get(v___x_1300_, 0);
                            v_isSharedCheck_1313_ = (!lean_is_exclusive(v___x_1300_)) as u8;
                            if v_isSharedCheck_1313_ == 0 {
                                v___x_1308_ = v___x_1300_;
                                v_isShared_1309_ = v_isSharedCheck_1313_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1306_);
                                lean_dec(v___x_1300_);
                                v___x_1308_ = lean_box(0);
                                v_isShared_1309_ = v_isSharedCheck_1313_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1297_);
                        lean_dec(v___x_1293_);
                        lean_dec(v_mvarId_1286_);
                        v_a_1314_ = lean_ctor_get(v___x_1298_, 0);
                        v_isSharedCheck_1321_ = (!lean_is_exclusive(v___x_1298_)) as u8;
                        if v_isSharedCheck_1321_ == 0 {
                            v___x_1316_ = v___x_1298_;
                            v_isShared_1317_ = v_isSharedCheck_1321_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1314_);
                            lean_dec(v___x_1298_);
                            v___x_1316_ = lean_box(0);
                            v_isShared_1317_ = v_isSharedCheck_1321_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1293_);
                    lean_dec(v_mvarId_1286_);
                    v_a_1322_ = lean_ctor_get(v___x_1296_, 0);
                    v_isSharedCheck_1329_ = (!lean_is_exclusive(v___x_1296_)) as u8;
                    if v_isSharedCheck_1329_ == 0 {
                        v___x_1324_ = v___x_1296_;
                        v_isShared_1325_ = v_isSharedCheck_1329_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1322_);
                        lean_dec(v___x_1296_);
                        v___x_1324_ = lean_box(0);
                        v_isShared_1325_ = v_isSharedCheck_1329_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1309_ == 0 {
                    v___x_1311_ = v___x_1308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
                    v___x_1311_ = v_reuseFailAlloc_1312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1311_;
            }
            3 => {
                if v_isShared_1317_ == 0 {
                    v___x_1319_ = v___x_1316_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
                    v___x_1319_ = v_reuseFailAlloc_1320_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1319_;
            }
            5 => {
                if v_isShared_1325_ == 0 {
                    v___x_1327_ = v___x_1324_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
                    v___x_1327_ = v_reuseFailAlloc_1328_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27___boxed(
    mut v_mvarId_1330_: *mut LeanObject,
    mut v_eqDecl_1331_: *mut LeanObject,
    mut v_a_1332_: *mut LeanObject,
    mut v_a_1333_: *mut LeanObject,
    mut v_a_1334_: *mut LeanObject,
    mut v_a_1335_: *mut LeanObject,
    mut v_a_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1337_: *mut LeanObject = core::ptr::null_mut();
    v_res_1337_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(
        v_mvarId_1330_,
        v_eqDecl_1331_,
        v_a_1332_,
        v_a_1333_,
        v_a_1334_,
        v_a_1335_,
    );
    lean_dec(v_a_1335_);
    lean_dec_ref(v_a_1334_);
    lean_dec(v_a_1333_);
    lean_dec_ref(v_a_1332_);
    lean_dec_ref(v_eqDecl_1331_);
    return v_res_1337_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0()
-> *mut LeanObject {
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    v___x_1338_ = lean_unsigned_to_nat(0);
    v___x_1339_ = l_Lean_mkNatLit(v___x_1338_);
    return v___x_1339_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(
    mut v_e_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
    mut v_a_1342_: *mut LeanObject,
    mut v_a_1343_: *mut LeanObject,
    mut v_a_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1364_: u8 = 0;
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut v_a_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1340_);
                v___x_1346_ =
                    l_Lean_Meta_evalNat(v_e_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
                if lean_obj_tag(v___x_1346_) == 0 {
                    v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
                    v_isSharedCheck_1365_ = (!lean_is_exclusive(v___x_1346_)) as u8;
                    if v_isSharedCheck_1365_ == 0 {
                        v___x_1349_ = v___x_1346_;
                        v_isShared_1350_ = v_isSharedCheck_1365_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1347_);
                        lean_dec(v___x_1346_);
                        v___x_1349_ = lean_box(0);
                        v_isShared_1350_ = v_isSharedCheck_1365_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1340_);
                    v_a_1366_ = lean_ctor_get(v___x_1346_, 0);
                    v_isSharedCheck_1373_ = (!lean_is_exclusive(v___x_1346_)) as u8;
                    if v_isSharedCheck_1373_ == 0 {
                        v___x_1368_ = v___x_1346_;
                        v_isShared_1369_ = v_isSharedCheck_1373_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1366_);
                        lean_dec(v___x_1346_);
                        v___x_1368_ = lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1373_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1347_) == 0 {
                    lean_del_object(v___x_1349_);
                    v___x_1351_ = l_Lean_Meta_isOffset_x3f(
                        v_e_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_,
                    );
                    return v___x_1351_;
                } else {
                    lean_dec_ref(v_e_1340_);
                    v_val_1352_ = lean_ctor_get(v_a_1347_, 0);
                    v_isSharedCheck_1364_ = (!lean_is_exclusive(v_a_1347_)) as u8;
                    if v_isSharedCheck_1364_ == 0 {
                        v___x_1354_ = v_a_1347_;
                        v_isShared_1355_ = v_isSharedCheck_1364_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1352_);
                        lean_dec(v_a_1347_);
                        v___x_1354_ = lean_box(0);
                        v_isShared_1355_ = v_isSharedCheck_1364_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1356_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0_once), _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___closed__0);
                v___x_1357_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                lean_ctor_set(v___x_1357_, 1, v_val_1352_);
                if v_isShared_1355_ == 0 {
                    lean_ctor_set(v___x_1354_, 0, v___x_1357_);
                    v___x_1359_ = v___x_1354_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1357_);
                    v___x_1359_ = v_reuseFailAlloc_1363_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1350_ == 0 {
                    lean_ctor_set(v___x_1349_, 0, v___x_1359_);
                    v___x_1361_ = v___x_1349_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1361_;
            }
            5 => {
                if v_isShared_1369_ == 0 {
                    v___x_1371_ = v___x_1368_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
                    v___x_1371_ = v_reuseFailAlloc_1372_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f___boxed(
    mut v_e_1374_: *mut LeanObject,
    mut v_a_1375_: *mut LeanObject,
    mut v_a_1376_: *mut LeanObject,
    mut v_a_1377_: *mut LeanObject,
    mut v_a_1378_: *mut LeanObject,
    mut v_a_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1380_: *mut LeanObject = core::ptr::null_mut();
    v_res_1380_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(
        v_e_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_,
    );
    lean_dec(v_a_1378_);
    lean_dec_ref(v_a_1377_);
    lean_dec(v_a_1376_);
    lean_dec_ref(v_a_1375_);
    return v_res_1380_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(
    mut v_x_1381_: *mut LeanObject,
    mut v___y_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_a_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v___y_1404_: u8 = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1408_: u8 = 0;
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut v_unused_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut v___x_1427_: u8 = 0;
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut v_a_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1432_: u8 = 0;
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1387_ = l_Lean_Meta_saveState___redArg(v___y_1383_, v___y_1385_);
                if lean_obj_tag(v___x_1387_) == 0 {
                    v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
                    lean_inc(v_a_1388_);
                    lean_dec_ref_known(v___x_1387_, 1);
                    lean_inc(v___y_1385_);
                    lean_inc_ref(v___y_1384_);
                    lean_inc(v___y_1383_);
                    lean_inc_ref(v___y_1382_);
                    v___x_1389_ = lean_apply_5(
                        v_x_1381_,
                        v___y_1382_,
                        v___y_1383_,
                        v___y_1384_,
                        v___y_1385_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1389_) == 0 {
                        lean_dec(v_a_1388_);
                        v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
                        v_isSharedCheck_1398_ = (!lean_is_exclusive(v___x_1389_)) as u8;
                        if v_isSharedCheck_1398_ == 0 {
                            v___x_1392_ = v___x_1389_;
                            v_isShared_1393_ = v_isSharedCheck_1398_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1390_);
                            lean_dec(v___x_1389_);
                            v___x_1392_ = lean_box(0);
                            v_isShared_1393_ = v_isSharedCheck_1398_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1399_ = lean_ctor_get(v___x_1389_, 0);
                        v_isSharedCheck_1428_ = (!lean_is_exclusive(v___x_1389_)) as u8;
                        if v_isSharedCheck_1428_ == 0 {
                            v___x_1401_ = v___x_1389_;
                            v_isShared_1402_ = v_isSharedCheck_1428_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1399_);
                            lean_dec(v___x_1389_);
                            v___x_1401_ = lean_box(0);
                            v_isShared_1402_ = v_isSharedCheck_1428_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_1381_);
                    v_a_1429_ = lean_ctor_get(v___x_1387_, 0);
                    v_isSharedCheck_1436_ = (!lean_is_exclusive(v___x_1387_)) as u8;
                    if v_isSharedCheck_1436_ == 0 {
                        v___x_1431_ = v___x_1387_;
                        v_isShared_1432_ = v_isSharedCheck_1436_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1429_);
                        lean_dec(v___x_1387_);
                        v___x_1431_ = lean_box(0);
                        v_isShared_1432_ = v_isSharedCheck_1436_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1394_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1394_, 0, v_a_1390_);
                if v_isShared_1393_ == 0 {
                    lean_ctor_set(v___x_1392_, 0, v___x_1394_);
                    v___x_1396_ = v___x_1392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
                    v___x_1396_ = v_reuseFailAlloc_1397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1396_;
            }
            3 => {
                v___x_1426_ = l_Lean_Exception_isInterrupt(v_a_1399_);
                if v___x_1426_ == 0 {
                    lean_inc(v_a_1399_);
                    v___x_1427_ = l_Lean_Exception_isRuntime(v_a_1399_);
                    v___y_1404_ = v___x_1427_;
                    state = 4;
                    continue;
                } else {
                    v___y_1404_ = v___x_1426_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_1404_ == 0 {
                    lean_del_object(v___x_1401_);
                    lean_dec(v_a_1399_);
                    v___x_1405_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_1388_,
                        v___y_1383_,
                        v___y_1385_,
                    );
                    lean_dec(v_a_1388_);
                    if lean_obj_tag(v___x_1405_) == 0 {
                        v_isSharedCheck_1413_ = (!lean_is_exclusive(v___x_1405_)) as u8;
                        if v_isSharedCheck_1413_ == 0 {
                            v_unused_1414_ = lean_ctor_get(v___x_1405_, 0);
                            lean_dec(v_unused_1414_);
                            v___x_1407_ = v___x_1405_;
                            v_isShared_1408_ = v_isSharedCheck_1413_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_1405_);
                            v___x_1407_ = lean_box(0);
                            v_isShared_1408_ = v_isSharedCheck_1413_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1415_ = lean_ctor_get(v___x_1405_, 0);
                        v_isSharedCheck_1422_ = (!lean_is_exclusive(v___x_1405_)) as u8;
                        if v_isSharedCheck_1422_ == 0 {
                            v___x_1417_ = v___x_1405_;
                            v_isShared_1418_ = v_isSharedCheck_1422_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1415_);
                            lean_dec(v___x_1405_);
                            v___x_1417_ = lean_box(0);
                            v_isShared_1418_ = v_isSharedCheck_1422_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1388_);
                    if v_isShared_1402_ == 0 {
                        v___x_1424_ = v___x_1401_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1399_);
                        v___x_1424_ = v_reuseFailAlloc_1425_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1409_ = lean_box(0);
                if v_isShared_1408_ == 0 {
                    lean_ctor_set(v___x_1407_, 0, v___x_1409_);
                    v___x_1411_ = v___x_1407_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
                    v___x_1411_ = v_reuseFailAlloc_1412_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1411_;
            }
            7 => {
                if v_isShared_1418_ == 0 {
                    v___x_1420_ = v___x_1417_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
                    v___x_1420_ = v_reuseFailAlloc_1421_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1420_;
            }
            9 => {
                return v___x_1424_;
            }
            10 => {
                if v_isShared_1432_ == 0 {
                    v___x_1434_ = v___x_1431_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
                    v___x_1434_ = v_reuseFailAlloc_1435_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg___boxed(
    mut v_x_1437_: *mut LeanObject,
    mut v___y_1438_: *mut LeanObject,
    mut v___y_1439_: *mut LeanObject,
    mut v___y_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1443_: *mut LeanObject = core::ptr::null_mut();
    v_res_1443_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
    lean_dec(v___y_1441_);
    lean_dec_ref(v___y_1440_);
    lean_dec(v___y_1439_);
    lean_dec_ref(v___y_1438_);
    return v_res_1443_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(
    mut v_00_u03b1_1444_: *mut LeanObject,
    mut v_x_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    v___x_1451_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
    return v___x_1451_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___boxed(
    mut v_00_u03b1_1452_: *mut LeanObject,
    mut v_x_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
    mut v___y_1455_: *mut LeanObject,
    mut v___y_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1459_: *mut LeanObject = core::ptr::null_mut();
    v_res_1459_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0(v_00_u03b1_1452_, v_x_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
    lean_dec(v___y_1457_);
    lean_dec_ref(v___y_1456_);
    lean_dec(v___y_1455_);
    lean_dec_ref(v___y_1454_);
    return v_res_1459_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(
    mut v_msgData_1460_: *mut LeanObject,
    mut v___y_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    v___x_1466_ = lean_st_ref_get(v___y_1464_);
    v_env_1467_ = lean_ctor_get(v___x_1466_, 0);
    lean_inc_ref(v_env_1467_);
    lean_dec(v___x_1466_);
    v___x_1468_ = lean_st_ref_get(v___y_1462_);
    v_mctx_1469_ = lean_ctor_get(v___x_1468_, 0);
    lean_inc_ref(v_mctx_1469_);
    lean_dec(v___x_1468_);
    v_lctx_1470_ = lean_ctor_get(v___y_1461_, 2);
    v_options_1471_ = lean_ctor_get(v___y_1463_, 2);
    lean_inc_ref(v_options_1471_);
    lean_inc_ref(v_lctx_1470_);
    v___x_1472_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1472_, 0, v_env_1467_);
    lean_ctor_set(v___x_1472_, 1, v_mctx_1469_);
    lean_ctor_set(v___x_1472_, 2, v_lctx_1470_);
    lean_ctor_set(v___x_1472_, 3, v_options_1471_);
    v___x_1473_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1473_, 0, v___x_1472_);
    lean_ctor_set(v___x_1473_, 1, v_msgData_1460_);
    v___x_1474_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1474_, 0, v___x_1473_);
    return v___x_1474_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1___boxed(
    mut v_msgData_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
    mut v___y_1478_: *mut LeanObject,
    mut v___y_1479_: *mut LeanObject,
    mut v___y_1480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1481_: *mut LeanObject = core::ptr::null_mut();
    v_res_1481_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msgData_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
    lean_dec(v___y_1479_);
    lean_dec_ref(v___y_1478_);
    lean_dec(v___y_1477_);
    lean_dec_ref(v___y_1476_);
    return v_res_1481_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(
    mut v_msg_1482_: *mut LeanObject,
    mut v___y_1483_: *mut LeanObject,
    mut v___y_1484_: *mut LeanObject,
    mut v___y_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1488_ = lean_ctor_get(v___y_1485_, 5);
                v___x_1489_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1_spec__1(v_msg_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
                v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
                v_isSharedCheck_1498_ = (!lean_is_exclusive(v___x_1489_)) as u8;
                if v_isSharedCheck_1498_ == 0 {
                    v___x_1492_ = v___x_1489_;
                    v_isShared_1493_ = v_isSharedCheck_1498_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1490_);
                    lean_dec(v___x_1489_);
                    v___x_1492_ = lean_box(0);
                    v_isShared_1493_ = v_isSharedCheck_1498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1488_);
                v___x_1494_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1494_, 0, v_ref_1488_);
                lean_ctor_set(v___x_1494_, 1, v_a_1490_);
                if v_isShared_1493_ == 0 {
                    lean_ctor_set_tag(v___x_1492_, 1);
                    lean_ctor_set(v___x_1492_, 0, v___x_1494_);
                    v___x_1496_ = v___x_1492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
                    v___x_1496_ = v_reuseFailAlloc_1497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg___boxed(
    mut v_msg_1499_: *mut LeanObject,
    mut v___y_1500_: *mut LeanObject,
    mut v___y_1501_: *mut LeanObject,
    mut v___y_1502_: *mut LeanObject,
    mut v___y_1503_: *mut LeanObject,
    mut v___y_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1505_: *mut LeanObject = core::ptr::null_mut();
    v_res_1505_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
    lean_dec(v___y_1503_);
    lean_dec_ref(v___y_1502_);
    lean_dec(v___y_1501_);
    lean_dec_ref(v___y_1500_);
    return v_res_1505_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1()
-> *mut LeanObject {
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    v___x_1507_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__0;
    v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
    return v___x_1508_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(
    mut v_mvarId_1509_: *mut LeanObject,
    mut v_eqFVarId_1510_: *mut LeanObject,
    mut v_subst_1511_: *mut LeanObject,
    mut v_acyclic_1512_: *mut LeanObject,
    mut v_eqDecl_1513_: *mut LeanObject,
    mut v_a_1514_: *mut LeanObject,
    mut v_b_1515_: *mut LeanObject,
    mut v_symm_1516_: u8,
    mut v_a_1517_: *mut LeanObject,
    mut v_a_1518_: *mut LeanObject,
    mut v_a_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1531_: u8 = 0;
    let mut v_val_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v_fst_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1566_: u8 = 0;
    let mut v_a_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut v_a_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut v_a_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1598_: u8 = 0;
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1602_: u8 = 0;
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_a_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1522_ = 1;
                v___x_1523_ = lean_box((v_symm_1516_) as usize);
                v___x_1524_ = lean_box((v___x_1522_) as usize);
                v___x_1525_ = lean_box((v___x_1522_) as usize);
                lean_inc(v_subst_1511_);
                lean_inc(v_eqFVarId_1510_);
                lean_inc(v_mvarId_1509_);
                v___x_1526_ = lean_alloc_closure(
                    l_Lean_Meta_substCore___boxed as *mut core::ffi::c_void,
                    11,
                    6,
                );
                lean_closure_set(v___x_1526_, 0, v_mvarId_1509_);
                lean_closure_set(v___x_1526_, 1, v_eqFVarId_1510_);
                lean_closure_set(v___x_1526_, 2, v___x_1523_);
                lean_closure_set(v___x_1526_, 3, v_subst_1511_);
                lean_closure_set(v___x_1526_, 4, v___x_1524_);
                lean_closure_set(v___x_1526_, 5, v___x_1525_);
                v___x_1527_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__0___redArg(v___x_1526_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
                if lean_obj_tag(v___x_1527_) == 0 {
                    v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
                    v_isSharedCheck_1603_ = (!lean_is_exclusive(v___x_1527_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1530_ = v___x_1527_;
                        v_isShared_1531_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1528_);
                        lean_dec(v___x_1527_);
                        v___x_1530_ = lean_box(0);
                        v_isShared_1531_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_b_1515_);
                    lean_dec_ref(v_a_1514_);
                    lean_dec_ref(v_acyclic_1512_);
                    lean_dec(v_subst_1511_);
                    lean_dec(v_eqFVarId_1510_);
                    lean_dec(v_mvarId_1509_);
                    v_a_1604_ = lean_ctor_get(v___x_1527_, 0);
                    v_isSharedCheck_1611_ = (!lean_is_exclusive(v___x_1527_)) as u8;
                    if v_isSharedCheck_1611_ == 0 {
                        v___x_1606_ = v___x_1527_;
                        v_isShared_1607_ = v_isSharedCheck_1611_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_1604_);
                        lean_dec(v___x_1527_);
                        v___x_1606_ = lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1611_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1528_) == 1 {
                    lean_dec_ref(v_b_1515_);
                    lean_dec_ref(v_a_1514_);
                    lean_dec_ref(v_acyclic_1512_);
                    lean_dec(v_subst_1511_);
                    lean_dec(v_eqFVarId_1510_);
                    lean_dec(v_mvarId_1509_);
                    v_val_1532_ = lean_ctor_get(v_a_1528_, 0);
                    v_isSharedCheck_1546_ = (!lean_is_exclusive(v_a_1528_)) as u8;
                    if v_isSharedCheck_1546_ == 0 {
                        v___x_1534_ = v_a_1528_;
                        v_isShared_1535_ = v_isSharedCheck_1546_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1532_);
                        lean_dec(v_a_1528_);
                        v___x_1534_ = lean_box(0);
                        v_isShared_1535_ = v_isSharedCheck_1546_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1530_);
                    lean_dec(v_a_1528_);
                    v___x_1547_ = l_Lean_Meta_isExprDefEq(
                        v_a_1514_, v_b_1515_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_,
                    );
                    if lean_obj_tag(v___x_1547_) == 0 {
                        v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
                        lean_inc(v_a_1548_);
                        lean_dec_ref_known(v___x_1547_, 1);
                        v___x_1549_ = (lean_unbox(v_a_1548_) as u8);
                        lean_dec(v_a_1548_);
                        if v___x_1549_ == 0 {
                            lean_dec(v_subst_1511_);
                            v___x_1550_ = l_Lean_mkFVar(v_eqFVarId_1510_);
                            lean_inc(v_a_1520_);
                            lean_inc_ref(v_a_1519_);
                            lean_inc(v_a_1518_);
                            lean_inc_ref(v_a_1517_);
                            v___x_1551_ = lean_apply_7(
                                v_acyclic_1512_,
                                v_mvarId_1509_,
                                v___x_1550_,
                                v_a_1517_,
                                v_a_1518_,
                                v_a_1519_,
                                v_a_1520_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_1551_) == 0 {
                                v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
                                v_isSharedCheck_1566_ = (!lean_is_exclusive(v___x_1551_)) as u8;
                                if v_isSharedCheck_1566_ == 0 {
                                    v___x_1554_ = v___x_1551_;
                                    v_isShared_1555_ = v_isSharedCheck_1566_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_1552_);
                                    lean_dec(v___x_1551_);
                                    v___x_1554_ = lean_box(0);
                                    v_isShared_1555_ = v_isSharedCheck_1566_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_1567_ = lean_ctor_get(v___x_1551_, 0);
                                v_isSharedCheck_1574_ = (!lean_is_exclusive(v___x_1551_)) as u8;
                                if v_isSharedCheck_1574_ == 0 {
                                    v___x_1569_ = v___x_1551_;
                                    v_isShared_1570_ = v_isSharedCheck_1574_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_1567_);
                                    lean_dec(v___x_1551_);
                                    v___x_1569_ = lean_box(0);
                                    v_isShared_1570_ = v_isSharedCheck_1574_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_acyclic_1512_);
                            v___x_1575_ = l_Lean_MVarId_clear(
                                v_mvarId_1509_,
                                v_eqFVarId_1510_,
                                v_a_1517_,
                                v_a_1518_,
                                v_a_1519_,
                                v_a_1520_,
                            );
                            if lean_obj_tag(v___x_1575_) == 0 {
                                v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
                                v_isSharedCheck_1586_ = (!lean_is_exclusive(v___x_1575_)) as u8;
                                if v_isSharedCheck_1586_ == 0 {
                                    v___x_1578_ = v___x_1575_;
                                    v_isShared_1579_ = v_isSharedCheck_1586_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_1576_);
                                    lean_dec(v___x_1575_);
                                    v___x_1578_ = lean_box(0);
                                    v_isShared_1579_ = v_isSharedCheck_1586_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                lean_dec(v_subst_1511_);
                                v_a_1587_ = lean_ctor_get(v___x_1575_, 0);
                                v_isSharedCheck_1594_ = (!lean_is_exclusive(v___x_1575_)) as u8;
                                if v_isSharedCheck_1594_ == 0 {
                                    v___x_1589_ = v___x_1575_;
                                    v_isShared_1590_ = v_isSharedCheck_1594_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_1587_);
                                    lean_dec(v___x_1575_);
                                    v___x_1589_ = lean_box(0);
                                    v_isShared_1590_ = v_isSharedCheck_1594_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_acyclic_1512_);
                        lean_dec(v_subst_1511_);
                        lean_dec(v_eqFVarId_1510_);
                        lean_dec(v_mvarId_1509_);
                        v_a_1595_ = lean_ctor_get(v___x_1547_, 0);
                        v_isSharedCheck_1602_ = (!lean_is_exclusive(v___x_1547_)) as u8;
                        if v_isSharedCheck_1602_ == 0 {
                            v___x_1597_ = v___x_1547_;
                            v_isShared_1598_ = v_isSharedCheck_1602_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_1595_);
                            lean_dec(v___x_1547_);
                            v___x_1597_ = lean_box(0);
                            v_isShared_1598_ = v_isSharedCheck_1602_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_fst_1536_ = lean_ctor_get(v_val_1532_, 0);
                lean_inc(v_fst_1536_);
                v_snd_1537_ = lean_ctor_get(v_val_1532_, 1);
                lean_inc(v_snd_1537_);
                lean_dec(v_val_1532_);
                v___x_1538_ = lean_unsigned_to_nat(0);
                v___x_1539_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1539_, 0, v_snd_1537_);
                lean_ctor_set(v___x_1539_, 1, v_fst_1536_);
                lean_ctor_set(v___x_1539_, 2, v___x_1538_);
                if v_isShared_1535_ == 0 {
                    lean_ctor_set(v___x_1534_, 0, v___x_1539_);
                    v___x_1541_ = v___x_1534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1539_);
                    v___x_1541_ = v_reuseFailAlloc_1545_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1531_ == 0 {
                    lean_ctor_set(v___x_1530_, 0, v___x_1541_);
                    v___x_1543_ = v___x_1530_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
                    v___x_1543_ = v_reuseFailAlloc_1544_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1543_;
            }
            5 => {
                v___x_1556_ = (lean_unbox(v_a_1552_) as u8);
                lean_dec(v_a_1552_);
                if v___x_1556_ == 0 {
                    lean_del_object(v___x_1554_);
                    v___x_1557_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once), _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
                    v___x_1558_ = l_Lean_LocalDecl_type(v_eqDecl_1513_);
                    v___x_1559_ = l_Lean_indentExpr(v___x_1558_);
                    v___x_1560_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1560_, 0, v___x_1557_);
                    lean_ctor_set(v___x_1560_, 1, v___x_1559_);
                    v___x_1561_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1560_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
                    return v___x_1561_;
                } else {
                    v___x_1562_ = lean_box(0);
                    if v_isShared_1555_ == 0 {
                        lean_ctor_set(v___x_1554_, 0, v___x_1562_);
                        v___x_1564_ = v___x_1554_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
                        v___x_1564_ = v_reuseFailAlloc_1565_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1564_;
            }
            7 => {
                if v_isShared_1570_ == 0 {
                    v___x_1572_ = v___x_1569_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
                    v___x_1572_ = v_reuseFailAlloc_1573_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1572_;
            }
            9 => {
                v___x_1580_ = lean_unsigned_to_nat(0);
                v___x_1581_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1581_, 0, v_a_1576_);
                lean_ctor_set(v___x_1581_, 1, v_subst_1511_);
                lean_ctor_set(v___x_1581_, 2, v___x_1580_);
                v___x_1582_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1582_, 0, v___x_1581_);
                if v_isShared_1579_ == 0 {
                    lean_ctor_set(v___x_1578_, 0, v___x_1582_);
                    v___x_1584_ = v___x_1578_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
                    v___x_1584_ = v_reuseFailAlloc_1585_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1584_;
            }
            11 => {
                if v_isShared_1590_ == 0 {
                    v___x_1592_ = v___x_1589_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
                    v___x_1592_ = v_reuseFailAlloc_1593_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1592_;
            }
            13 => {
                if v_isShared_1598_ == 0 {
                    v___x_1600_ = v___x_1597_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
                    v___x_1600_ = v_reuseFailAlloc_1601_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1600_;
            }
            15 => {
                if v_isShared_1607_ == 0 {
                    v___x_1609_ = v___x_1606_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
                    v___x_1609_ = v_reuseFailAlloc_1610_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___boxed(
    mut v_mvarId_1612_: *mut LeanObject,
    mut v_eqFVarId_1613_: *mut LeanObject,
    mut v_subst_1614_: *mut LeanObject,
    mut v_acyclic_1615_: *mut LeanObject,
    mut v_eqDecl_1616_: *mut LeanObject,
    mut v_a_1617_: *mut LeanObject,
    mut v_b_1618_: *mut LeanObject,
    mut v_symm_1619_: *mut LeanObject,
    mut v_a_1620_: *mut LeanObject,
    mut v_a_1621_: *mut LeanObject,
    mut v_a_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_1625_: u8 = 0;
    let mut v_res_1626_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_1625_ = (lean_unbox(v_symm_1619_) as u8);
    v_res_1626_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(
        v_mvarId_1612_,
        v_eqFVarId_1613_,
        v_subst_1614_,
        v_acyclic_1615_,
        v_eqDecl_1616_,
        v_a_1617_,
        v_b_1618_,
        v_symm_boxed_1625_,
        v_a_1620_,
        v_a_1621_,
        v_a_1622_,
        v_a_1623_,
    );
    lean_dec(v_a_1623_);
    lean_dec_ref(v_a_1622_);
    lean_dec(v_a_1621_);
    lean_dec_ref(v_a_1620_);
    lean_dec_ref(v_eqDecl_1616_);
    return v_res_1626_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(
    mut v_00_u03b1_1627_: *mut LeanObject,
    mut v_msg_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
    mut v___y_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
    mut v___y_1632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    v___x_1634_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v_msg_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
    return v___x_1634_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___boxed(
    mut v_00_u03b1_1635_: *mut LeanObject,
    mut v_msg_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1642_: *mut LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1(v_00_u03b1_1635_, v_msg_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
    lean_dec(v___y_1640_);
    lean_dec_ref(v___y_1639_);
    lean_dec(v___y_1638_);
    lean_dec_ref(v___y_1637_);
    return v_res_1642_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1()
-> *mut LeanObject {
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    v___x_1644_ =
        l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__0;
    v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3()
-> *mut LeanObject {
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    v___x_1647_ =
        l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__2;
    v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(
    mut v_mvarId_1649_: *mut LeanObject,
    mut v_eqFVarId_1650_: *mut LeanObject,
    mut v_subst_1651_: *mut LeanObject,
    mut v_caseName_x3f_1652_: *mut LeanObject,
    mut v_eqDecl_1653_: *mut LeanObject,
    mut v_injectionOffset_x3f_1654_: *mut LeanObject,
    mut v_a_1655_: *mut LeanObject,
    mut v_b_1656_: *mut LeanObject,
    mut v_a_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
    mut v_a_1659_: *mut LeanObject,
    mut v_a_1660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1675_: u8 = 0;
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1682_: u8 = 0;
    let mut v_a_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1690_: u8 = 0;
    let mut v_a_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1698_: u8 = 0;
    let mut v_a_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1702_: u8 = 0;
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1706_: u8 = 0;
    let mut v___y_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut v_a_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1755_: u8 = 0;
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numNewEqs_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut v_a_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1775_: u8 = 0;
    let mut v_a_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v_val_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_a_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1660_);
                lean_inc_ref(v_a_1659_);
                lean_inc(v_a_1658_);
                lean_inc_ref(v_a_1657_);
                lean_inc_ref(v_b_1656_);
                lean_inc_ref(v_a_1655_);
                v___x_1784_ = lean_apply_7(
                    v_injectionOffset_x3f_1654_,
                    v_a_1655_,
                    v_b_1656_,
                    v_a_1657_,
                    v_a_1658_,
                    v_a_1659_,
                    v_a_1660_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1784_) == 0 {
                    v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
                    v_isSharedCheck_1806_ = (!lean_is_exclusive(v___x_1784_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1787_ = v___x_1784_;
                        v_isShared_1788_ = v_isSharedCheck_1806_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_1785_);
                        lean_dec(v___x_1784_);
                        v___x_1787_ = lean_box(0);
                        v_isShared_1788_ = v_isSharedCheck_1806_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_b_1656_);
                    lean_dec_ref(v_a_1655_);
                    lean_dec(v_caseName_x3f_1652_);
                    lean_dec(v_subst_1651_);
                    lean_dec(v_eqFVarId_1650_);
                    lean_dec(v_mvarId_1649_);
                    v_a_1807_ = lean_ctor_get(v___x_1784_, 0);
                    v_isSharedCheck_1814_ = (!lean_is_exclusive(v___x_1784_)) as u8;
                    if v_isSharedCheck_1814_ == 0 {
                        v___x_1809_ = v___x_1784_;
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 26;
                        continue;
                    } else {
                        lean_inc(v_a_1807_);
                        lean_dec(v___x_1784_);
                        v___x_1809_ = lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1665_ = l_Lean_Meta_mkEq(
                    v___y_1663_,
                    v___y_1664_,
                    v_a_1657_,
                    v_a_1658_,
                    v_a_1659_,
                    v_a_1660_,
                );
                if lean_obj_tag(v___x_1665_) == 0 {
                    v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
                    lean_inc(v_a_1666_);
                    lean_dec_ref_known(v___x_1665_, 1);
                    lean_inc(v_eqFVarId_1650_);
                    v___x_1667_ = l_Lean_mkFVar(v_eqFVarId_1650_);
                    v___x_1668_ = l_Lean_LocalDecl_userName(v_eqDecl_1653_);
                    v___x_1669_ = l_Lean_MVarId_assert(
                        v_mvarId_1649_,
                        v___x_1668_,
                        v_a_1666_,
                        v___x_1667_,
                        v_a_1657_,
                        v_a_1658_,
                        v_a_1659_,
                        v_a_1660_,
                    );
                    if lean_obj_tag(v___x_1669_) == 0 {
                        v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
                        lean_inc(v_a_1670_);
                        lean_dec_ref_known(v___x_1669_, 1);
                        v___x_1671_ = l_Lean_MVarId_clear(
                            v_a_1670_,
                            v_eqFVarId_1650_,
                            v_a_1657_,
                            v_a_1658_,
                            v_a_1659_,
                            v_a_1660_,
                        );
                        if lean_obj_tag(v___x_1671_) == 0 {
                            v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
                            v_isSharedCheck_1682_ = (!lean_is_exclusive(v___x_1671_)) as u8;
                            if v_isSharedCheck_1682_ == 0 {
                                v___x_1674_ = v___x_1671_;
                                v_isShared_1675_ = v_isSharedCheck_1682_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1672_);
                                lean_dec(v___x_1671_);
                                v___x_1674_ = lean_box(0);
                                v_isShared_1675_ = v_isSharedCheck_1682_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_subst_1651_);
                            v_a_1683_ = lean_ctor_get(v___x_1671_, 0);
                            v_isSharedCheck_1690_ = (!lean_is_exclusive(v___x_1671_)) as u8;
                            if v_isSharedCheck_1690_ == 0 {
                                v___x_1685_ = v___x_1671_;
                                v_isShared_1686_ = v_isSharedCheck_1690_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1683_);
                                lean_dec(v___x_1671_);
                                v___x_1685_ = lean_box(0);
                                v_isShared_1686_ = v_isSharedCheck_1690_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_subst_1651_);
                        lean_dec(v_eqFVarId_1650_);
                        v_a_1691_ = lean_ctor_get(v___x_1669_, 0);
                        v_isSharedCheck_1698_ = (!lean_is_exclusive(v___x_1669_)) as u8;
                        if v_isSharedCheck_1698_ == 0 {
                            v___x_1693_ = v___x_1669_;
                            v_isShared_1694_ = v_isSharedCheck_1698_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1691_);
                            lean_dec(v___x_1669_);
                            v___x_1693_ = lean_box(0);
                            v_isShared_1694_ = v_isSharedCheck_1698_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_subst_1651_);
                    lean_dec(v_eqFVarId_1650_);
                    lean_dec(v_mvarId_1649_);
                    v_a_1699_ = lean_ctor_get(v___x_1665_, 0);
                    v_isSharedCheck_1706_ = (!lean_is_exclusive(v___x_1665_)) as u8;
                    if v_isSharedCheck_1706_ == 0 {
                        v___x_1701_ = v___x_1665_;
                        v_isShared_1702_ = v_isSharedCheck_1706_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1699_);
                        lean_dec(v___x_1665_);
                        v___x_1701_ = lean_box(0);
                        v_isShared_1702_ = v_isSharedCheck_1706_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1676_ = lean_unsigned_to_nat(1);
                v___x_1677_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1677_, 0, v_a_1672_);
                lean_ctor_set(v___x_1677_, 1, v_subst_1651_);
                lean_ctor_set(v___x_1677_, 2, v___x_1676_);
                v___x_1678_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                if v_isShared_1675_ == 0 {
                    lean_ctor_set(v___x_1674_, 0, v___x_1678_);
                    v___x_1680_ = v___x_1674_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
                    v___x_1680_ = v_reuseFailAlloc_1681_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1680_;
            }
            4 => {
                if v_isShared_1686_ == 0 {
                    v___x_1688_ = v___x_1685_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
                    v___x_1688_ = v_reuseFailAlloc_1689_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1688_;
            }
            6 => {
                if v_isShared_1694_ == 0 {
                    v___x_1696_ = v___x_1693_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
                    v___x_1696_ = v_reuseFailAlloc_1697_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1696_;
            }
            8 => {
                if v_isShared_1702_ == 0 {
                    v___x_1704_ = v___x_1701_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
                    v___x_1704_ = v_reuseFailAlloc_1705_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1704_;
            }
            10 => {
                if lean_obj_tag(v___y_1708_) == 0 {
                    v_a_1709_ = lean_ctor_get(v___y_1708_, 0);
                    lean_inc(v_a_1709_);
                    lean_dec_ref_known(v___y_1708_, 1);
                    v___x_1710_ = (lean_unbox(v_a_1709_) as u8);
                    if v___x_1710_ == 0 {
                        lean_inc(v_a_1660_);
                        lean_inc_ref(v_a_1659_);
                        lean_inc(v_a_1658_);
                        lean_inc_ref(v_a_1657_);
                        lean_inc_ref(v_a_1655_);
                        v___x_1711_ =
                            lean_whnf(v_a_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
                        if lean_obj_tag(v___x_1711_) == 0 {
                            v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
                            lean_inc(v_a_1712_);
                            lean_dec_ref_known(v___x_1711_, 1);
                            lean_inc(v_a_1660_);
                            lean_inc_ref(v_a_1659_);
                            lean_inc(v_a_1658_);
                            lean_inc_ref(v_a_1657_);
                            lean_inc_ref(v_b_1656_);
                            v___x_1713_ =
                                lean_whnf(v_b_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
                            if lean_obj_tag(v___x_1713_) == 0 {
                                v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
                                lean_inc(v_a_1714_);
                                lean_dec_ref_known(v___x_1713_, 1);
                                v___x_1715_ = lean_expr_eqv(v_a_1712_, v_a_1655_);
                                lean_dec_ref(v_a_1655_);
                                if v___x_1715_ == 0 {
                                    lean_dec(v_a_1709_);
                                    lean_dec_ref(v_b_1656_);
                                    lean_dec(v_caseName_x3f_1652_);
                                    v___y_1663_ = v_a_1712_;
                                    v___y_1664_ = v_a_1714_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1716_ = lean_expr_eqv(v_a_1714_, v_b_1656_);
                                    lean_dec_ref(v_b_1656_);
                                    if v___x_1716_ == 0 {
                                        lean_dec(v_a_1709_);
                                        lean_dec(v_caseName_x3f_1652_);
                                        v___y_1663_ = v_a_1712_;
                                        v___y_1664_ = v_a_1714_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v_a_1714_);
                                        lean_dec(v_a_1712_);
                                        lean_dec(v_subst_1651_);
                                        lean_dec(v_eqFVarId_1650_);
                                        lean_dec(v_mvarId_1649_);
                                        if lean_obj_tag(v_caseName_x3f_1652_) == 0 {
                                            lean_dec(v_a_1709_);
                                            v___x_1717_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once), _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
                                            v___x_1718_ = l_Lean_LocalDecl_type(v_eqDecl_1653_);
                                            v___x_1719_ = l_Lean_indentExpr(v___x_1718_);
                                            v___x_1720_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_1720_, 0, v___x_1717_);
                                            lean_ctor_set(v___x_1720_, 1, v___x_1719_);
                                            v___x_1721_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1720_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
                                            return v___x_1721_;
                                        } else {
                                            v_val_1722_ = lean_ctor_get(v_caseName_x3f_1652_, 0);
                                            lean_inc(v_val_1722_);
                                            lean_dec_ref_known(v_caseName_x3f_1652_, 1);
                                            v___x_1723_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1_once), _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq___closed__1);
                                            v___x_1724_ = l_Lean_LocalDecl_type(v_eqDecl_1653_);
                                            v___x_1725_ = l_Lean_indentExpr(v___x_1724_);
                                            v___x_1726_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_1726_, 0, v___x_1723_);
                                            lean_ctor_set(v___x_1726_, 1, v___x_1725_);
                                            v___x_1727_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1_once), _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__1);
                                            v___x_1728_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_1728_, 0, v___x_1726_);
                                            lean_ctor_set(v___x_1728_, 1, v___x_1727_);
                                            v___x_1729_ = (lean_unbox(v_a_1709_) as u8);
                                            lean_dec(v_a_1709_);
                                            v___x_1730_ = l_Lean_MessageData_ofConstName(
                                                v_val_1722_,
                                                v___x_1729_,
                                            );
                                            v___x_1731_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_1731_, 0, v___x_1728_);
                                            lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                                            v___x_1732_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3_once), _init_l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___closed__3);
                                            v___x_1733_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_1733_, 0, v___x_1731_);
                                            lean_ctor_set(v___x_1733_, 1, v___x_1732_);
                                            v___x_1734_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_1733_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
                                            return v___x_1734_;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_a_1712_);
                                lean_dec(v_a_1709_);
                                lean_dec_ref(v_b_1656_);
                                lean_dec_ref(v_a_1655_);
                                lean_dec(v_caseName_x3f_1652_);
                                lean_dec(v_subst_1651_);
                                lean_dec(v_eqFVarId_1650_);
                                lean_dec(v_mvarId_1649_);
                                v_a_1735_ = lean_ctor_get(v___x_1713_, 0);
                                v_isSharedCheck_1742_ = (!lean_is_exclusive(v___x_1713_)) as u8;
                                if v_isSharedCheck_1742_ == 0 {
                                    v___x_1737_ = v___x_1713_;
                                    v_isShared_1738_ = v_isSharedCheck_1742_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_1735_);
                                    lean_dec(v___x_1713_);
                                    v___x_1737_ = lean_box(0);
                                    v_isShared_1738_ = v_isSharedCheck_1742_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_1709_);
                            lean_dec_ref(v_b_1656_);
                            lean_dec_ref(v_a_1655_);
                            lean_dec(v_caseName_x3f_1652_);
                            lean_dec(v_subst_1651_);
                            lean_dec(v_eqFVarId_1650_);
                            lean_dec(v_mvarId_1649_);
                            v_a_1743_ = lean_ctor_get(v___x_1711_, 0);
                            v_isSharedCheck_1750_ = (!lean_is_exclusive(v___x_1711_)) as u8;
                            if v_isSharedCheck_1750_ == 0 {
                                v___x_1745_ = v___x_1711_;
                                v_isShared_1746_ = v_isSharedCheck_1750_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_1743_);
                                lean_dec(v___x_1711_);
                                v___x_1745_ = lean_box(0);
                                v_isShared_1746_ = v_isSharedCheck_1750_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1709_);
                        lean_dec_ref(v_b_1656_);
                        lean_dec_ref(v_a_1655_);
                        lean_dec(v_caseName_x3f_1652_);
                        v___x_1751_ = l_Lean_Meta_injectionCore(
                            v_mvarId_1649_,
                            v_eqFVarId_1650_,
                            v_a_1657_,
                            v_a_1658_,
                            v_a_1659_,
                            v_a_1660_,
                        );
                        if lean_obj_tag(v___x_1751_) == 0 {
                            v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
                            v_isSharedCheck_1767_ = (!lean_is_exclusive(v___x_1751_)) as u8;
                            if v_isSharedCheck_1767_ == 0 {
                                v___x_1754_ = v___x_1751_;
                                v_isShared_1755_ = v_isSharedCheck_1767_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_1752_);
                                lean_dec(v___x_1751_);
                                v___x_1754_ = lean_box(0);
                                v_isShared_1755_ = v_isSharedCheck_1767_;
                                state = 15;
                                continue;
                            }
                        } else {
                            lean_dec(v_subst_1651_);
                            v_a_1768_ = lean_ctor_get(v___x_1751_, 0);
                            v_isSharedCheck_1775_ = (!lean_is_exclusive(v___x_1751_)) as u8;
                            if v_isSharedCheck_1775_ == 0 {
                                v___x_1770_ = v___x_1751_;
                                v_isShared_1771_ = v_isSharedCheck_1775_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_1768_);
                                lean_dec(v___x_1751_);
                                v___x_1770_ = lean_box(0);
                                v_isShared_1771_ = v_isSharedCheck_1775_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_b_1656_);
                    lean_dec_ref(v_a_1655_);
                    lean_dec(v_caseName_x3f_1652_);
                    lean_dec(v_subst_1651_);
                    lean_dec(v_eqFVarId_1650_);
                    lean_dec(v_mvarId_1649_);
                    v_a_1776_ = lean_ctor_get(v___y_1708_, 0);
                    v_isSharedCheck_1783_ = (!lean_is_exclusive(v___y_1708_)) as u8;
                    if v_isSharedCheck_1783_ == 0 {
                        v___x_1778_ = v___y_1708_;
                        v_isShared_1779_ = v_isSharedCheck_1783_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_1776_);
                        lean_dec(v___y_1708_);
                        v___x_1778_ = lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1783_;
                        state = 20;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_1738_ == 0 {
                    v___x_1740_ = v___x_1737_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
                    v___x_1740_ = v_reuseFailAlloc_1741_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1740_;
            }
            13 => {
                if v_isShared_1746_ == 0 {
                    v___x_1748_ = v___x_1745_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1748_;
            }
            15 => {
                if lean_obj_tag(v_a_1752_) == 0 {
                    lean_dec(v_subst_1651_);
                    v___x_1756_ = lean_box(0);
                    if v_isShared_1755_ == 0 {
                        lean_ctor_set(v___x_1754_, 0, v___x_1756_);
                        v___x_1758_ = v___x_1754_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
                        v___x_1758_ = v_reuseFailAlloc_1759_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_mvarId_1760_ = lean_ctor_get(v_a_1752_, 0);
                    lean_inc(v_mvarId_1760_);
                    v_numNewEqs_1761_ = lean_ctor_get(v_a_1752_, 1);
                    lean_inc(v_numNewEqs_1761_);
                    lean_dec_ref_known(v_a_1752_, 2);
                    v___x_1762_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1762_, 0, v_mvarId_1760_);
                    lean_ctor_set(v___x_1762_, 1, v_subst_1651_);
                    lean_ctor_set(v___x_1762_, 2, v_numNewEqs_1761_);
                    v___x_1763_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                    if v_isShared_1755_ == 0 {
                        lean_ctor_set(v___x_1754_, 0, v___x_1763_);
                        v___x_1765_ = v___x_1754_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
                        v___x_1765_ = v_reuseFailAlloc_1766_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_1758_;
            }
            17 => {
                return v___x_1765_;
            }
            18 => {
                if v_isShared_1771_ == 0 {
                    v___x_1773_ = v___x_1770_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
                    v___x_1773_ = v_reuseFailAlloc_1774_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1773_;
            }
            20 => {
                if v_isShared_1779_ == 0 {
                    v___x_1781_ = v___x_1778_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
                    v___x_1781_ = v_reuseFailAlloc_1782_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1781_;
            }
            22 => {
                if lean_obj_tag(v_a_1785_) == 1 {
                    lean_dec_ref(v_b_1656_);
                    lean_dec_ref(v_a_1655_);
                    lean_dec(v_caseName_x3f_1652_);
                    lean_dec(v_eqFVarId_1650_);
                    lean_dec(v_mvarId_1649_);
                    v_val_1789_ = lean_ctor_get(v_a_1785_, 0);
                    v_isSharedCheck_1801_ = (!lean_is_exclusive(v_a_1785_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1791_ = v_a_1785_;
                        v_isShared_1792_ = v_isSharedCheck_1801_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_val_1789_);
                        lean_dec(v_a_1785_);
                        v___x_1791_ = lean_box(0);
                        v_isShared_1792_ = v_isSharedCheck_1801_;
                        state = 23;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1787_);
                    lean_dec(v_a_1785_);
                    lean_inc_ref(v_a_1655_);
                    v___x_1802_ = l_Lean_Meta_isConstructorApp(
                        v_a_1655_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_,
                    );
                    if lean_obj_tag(v___x_1802_) == 0 {
                        v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
                        lean_inc(v_a_1803_);
                        v___x_1804_ = (lean_unbox(v_a_1803_) as u8);
                        lean_dec(v_a_1803_);
                        if v___x_1804_ == 0 {
                            v___y_1708_ = v___x_1802_;
                            state = 10;
                            continue;
                        } else {
                            lean_dec_ref_known(v___x_1802_, 1);
                            lean_inc_ref(v_b_1656_);
                            v___x_1805_ = l_Lean_Meta_isConstructorApp(
                                v_b_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_,
                            );
                            v___y_1708_ = v___x_1805_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___y_1708_ = v___x_1802_;
                        state = 10;
                        continue;
                    }
                }
            }
            23 => {
                v___x_1793_ = lean_unsigned_to_nat(1);
                v___x_1794_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1794_, 0, v_val_1789_);
                lean_ctor_set(v___x_1794_, 1, v_subst_1651_);
                lean_ctor_set(v___x_1794_, 2, v___x_1793_);
                if v_isShared_1792_ == 0 {
                    lean_ctor_set(v___x_1791_, 0, v___x_1794_);
                    v___x_1796_ = v___x_1791_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1794_);
                    v___x_1796_ = v_reuseFailAlloc_1800_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_1788_ == 0 {
                    lean_ctor_set(v___x_1787_, 0, v___x_1796_);
                    v___x_1798_ = v___x_1787_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
                    v___x_1798_ = v_reuseFailAlloc_1799_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1798_;
            }
            26 => {
                if v_isShared_1810_ == 0 {
                    v___x_1812_ = v___x_1809_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
                    v___x_1812_ = v_reuseFailAlloc_1813_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection___boxed(
    mut v_mvarId_1815_: *mut LeanObject,
    mut v_eqFVarId_1816_: *mut LeanObject,
    mut v_subst_1817_: *mut LeanObject,
    mut v_caseName_x3f_1818_: *mut LeanObject,
    mut v_eqDecl_1819_: *mut LeanObject,
    mut v_injectionOffset_x3f_1820_: *mut LeanObject,
    mut v_a_1821_: *mut LeanObject,
    mut v_b_1822_: *mut LeanObject,
    mut v_a_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1828_: *mut LeanObject = core::ptr::null_mut();
    v_res_1828_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(
        v_mvarId_1815_,
        v_eqFVarId_1816_,
        v_subst_1817_,
        v_caseName_x3f_1818_,
        v_eqDecl_1819_,
        v_injectionOffset_x3f_1820_,
        v_a_1821_,
        v_b_1822_,
        v_a_1823_,
        v_a_1824_,
        v_a_1825_,
        v_a_1826_,
    );
    lean_dec(v_a_1826_);
    lean_dec_ref(v_a_1825_);
    lean_dec(v_a_1824_);
    lean_dec_ref(v_a_1823_);
    lean_dec_ref(v_eqDecl_1819_);
    return v_res_1828_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(
    mut v_e_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1846_: u8 = 0;
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1852_: u8 = 0;
    let mut v_unused_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1832_ = l_Lean_Expr_hasMVar(v_e_1829_);
                if v___x_1832_ == 0 {
                    v___x_1833_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1833_, 0, v_e_1829_);
                    return v___x_1833_;
                } else {
                    v___x_1834_ = lean_st_ref_get(v___y_1830_);
                    v_mctx_1835_ = lean_ctor_get(v___x_1834_, 0);
                    lean_inc_ref(v_mctx_1835_);
                    lean_dec(v___x_1834_);
                    v___x_1836_ = l_Lean_instantiateMVarsCore(v_mctx_1835_, v_e_1829_);
                    v_fst_1837_ = lean_ctor_get(v___x_1836_, 0);
                    lean_inc(v_fst_1837_);
                    v_snd_1838_ = lean_ctor_get(v___x_1836_, 1);
                    lean_inc(v_snd_1838_);
                    lean_dec_ref(v___x_1836_);
                    v___x_1839_ = lean_st_ref_take(v___y_1830_);
                    v_cache_1840_ = lean_ctor_get(v___x_1839_, 1);
                    v_zetaDeltaFVarIds_1841_ = lean_ctor_get(v___x_1839_, 2);
                    v_postponed_1842_ = lean_ctor_get(v___x_1839_, 3);
                    v_diag_1843_ = lean_ctor_get(v___x_1839_, 4);
                    v_isSharedCheck_1852_ = (!lean_is_exclusive(v___x_1839_)) as u8;
                    if v_isSharedCheck_1852_ == 0 {
                        v_unused_1853_ = lean_ctor_get(v___x_1839_, 0);
                        lean_dec(v_unused_1853_);
                        v___x_1845_ = v___x_1839_;
                        v_isShared_1846_ = v_isSharedCheck_1852_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1843_);
                        lean_inc(v_postponed_1842_);
                        lean_inc(v_zetaDeltaFVarIds_1841_);
                        lean_inc(v_cache_1840_);
                        lean_dec(v___x_1839_);
                        v___x_1845_ = lean_box(0);
                        v_isShared_1846_ = v_isSharedCheck_1852_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1846_ == 0 {
                    lean_ctor_set(v___x_1845_, 0, v_snd_1838_);
                    v___x_1848_ = v___x_1845_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_snd_1838_);
                    lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_cache_1840_);
                    lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_zetaDeltaFVarIds_1841_);
                    lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_postponed_1842_);
                    lean_ctor_set(v_reuseFailAlloc_1851_, 4, v_diag_1843_);
                    v___x_1848_ = v_reuseFailAlloc_1851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1849_ = lean_st_ref_set(v___y_1830_, v___x_1848_);
                v___x_1850_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1850_, 0, v_fst_1837_);
                return v___x_1850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg___boxed(
    mut v_e_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(
        v_e_1854_,
        v___y_1855_,
    );
    lean_dec(v___y_1855_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0(
    mut v_e_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1864_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(
        v_e_1858_,
        v___y_1860_,
    );
    return v___x_1864_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___boxed(
    mut v_e_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1871_: *mut LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0(
        v_e_1865_,
        v___y_1866_,
        v___y_1867_,
        v___y_1868_,
        v___y_1869_,
    );
    lean_dec(v___y_1869_);
    lean_dec_ref(v___y_1868_);
    lean_dec(v___y_1867_);
    lean_dec_ref(v___y_1866_);
    return v_res_1871_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(
    mut v_mvarId_1872_: *mut LeanObject,
    mut v_x_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
    mut v___y_1875_: *mut LeanObject,
    mut v___y_1876_: *mut LeanObject,
    mut v___y_1877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1883_: u8 = 0;
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1887_: u8 = 0;
    let mut v_a_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1879_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1872_,
                    v_x_1873_,
                    v___y_1874_,
                    v___y_1875_,
                    v___y_1876_,
                    v___y_1877_,
                );
                if lean_obj_tag(v___x_1879_) == 0 {
                    v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
                    v_isSharedCheck_1887_ = (!lean_is_exclusive(v___x_1879_)) as u8;
                    if v_isSharedCheck_1887_ == 0 {
                        v___x_1882_ = v___x_1879_;
                        v_isShared_1883_ = v_isSharedCheck_1887_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1880_);
                        lean_dec(v___x_1879_);
                        v___x_1882_ = lean_box(0);
                        v_isShared_1883_ = v_isSharedCheck_1887_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1888_ = lean_ctor_get(v___x_1879_, 0);
                    v_isSharedCheck_1895_ = (!lean_is_exclusive(v___x_1879_)) as u8;
                    if v_isSharedCheck_1895_ == 0 {
                        v___x_1890_ = v___x_1879_;
                        v_isShared_1891_ = v_isSharedCheck_1895_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1888_);
                        lean_dec(v___x_1879_);
                        v___x_1890_ = lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1895_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1883_ == 0 {
                    v___x_1885_ = v___x_1882_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
                    v___x_1885_ = v_reuseFailAlloc_1886_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1885_;
            }
            3 => {
                if v_isShared_1891_ == 0 {
                    v___x_1893_ = v___x_1890_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
                    v___x_1893_ = v_reuseFailAlloc_1894_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg___boxed(
    mut v_mvarId_1896_: *mut LeanObject,
    mut v_x_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1903_: *mut LeanObject = core::ptr::null_mut();
    v_res_1903_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(
        v_mvarId_1896_,
        v_x_1897_,
        v___y_1898_,
        v___y_1899_,
        v___y_1900_,
        v___y_1901_,
    );
    lean_dec(v___y_1901_);
    lean_dec_ref(v___y_1900_);
    lean_dec(v___y_1899_);
    lean_dec_ref(v___y_1898_);
    return v_res_1903_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(
    mut v_00_u03b1_1904_: *mut LeanObject,
    mut v_mvarId_1905_: *mut LeanObject,
    mut v_x_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
    mut v___y_1910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(
        v_mvarId_1905_,
        v_x_1906_,
        v___y_1907_,
        v___y_1908_,
        v___y_1909_,
        v___y_1910_,
    );
    return v___x_1912_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___boxed(
    mut v_00_u03b1_1913_: *mut LeanObject,
    mut v_mvarId_1914_: *mut LeanObject,
    mut v_x_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
    mut v___y_1918_: *mut LeanObject,
    mut v___y_1919_: *mut LeanObject,
    mut v___y_1920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1921_: *mut LeanObject = core::ptr::null_mut();
    v_res_1921_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2(
        v_00_u03b1_1913_,
        v_mvarId_1914_,
        v_x_1915_,
        v___y_1916_,
        v___y_1917_,
        v___y_1918_,
        v___y_1919_,
    );
    lean_dec(v___y_1919_);
    lean_dec_ref(v___y_1918_);
    lean_dec(v___y_1917_);
    lean_dec_ref(v___y_1916_);
    return v_res_1921_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_1922_: *mut LeanObject,
    mut v_x_1923_: *mut LeanObject,
    mut v_x_1924_: *mut LeanObject,
    mut v_x_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1926_ = lean_ctor_get(v_x_1922_, 0);
                v_vs_1927_ = lean_ctor_get(v_x_1922_, 1);
                v_isSharedCheck_1951_ = (!lean_is_exclusive(v_x_1922_)) as u8;
                if v_isSharedCheck_1951_ == 0 {
                    v___x_1929_ = v_x_1922_;
                    v_isShared_1930_ = v_isSharedCheck_1951_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1927_);
                    lean_inc(v_ks_1926_);
                    lean_dec(v_x_1922_);
                    v___x_1929_ = lean_box(0);
                    v_isShared_1930_ = v_isSharedCheck_1951_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1931_ = lean_array_get_size(v_ks_1926_);
                v___x_1932_ = lean_nat_dec_lt(v_x_1923_, v___x_1931_);
                if v___x_1932_ == 0 {
                    lean_dec(v_x_1923_);
                    v___x_1933_ = lean_array_push(v_ks_1926_, v_x_1924_);
                    v___x_1934_ = lean_array_push(v_vs_1927_, v_x_1925_);
                    if v_isShared_1930_ == 0 {
                        lean_ctor_set(v___x_1929_, 1, v___x_1934_);
                        lean_ctor_set(v___x_1929_, 0, v___x_1933_);
                        v___x_1936_ = v___x_1929_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1933_);
                        lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1934_);
                        v___x_1936_ = v_reuseFailAlloc_1937_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1938_ = lean_array_fget_borrowed(v_ks_1926_, v_x_1923_);
                    v___x_1939_ = l_Lean_instBEqMVarId_beq(v_x_1924_, v_k_x27_1938_);
                    if v___x_1939_ == 0 {
                        if v_isShared_1930_ == 0 {
                            v___x_1941_ = v___x_1929_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_ks_1926_);
                            lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_vs_1927_);
                            v___x_1941_ = v_reuseFailAlloc_1945_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1946_ = lean_array_fset(v_ks_1926_, v_x_1923_, v_x_1924_);
                        v___x_1947_ = lean_array_fset(v_vs_1927_, v_x_1923_, v_x_1925_);
                        lean_dec(v_x_1923_);
                        if v_isShared_1930_ == 0 {
                            lean_ctor_set(v___x_1929_, 1, v___x_1947_);
                            lean_ctor_set(v___x_1929_, 0, v___x_1946_);
                            v___x_1949_ = v___x_1929_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1946_);
                            lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___x_1947_);
                            v___x_1949_ = v_reuseFailAlloc_1950_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1936_;
            }
            3 => {
                v___x_1942_ = lean_unsigned_to_nat(1);
                v___x_1943_ = lean_nat_add(v_x_1923_, v___x_1942_);
                lean_dec(v_x_1923_);
                v_x_1922_ = v___x_1941_;
                v_x_1923_ = v___x_1943_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(
    mut v_n_1952_: *mut LeanObject,
    mut v_k_1953_: *mut LeanObject,
    mut v_v_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    v___x_1955_ = lean_unsigned_to_nat(0);
    v___x_1956_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_1952_, v___x_1955_, v_k_1953_, v_v_1954_);
    return v___x_1956_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_1957_: usize = 0;
    let mut v___x_1958_: usize = 0;
    let mut v___x_1959_: usize = 0;
    v___x_1957_ = 5usize;
    v___x_1958_ = 1usize;
    v___x_1959_ = lean_usize_shift_left(v___x_1958_, v___x_1957_);
    return v___x_1959_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_1960_: usize = 0;
    let mut v___x_1961_: usize = 0;
    let mut v___x_1962_: usize = 0;
    v___x_1960_ = 1usize;
    v___x_1961_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_1962_ = lean_usize_sub(v___x_1961_, v___x_1960_);
    return v___x_1962_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    v___x_1963_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1963_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(
    mut v_x_1964_: *mut LeanObject,
    mut v_x_1965_: usize,
    mut v_x_1966_: usize,
    mut v_x_1967_: *mut LeanObject,
    mut v_x_1968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: usize = 0;
    let mut v___x_1973_: usize = 0;
    let mut v_j_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: u8 = 0;
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v_v_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1994_: u8 = 0;
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_node_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___x_2005_: usize = 0;
    let mut v___x_2006_: usize = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2013_: u8 = 0;
    let mut v_unused_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2024_: u8 = 0;
    let mut v_ks_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: usize = 0;
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: u8 = 0;
    let mut v_reuseFailAlloc_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1964_) == 0 {
                    v_es_1969_ = lean_ctor_get(v_x_1964_, 0);
                    v___x_1970_ = 5usize;
                    v___x_1971_ = 1usize;
                    v___x_1972_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__1);
                    v___x_1973_ = lean_usize_land(v_x_1965_, v___x_1972_);
                    v_j_1974_ = lean_usize_to_nat(v___x_1973_);
                    v___x_1975_ = lean_array_get_size(v_es_1969_);
                    v___x_1976_ = lean_nat_dec_lt(v_j_1974_, v___x_1975_);
                    if v___x_1976_ == 0 {
                        lean_dec(v_j_1974_);
                        lean_dec(v_x_1968_);
                        lean_dec(v_x_1967_);
                        return v_x_1964_;
                    } else {
                        lean_inc_ref(v_es_1969_);
                        v_isSharedCheck_2013_ = (!lean_is_exclusive(v_x_1964_)) as u8;
                        if v_isSharedCheck_2013_ == 0 {
                            v_unused_2014_ = lean_ctor_get(v_x_1964_, 0);
                            lean_dec(v_unused_2014_);
                            v___x_1978_ = v_x_1964_;
                            v_isShared_1979_ = v_isSharedCheck_2013_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1964_);
                            v___x_1978_ = lean_box(0);
                            v_isShared_1979_ = v_isSharedCheck_2013_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2015_ = lean_ctor_get(v_x_1964_, 0);
                    v_vs_2016_ = lean_ctor_get(v_x_1964_, 1);
                    v_isSharedCheck_2036_ = (!lean_is_exclusive(v_x_1964_)) as u8;
                    if v_isSharedCheck_2036_ == 0 {
                        v___x_2018_ = v_x_1964_;
                        v_isShared_2019_ = v_isSharedCheck_2036_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2016_);
                        lean_inc(v_ks_2015_);
                        lean_dec(v_x_1964_);
                        v___x_2018_ = lean_box(0);
                        v_isShared_2019_ = v_isSharedCheck_2036_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1980_ = lean_array_fget(v_es_1969_, v_j_1974_);
                v___x_1981_ = lean_box(0);
                v_xs_x27_1982_ = lean_array_fset(v_es_1969_, v_j_1974_, v___x_1981_);
                match lean_obj_tag(v_v_1980_) {
                    0 => {
                        v_key_1989_ = lean_ctor_get(v_v_1980_, 0);
                        v_val_1990_ = lean_ctor_get(v_v_1980_, 1);
                        v_isSharedCheck_2000_ = (!lean_is_exclusive(v_v_1980_)) as u8;
                        if v_isSharedCheck_2000_ == 0 {
                            v___x_1992_ = v_v_1980_;
                            v_isShared_1993_ = v_isSharedCheck_2000_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1990_);
                            lean_inc(v_key_1989_);
                            lean_dec(v_v_1980_);
                            v___x_1992_ = lean_box(0);
                            v_isShared_1993_ = v_isSharedCheck_2000_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2001_ = lean_ctor_get(v_v_1980_, 0);
                        v_isSharedCheck_2011_ = (!lean_is_exclusive(v_v_1980_)) as u8;
                        if v_isSharedCheck_2011_ == 0 {
                            v___x_2003_ = v_v_1980_;
                            v_isShared_2004_ = v_isSharedCheck_2011_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2001_);
                            lean_dec(v_v_1980_);
                            v___x_2003_ = lean_box(0);
                            v_isShared_2004_ = v_isSharedCheck_2011_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2012_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2012_, 0, v_x_1967_);
                        lean_ctor_set(v___x_2012_, 1, v_x_1968_);
                        v___y_1984_ = v___x_2012_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1985_ = lean_array_fset(v_xs_x27_1982_, v_j_1974_, v___y_1984_);
                lean_dec(v_j_1974_);
                if v_isShared_1979_ == 0 {
                    lean_ctor_set(v___x_1978_, 0, v___x_1985_);
                    v___x_1987_ = v___x_1978_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
                    v___x_1987_ = v_reuseFailAlloc_1988_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1987_;
            }
            4 => {
                v___x_1994_ = l_Lean_instBEqMVarId_beq(v_x_1967_, v_key_1989_);
                if v___x_1994_ == 0 {
                    lean_del_object(v___x_1992_);
                    v___x_1995_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1989_,
                        v_val_1990_,
                        v_x_1967_,
                        v_x_1968_,
                    );
                    v___x_1996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1996_, 0, v___x_1995_);
                    v___y_1984_ = v___x_1996_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1990_);
                    lean_dec(v_key_1989_);
                    if v_isShared_1993_ == 0 {
                        lean_ctor_set(v___x_1992_, 1, v_x_1968_);
                        lean_ctor_set(v___x_1992_, 0, v_x_1967_);
                        v___x_1998_ = v___x_1992_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_x_1967_);
                        lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_x_1968_);
                        v___x_1998_ = v_reuseFailAlloc_1999_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1984_ = v___x_1998_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2005_ = lean_usize_shift_right(v_x_1965_, v___x_1970_);
                v___x_2006_ = lean_usize_add(v_x_1966_, v___x_1971_);
                v___x_2007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_node_2001_, v___x_2005_, v___x_2006_, v_x_1967_, v_x_1968_);
                if v_isShared_2004_ == 0 {
                    lean_ctor_set(v___x_2003_, 0, v___x_2007_);
                    v___x_2009_ = v___x_2003_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1984_ = v___x_2009_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2019_ == 0 {
                    v___x_2021_ = v___x_2018_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_ks_2015_);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_vs_2016_);
                    v___x_2021_ = v_reuseFailAlloc_2035_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2022_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(v___x_2021_, v_x_1967_, v_x_1968_);
                v___x_2030_ = 7usize;
                v___x_2031_ = lean_usize_dec_le(v___x_2030_, v_x_1966_);
                if v___x_2031_ == 0 {
                    v___x_2032_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2022_);
                    v___x_2033_ = lean_unsigned_to_nat(4);
                    v___x_2034_ = lean_nat_dec_lt(v___x_2032_, v___x_2033_);
                    lean_dec(v___x_2032_);
                    v___y_2024_ = v___x_2034_;
                    state = 10;
                    continue;
                } else {
                    v___y_2024_ = v___x_2031_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2024_ == 0 {
                    v_ks_2025_ = lean_ctor_get(v_newNode_2022_, 0);
                    lean_inc_ref(v_ks_2025_);
                    v_vs_2026_ = lean_ctor_get(v_newNode_2022_, 1);
                    lean_inc_ref(v_vs_2026_);
                    lean_dec_ref(v_newNode_2022_);
                    v___x_2027_ = lean_unsigned_to_nat(0);
                    v___x_2028_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___closed__2);
                    v___x_2029_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_x_1966_, v_ks_2025_, v_vs_2026_, v___x_2027_, v___x_2028_);
                    lean_dec_ref(v_vs_2026_);
                    lean_dec_ref(v_ks_2025_);
                    return v___x_2029_;
                } else {
                    return v_newNode_2022_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(
    mut v_depth_2037_: usize,
    mut v_keys_2038_: *mut LeanObject,
    mut v_vals_2039_: *mut LeanObject,
    mut v_i_2040_: *mut LeanObject,
    mut v_entries_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v_k_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u64 = 0;
    let mut v_h_2047_: usize = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: usize = 0;
    let mut v___x_2051_: usize = 0;
    let mut v___x_2052_: usize = 0;
    let mut v_h_2053_: usize = 0;
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2042_ = lean_array_get_size(v_keys_2038_);
                v___x_2043_ = lean_nat_dec_lt(v_i_2040_, v___x_2042_);
                if v___x_2043_ == 0 {
                    lean_dec(v_i_2040_);
                    return v_entries_2041_;
                } else {
                    v_k_2044_ = lean_array_fget_borrowed(v_keys_2038_, v_i_2040_);
                    v_v_2045_ = lean_array_fget_borrowed(v_vals_2039_, v_i_2040_);
                    v___x_2046_ = l_Lean_instHashableMVarId_hash(v_k_2044_);
                    v_h_2047_ = lean_uint64_to_usize(v___x_2046_);
                    v___x_2048_ = 5usize;
                    v___x_2049_ = lean_unsigned_to_nat(1);
                    v___x_2050_ = 1usize;
                    v___x_2051_ = lean_usize_sub(v_depth_2037_, v___x_2050_);
                    v___x_2052_ = lean_usize_mul(v___x_2048_, v___x_2051_);
                    v_h_2053_ = lean_usize_shift_right(v_h_2047_, v___x_2052_);
                    v___x_2054_ = lean_nat_add(v_i_2040_, v___x_2049_);
                    lean_dec(v_i_2040_);
                    lean_inc(v_v_2045_);
                    lean_inc(v_k_2044_);
                    v___x_2055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_entries_2041_, v_h_2053_, v_depth_2037_, v_k_2044_, v_v_2045_);
                    v_i_2040_ = v___x_2054_;
                    v_entries_2041_ = v___x_2055_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_depth_2057_: *mut LeanObject,
    mut v_keys_2058_: *mut LeanObject,
    mut v_vals_2059_: *mut LeanObject,
    mut v_i_2060_: *mut LeanObject,
    mut v_entries_2061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2062_: usize = 0;
    let mut v_res_2063_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2062_ = lean_unbox_usize(v_depth_2057_);
    lean_dec(v_depth_2057_);
    v_res_2063_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_2062_, v_keys_2058_, v_vals_2059_, v_i_2060_, v_entries_2061_);
    lean_dec_ref(v_vals_2059_);
    lean_dec_ref(v_keys_2058_);
    return v_res_2063_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_2064_: *mut LeanObject,
    mut v_x_2065_: *mut LeanObject,
    mut v_x_2066_: *mut LeanObject,
    mut v_x_2067_: *mut LeanObject,
    mut v_x_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9334__boxed_2069_: usize = 0;
    let mut v_x_9335__boxed_2070_: usize = 0;
    let mut v_res_2071_: *mut LeanObject = core::ptr::null_mut();
    v_x_9334__boxed_2069_ = lean_unbox_usize(v_x_2065_);
    lean_dec(v_x_2065_);
    v_x_9335__boxed_2070_ = lean_unbox_usize(v_x_2066_);
    lean_dec(v_x_2066_);
    v_res_2071_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_2064_, v_x_9334__boxed_2069_, v_x_9335__boxed_2070_, v_x_2067_, v_x_2068_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(
    mut v_x_2072_: *mut LeanObject,
    mut v_x_2073_: *mut LeanObject,
    mut v_x_2074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2075_: u64 = 0;
    let mut v___x_2076_: usize = 0;
    let mut v___x_2077_: usize = 0;
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Lean_instHashableMVarId_hash(v_x_2073_);
    v___x_2076_ = lean_uint64_to_usize(v___x_2075_);
    v___x_2077_ = 1usize;
    v___x_2078_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_2072_, v___x_2076_, v___x_2077_, v_x_2073_, v_x_2074_);
    return v___x_2078_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(
    mut v_mvarId_2079_: *mut LeanObject,
    mut v_val_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2091_: u8 = 0;
    let mut v_depth_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2115_: u8 = 0;
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2083_ = lean_st_ref_take(v___y_2081_);
                v_mctx_2084_ = lean_ctor_get(v___x_2083_, 0);
                v_cache_2085_ = lean_ctor_get(v___x_2083_, 1);
                v_zetaDeltaFVarIds_2086_ = lean_ctor_get(v___x_2083_, 2);
                v_postponed_2087_ = lean_ctor_get(v___x_2083_, 3);
                v_diag_2088_ = lean_ctor_get(v___x_2083_, 4);
                v_isSharedCheck_2116_ = (!lean_is_exclusive(v___x_2083_)) as u8;
                if v_isSharedCheck_2116_ == 0 {
                    v___x_2090_ = v___x_2083_;
                    v_isShared_2091_ = v_isSharedCheck_2116_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_2088_);
                    lean_inc(v_postponed_2087_);
                    lean_inc(v_zetaDeltaFVarIds_2086_);
                    lean_inc(v_cache_2085_);
                    lean_inc(v_mctx_2084_);
                    lean_dec(v___x_2083_);
                    v___x_2090_ = lean_box(0);
                    v_isShared_2091_ = v_isSharedCheck_2116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2092_ = lean_ctor_get(v_mctx_2084_, 0);
                v_levelAssignDepth_2093_ = lean_ctor_get(v_mctx_2084_, 1);
                v_lmvarCounter_2094_ = lean_ctor_get(v_mctx_2084_, 2);
                v_mvarCounter_2095_ = lean_ctor_get(v_mctx_2084_, 3);
                v_lDecls_2096_ = lean_ctor_get(v_mctx_2084_, 4);
                v_decls_2097_ = lean_ctor_get(v_mctx_2084_, 5);
                v_userNames_2098_ = lean_ctor_get(v_mctx_2084_, 6);
                v_lAssignment_2099_ = lean_ctor_get(v_mctx_2084_, 7);
                v_eAssignment_2100_ = lean_ctor_get(v_mctx_2084_, 8);
                v_dAssignment_2101_ = lean_ctor_get(v_mctx_2084_, 9);
                v_isSharedCheck_2115_ = (!lean_is_exclusive(v_mctx_2084_)) as u8;
                if v_isSharedCheck_2115_ == 0 {
                    v___x_2103_ = v_mctx_2084_;
                    v_isShared_2104_ = v_isSharedCheck_2115_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_2101_);
                    lean_inc(v_eAssignment_2100_);
                    lean_inc(v_lAssignment_2099_);
                    lean_inc(v_userNames_2098_);
                    lean_inc(v_decls_2097_);
                    lean_inc(v_lDecls_2096_);
                    lean_inc(v_mvarCounter_2095_);
                    lean_inc(v_lmvarCounter_2094_);
                    lean_inc(v_levelAssignDepth_2093_);
                    lean_inc(v_depth_2092_);
                    lean_dec(v_mctx_2084_);
                    v___x_2103_ = lean_box(0);
                    v_isShared_2104_ = v_isSharedCheck_2115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2105_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(v_eAssignment_2100_, v_mvarId_2079_, v_val_2080_);
                if v_isShared_2104_ == 0 {
                    lean_ctor_set(v___x_2103_, 8, v___x_2105_);
                    v___x_2107_ = v___x_2103_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_depth_2092_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_levelAssignDepth_2093_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_lmvarCounter_2094_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_mvarCounter_2095_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_lDecls_2096_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 5, v_decls_2097_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 6, v_userNames_2098_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 7, v_lAssignment_2099_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 8, v___x_2105_);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 9, v_dAssignment_2101_);
                    v___x_2107_ = v_reuseFailAlloc_2114_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2091_ == 0 {
                    lean_ctor_set(v___x_2090_, 0, v___x_2107_);
                    v___x_2109_ = v___x_2090_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2107_);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_cache_2085_);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_zetaDeltaFVarIds_2086_);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_postponed_2087_);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_diag_2088_);
                    v___x_2109_ = v_reuseFailAlloc_2113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2110_ = lean_st_ref_set(v___y_2081_, v___x_2109_);
                v___x_2111_ = lean_box(0);
                v___x_2112_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2112_, 0, v___x_2111_);
                return v___x_2112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg___boxed(
    mut v_mvarId_2117_: *mut LeanObject,
    mut v_val_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2121_: *mut LeanObject = core::ptr::null_mut();
    v_res_2121_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(
        v_mvarId_2117_,
        v_val_2118_,
        v___y_2119_,
    );
    lean_dec(v___y_2119_);
    return v_res_2121_;
}
pub unsafe fn l_Lean_Meta_unifyEq_x3f___lam__0(
    mut v___x_2127_: u8,
    mut v_mvarId_2128_: *mut LeanObject,
    mut v_a_2129_: *mut LeanObject,
    mut v_a_2130_: *mut LeanObject,
    mut v_b_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v_a_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut v_unused_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_a_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_a_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_a_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v_a_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2237_: u8 = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_a_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v___x_2250_: u8 = 0;
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v_val_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2276_: u8 = 0;
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2286_: u8 = 0;
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2290_: u8 = 0;
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2302_: u8 = 0;
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2307_: u8 = 0;
    let mut v_a_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v_a_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2137_ = lean_st_ref_get(v___y_2135_);
                v_env_2138_ = lean_ctor_get(v___x_2137_, 0);
                lean_inc_ref(v_env_2138_);
                lean_dec(v___x_2137_);
                v___x_2139_ = l_Lean_Meta_unifyEq_x3f___lam__0___closed__2;
                v___x_2250_ = l_Lean_Environment_contains(v_env_2138_, v___x_2139_, v___x_2127_);
                if v___x_2250_ == 0 {
                    lean_dec_ref(v_b_2131_);
                    lean_dec_ref(v_a_2130_);
                    lean_dec_ref(v_a_2129_);
                    lean_dec(v_mvarId_2128_);
                    v___x_2251_ = lean_box(0);
                    v___x_2252_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2252_, 0, v___x_2251_);
                    return v___x_2252_;
                } else {
                    v___x_2253_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(
                        v_a_2130_,
                        v___y_2132_,
                        v___y_2133_,
                        v___y_2134_,
                        v___y_2135_,
                    );
                    if lean_obj_tag(v___x_2253_) == 0 {
                        v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
                        v_isSharedCheck_2320_ = (!lean_is_exclusive(v___x_2253_)) as u8;
                        if v_isSharedCheck_2320_ == 0 {
                            v___x_2256_ = v___x_2253_;
                            v_isShared_2257_ = v_isSharedCheck_2320_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_2254_);
                            lean_dec(v___x_2253_);
                            v___x_2256_ = lean_box(0);
                            v_isShared_2257_ = v_isSharedCheck_2320_;
                            state = 20;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_2131_);
                        lean_dec_ref(v_a_2129_);
                        lean_dec(v_mvarId_2128_);
                        v_a_2321_ = lean_ctor_get(v___x_2253_, 0);
                        v_isSharedCheck_2328_ = (!lean_is_exclusive(v___x_2253_)) as u8;
                        if v_isSharedCheck_2328_ == 0 {
                            v___x_2323_ = v___x_2253_;
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 32;
                            continue;
                        } else {
                            lean_inc(v_a_2321_);
                            lean_dec(v___x_2253_);
                            v___x_2323_ = lean_box(0);
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 32;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_mvarId_2128_);
                v___x_2148_ = l_Lean_MVarId_getType(
                    v_mvarId_2128_,
                    v___y_2144_,
                    v___y_2145_,
                    v___y_2146_,
                    v___y_2147_,
                );
                if lean_obj_tag(v___x_2148_) == 0 {
                    v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
                    lean_inc_n(v_a_2149_, 2);
                    lean_dec_ref_known(v___x_2148_, 1);
                    v___x_2150_ = l_Lean_Meta_getLevel(
                        v_a_2149_,
                        v___y_2144_,
                        v___y_2145_,
                        v___y_2146_,
                        v___y_2147_,
                    );
                    if lean_obj_tag(v___x_2150_) == 0 {
                        v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
                        lean_inc(v_a_2151_);
                        lean_dec_ref_known(v___x_2150_, 1);
                        lean_inc_ref(v_fst_2142_);
                        lean_inc_ref(v_fst_2141_);
                        v___x_2152_ = l_Lean_Meta_mkEq(
                            v_fst_2141_,
                            v_fst_2142_,
                            v___y_2144_,
                            v___y_2145_,
                            v___y_2146_,
                            v___y_2147_,
                        );
                        if lean_obj_tag(v___x_2152_) == 0 {
                            v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
                            lean_inc(v_a_2153_);
                            lean_dec_ref_known(v___x_2152_, 1);
                            lean_inc(v_a_2149_);
                            v___x_2154_ =
                                l_Lean_mkArrow(v_a_2153_, v_a_2149_, v___y_2146_, v___y_2147_);
                            if lean_obj_tag(v___x_2154_) == 0 {
                                v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
                                lean_inc(v_a_2155_);
                                lean_dec_ref_known(v___x_2154_, 1);
                                lean_inc(v_mvarId_2128_);
                                v___x_2156_ = l_Lean_MVarId_getTag(
                                    v_mvarId_2128_,
                                    v___y_2144_,
                                    v___y_2145_,
                                    v___y_2146_,
                                    v___y_2147_,
                                );
                                if lean_obj_tag(v___x_2156_) == 0 {
                                    v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
                                    lean_inc(v_a_2157_);
                                    lean_dec_ref_known(v___x_2156_, 1);
                                    v___x_2158_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                        v_a_2155_,
                                        v_a_2157_,
                                        v___y_2144_,
                                        v___y_2145_,
                                        v___y_2146_,
                                        v___y_2147_,
                                    );
                                    if lean_obj_tag(v___x_2158_) == 0 {
                                        v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
                                        lean_inc_n(v_a_2159_, 2);
                                        lean_dec_ref_known(v___x_2158_, 1);
                                        v___x_2160_ = lean_box(0);
                                        v___x_2161_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_2161_, 0, v_a_2151_);
                                        lean_ctor_set(v___x_2161_, 1, v___x_2160_);
                                        v___x_2162_ = l_Lean_mkConst(v___x_2139_, v___x_2161_);
                                        v___x_2163_ = l_Lean_mkNatLit(v_snd_2143_);
                                        lean_inc_ref(v_a_2129_);
                                        v___x_2164_ = l_Lean_LocalDecl_toExpr(v_a_2129_);
                                        v___x_2165_ = lean_unsigned_to_nat(6);
                                        v___x_2166_ =
                                            lean_mk_empty_array_with_capacity(v___x_2165_);
                                        v___x_2167_ = lean_array_push(v___x_2166_, v_a_2149_);
                                        v___x_2168_ = lean_array_push(v___x_2167_, v_fst_2141_);
                                        v___x_2169_ = lean_array_push(v___x_2168_, v_fst_2142_);
                                        v___x_2170_ = lean_array_push(v___x_2169_, v___x_2163_);
                                        v___x_2171_ = lean_array_push(v___x_2170_, v___x_2164_);
                                        v___x_2172_ = lean_array_push(v___x_2171_, v_a_2159_);
                                        v___x_2173_ = l_Lean_mkAppN(v___x_2162_, v___x_2172_);
                                        lean_dec_ref(v___x_2172_);
                                        v___x_2174_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(v_mvarId_2128_, v___x_2173_, v___y_2145_);
                                        v_isSharedCheck_2200_ =
                                            (!lean_is_exclusive(v___x_2174_)) as u8;
                                        if v_isSharedCheck_2200_ == 0 {
                                            v_unused_2201_ = lean_ctor_get(v___x_2174_, 0);
                                            lean_dec(v_unused_2201_);
                                            v___x_2176_ = v___x_2174_;
                                            v_isShared_2177_ = v_isSharedCheck_2200_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_dec(v___x_2174_);
                                            v___x_2176_ = lean_box(0);
                                            v_isShared_2177_ = v_isSharedCheck_2200_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_2151_);
                                        lean_dec(v_a_2149_);
                                        lean_dec(v_snd_2143_);
                                        lean_dec_ref(v_fst_2142_);
                                        lean_dec_ref(v_fst_2141_);
                                        lean_dec_ref(v_a_2129_);
                                        lean_dec(v_mvarId_2128_);
                                        v_a_2202_ = lean_ctor_get(v___x_2158_, 0);
                                        v_isSharedCheck_2209_ =
                                            (!lean_is_exclusive(v___x_2158_)) as u8;
                                        if v_isSharedCheck_2209_ == 0 {
                                            v___x_2204_ = v___x_2158_;
                                            v_isShared_2205_ = v_isSharedCheck_2209_;
                                            state = 8;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2202_);
                                            lean_dec(v___x_2158_);
                                            v___x_2204_ = lean_box(0);
                                            v_isShared_2205_ = v_isSharedCheck_2209_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2155_);
                                    lean_dec(v_a_2151_);
                                    lean_dec(v_a_2149_);
                                    lean_dec(v_snd_2143_);
                                    lean_dec_ref(v_fst_2142_);
                                    lean_dec_ref(v_fst_2141_);
                                    lean_dec_ref(v_a_2129_);
                                    lean_dec(v_mvarId_2128_);
                                    v_a_2210_ = lean_ctor_get(v___x_2156_, 0);
                                    v_isSharedCheck_2217_ = (!lean_is_exclusive(v___x_2156_)) as u8;
                                    if v_isSharedCheck_2217_ == 0 {
                                        v___x_2212_ = v___x_2156_;
                                        v_isShared_2213_ = v_isSharedCheck_2217_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2210_);
                                        lean_dec(v___x_2156_);
                                        v___x_2212_ = lean_box(0);
                                        v_isShared_2213_ = v_isSharedCheck_2217_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_2151_);
                                lean_dec(v_a_2149_);
                                lean_dec(v_snd_2143_);
                                lean_dec_ref(v_fst_2142_);
                                lean_dec_ref(v_fst_2141_);
                                lean_dec_ref(v_a_2129_);
                                lean_dec(v_mvarId_2128_);
                                v_a_2218_ = lean_ctor_get(v___x_2154_, 0);
                                v_isSharedCheck_2225_ = (!lean_is_exclusive(v___x_2154_)) as u8;
                                if v_isSharedCheck_2225_ == 0 {
                                    v___x_2220_ = v___x_2154_;
                                    v_isShared_2221_ = v_isSharedCheck_2225_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_2218_);
                                    lean_dec(v___x_2154_);
                                    v___x_2220_ = lean_box(0);
                                    v_isShared_2221_ = v_isSharedCheck_2225_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2151_);
                            lean_dec(v_a_2149_);
                            lean_dec(v_snd_2143_);
                            lean_dec_ref(v_fst_2142_);
                            lean_dec_ref(v_fst_2141_);
                            lean_dec_ref(v_a_2129_);
                            lean_dec(v_mvarId_2128_);
                            v_a_2226_ = lean_ctor_get(v___x_2152_, 0);
                            v_isSharedCheck_2233_ = (!lean_is_exclusive(v___x_2152_)) as u8;
                            if v_isSharedCheck_2233_ == 0 {
                                v___x_2228_ = v___x_2152_;
                                v_isShared_2229_ = v_isSharedCheck_2233_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_2226_);
                                lean_dec(v___x_2152_);
                                v___x_2228_ = lean_box(0);
                                v_isShared_2229_ = v_isSharedCheck_2233_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2149_);
                        lean_dec(v_snd_2143_);
                        lean_dec_ref(v_fst_2142_);
                        lean_dec_ref(v_fst_2141_);
                        lean_dec_ref(v_a_2129_);
                        lean_dec(v_mvarId_2128_);
                        v_a_2234_ = lean_ctor_get(v___x_2150_, 0);
                        v_isSharedCheck_2241_ = (!lean_is_exclusive(v___x_2150_)) as u8;
                        if v_isSharedCheck_2241_ == 0 {
                            v___x_2236_ = v___x_2150_;
                            v_isShared_2237_ = v_isSharedCheck_2241_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_2234_);
                            lean_dec(v___x_2150_);
                            v___x_2236_ = lean_box(0);
                            v_isShared_2237_ = v_isSharedCheck_2241_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_2143_);
                    lean_dec_ref(v_fst_2142_);
                    lean_dec_ref(v_fst_2141_);
                    lean_dec_ref(v_a_2129_);
                    lean_dec(v_mvarId_2128_);
                    v_a_2242_ = lean_ctor_get(v___x_2148_, 0);
                    v_isSharedCheck_2249_ = (!lean_is_exclusive(v___x_2148_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v___x_2244_ = v___x_2148_;
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_2242_);
                        lean_dec(v___x_2148_);
                        v___x_2244_ = lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 18;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2178_ = l_Lean_Expr_mvarId_x21(v_a_2159_);
                lean_dec(v_a_2159_);
                v___x_2179_ = l_Lean_LocalDecl_fvarId(v_a_2129_);
                lean_dec_ref(v_a_2129_);
                v___x_2180_ = l_Lean_MVarId_tryClear(
                    v___x_2178_,
                    v___x_2179_,
                    v___y_2144_,
                    v___y_2145_,
                    v___y_2146_,
                    v___y_2147_,
                );
                if lean_obj_tag(v___x_2180_) == 0 {
                    v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
                    v_isSharedCheck_2191_ = (!lean_is_exclusive(v___x_2180_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2183_ = v___x_2180_;
                        v_isShared_2184_ = v_isSharedCheck_2191_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2181_);
                        lean_dec(v___x_2180_);
                        v___x_2183_ = lean_box(0);
                        v_isShared_2184_ = v_isSharedCheck_2191_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2176_);
                    v_a_2192_ = lean_ctor_get(v___x_2180_, 0);
                    v_isSharedCheck_2199_ = (!lean_is_exclusive(v___x_2180_)) as u8;
                    if v_isSharedCheck_2199_ == 0 {
                        v___x_2194_ = v___x_2180_;
                        v_isShared_2195_ = v_isSharedCheck_2199_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2192_);
                        lean_dec(v___x_2180_);
                        v___x_2194_ = lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2199_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2177_ == 0 {
                    lean_ctor_set_tag(v___x_2176_, 1);
                    lean_ctor_set(v___x_2176_, 0, v_a_2181_);
                    v___x_2186_ = v___x_2176_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2181_);
                    v___x_2186_ = v_reuseFailAlloc_2190_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2184_ == 0 {
                    lean_ctor_set(v___x_2183_, 0, v___x_2186_);
                    v___x_2188_ = v___x_2183_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
                    v___x_2188_ = v_reuseFailAlloc_2189_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2188_;
            }
            6 => {
                if v_isShared_2195_ == 0 {
                    v___x_2197_ = v___x_2194_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
                    v___x_2197_ = v_reuseFailAlloc_2198_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2197_;
            }
            8 => {
                if v_isShared_2205_ == 0 {
                    v___x_2207_ = v___x_2204_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
                    v___x_2207_ = v_reuseFailAlloc_2208_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2207_;
            }
            10 => {
                if v_isShared_2213_ == 0 {
                    v___x_2215_ = v___x_2212_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
                    v___x_2215_ = v_reuseFailAlloc_2216_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2215_;
            }
            12 => {
                if v_isShared_2221_ == 0 {
                    v___x_2223_ = v___x_2220_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
                    v___x_2223_ = v_reuseFailAlloc_2224_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2223_;
            }
            14 => {
                if v_isShared_2229_ == 0 {
                    v___x_2231_ = v___x_2228_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2231_;
            }
            16 => {
                if v_isShared_2237_ == 0 {
                    v___x_2239_ = v___x_2236_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
                    v___x_2239_ = v_reuseFailAlloc_2240_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2239_;
            }
            18 => {
                if v_isShared_2245_ == 0 {
                    v___x_2247_ = v___x_2244_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
                    v___x_2247_ = v_reuseFailAlloc_2248_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2247_;
            }
            20 => {
                if lean_obj_tag(v_a_2254_) == 1 {
                    v_val_2258_ = lean_ctor_get(v_a_2254_, 0);
                    lean_inc(v_val_2258_);
                    lean_dec_ref_known(v_a_2254_, 1);
                    v_fst_2259_ = lean_ctor_get(v_val_2258_, 0);
                    lean_inc(v_fst_2259_);
                    v_snd_2260_ = lean_ctor_get(v_val_2258_, 1);
                    lean_inc(v_snd_2260_);
                    lean_dec(v_val_2258_);
                    v___x_2261_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(
                        v_b_2131_,
                        v___y_2132_,
                        v___y_2133_,
                        v___y_2134_,
                        v___y_2135_,
                    );
                    if lean_obj_tag(v___x_2261_) == 0 {
                        v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
                        v_isSharedCheck_2307_ = (!lean_is_exclusive(v___x_2261_)) as u8;
                        if v_isSharedCheck_2307_ == 0 {
                            v___x_2264_ = v___x_2261_;
                            v_isShared_2265_ = v_isSharedCheck_2307_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_2262_);
                            lean_dec(v___x_2261_);
                            v___x_2264_ = lean_box(0);
                            v_isShared_2265_ = v_isSharedCheck_2307_;
                            state = 21;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_2260_);
                        lean_dec(v_fst_2259_);
                        lean_del_object(v___x_2256_);
                        lean_dec_ref(v_a_2129_);
                        lean_dec(v_mvarId_2128_);
                        v_a_2308_ = lean_ctor_get(v___x_2261_, 0);
                        v_isSharedCheck_2315_ = (!lean_is_exclusive(v___x_2261_)) as u8;
                        if v_isSharedCheck_2315_ == 0 {
                            v___x_2310_ = v___x_2261_;
                            v_isShared_2311_ = v_isSharedCheck_2315_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_2308_);
                            lean_dec(v___x_2261_);
                            v___x_2310_ = lean_box(0);
                            v_isShared_2311_ = v_isSharedCheck_2315_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2254_);
                    lean_dec_ref(v_b_2131_);
                    lean_dec_ref(v_a_2129_);
                    lean_dec(v_mvarId_2128_);
                    v___x_2316_ = lean_box(0);
                    if v_isShared_2257_ == 0 {
                        lean_ctor_set(v___x_2256_, 0, v___x_2316_);
                        v___x_2318_ = v___x_2256_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
                        v___x_2318_ = v_reuseFailAlloc_2319_;
                        state = 31;
                        continue;
                    }
                }
            }
            21 => {
                if lean_obj_tag(v_a_2262_) == 1 {
                    lean_del_object(v___x_2256_);
                    v_val_2271_ = lean_ctor_get(v_a_2262_, 0);
                    lean_inc(v_val_2271_);
                    lean_dec_ref_known(v_a_2262_, 1);
                    v_fst_2272_ = lean_ctor_get(v_val_2271_, 0);
                    lean_inc(v_fst_2272_);
                    v_snd_2273_ = lean_ctor_get(v_val_2271_, 1);
                    lean_inc(v_snd_2273_);
                    lean_dec(v_val_2271_);
                    v___x_2274_ = lean_unsigned_to_nat(0);
                    v___x_2275_ = lean_nat_dec_eq(v_snd_2260_, v___x_2274_);
                    if v___x_2275_ == 0 {
                        v___x_2276_ = lean_nat_dec_eq(v_snd_2273_, v___x_2274_);
                        if v___x_2276_ == 0 {
                            lean_del_object(v___x_2264_);
                            v___x_2277_ = lean_nat_dec_lt(v_snd_2260_, v_snd_2273_);
                            if v___x_2277_ == 0 {
                                v___x_2278_ = lean_nat_dec_eq(v_snd_2260_, v_snd_2273_);
                                if v___x_2278_ == 0 {
                                    v___x_2279_ = lean_nat_sub(v_snd_2260_, v_snd_2273_);
                                    lean_dec(v_snd_2260_);
                                    v___x_2280_ = l_Lean_mkNatLit(v___x_2279_);
                                    v___x_2281_ = l_Lean_Meta_mkAdd(
                                        v_fst_2259_,
                                        v___x_2280_,
                                        v___y_2132_,
                                        v___y_2133_,
                                        v___y_2134_,
                                        v___y_2135_,
                                    );
                                    if lean_obj_tag(v___x_2281_) == 0 {
                                        v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
                                        lean_inc(v_a_2282_);
                                        lean_dec_ref_known(v___x_2281_, 1);
                                        v_fst_2141_ = v_a_2282_;
                                        v_fst_2142_ = v_fst_2272_;
                                        v_snd_2143_ = v_snd_2273_;
                                        v___y_2144_ = v___y_2132_;
                                        v___y_2145_ = v___y_2133_;
                                        v___y_2146_ = v___y_2134_;
                                        v___y_2147_ = v___y_2135_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v_snd_2273_);
                                        lean_dec(v_fst_2272_);
                                        lean_dec_ref(v_a_2129_);
                                        lean_dec(v_mvarId_2128_);
                                        v_a_2283_ = lean_ctor_get(v___x_2281_, 0);
                                        v_isSharedCheck_2290_ =
                                            (!lean_is_exclusive(v___x_2281_)) as u8;
                                        if v_isSharedCheck_2290_ == 0 {
                                            v___x_2285_ = v___x_2281_;
                                            v_isShared_2286_ = v_isSharedCheck_2290_;
                                            state = 24;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2283_);
                                            lean_dec(v___x_2281_);
                                            v___x_2285_ = lean_box(0);
                                            v_isShared_2286_ = v_isSharedCheck_2290_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_snd_2273_);
                                    v_fst_2141_ = v_fst_2259_;
                                    v_fst_2142_ = v_fst_2272_;
                                    v_snd_2143_ = v_snd_2260_;
                                    v___y_2144_ = v___y_2132_;
                                    v___y_2145_ = v___y_2133_;
                                    v___y_2146_ = v___y_2134_;
                                    v___y_2147_ = v___y_2135_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_2291_ = lean_nat_sub(v_snd_2273_, v_snd_2260_);
                                lean_dec(v_snd_2273_);
                                v___x_2292_ = l_Lean_mkNatLit(v___x_2291_);
                                v___x_2293_ = l_Lean_Meta_mkAdd(
                                    v_fst_2272_,
                                    v___x_2292_,
                                    v___y_2132_,
                                    v___y_2133_,
                                    v___y_2134_,
                                    v___y_2135_,
                                );
                                if lean_obj_tag(v___x_2293_) == 0 {
                                    v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
                                    lean_inc(v_a_2294_);
                                    lean_dec_ref_known(v___x_2293_, 1);
                                    v_fst_2141_ = v_fst_2259_;
                                    v_fst_2142_ = v_a_2294_;
                                    v_snd_2143_ = v_snd_2260_;
                                    v___y_2144_ = v___y_2132_;
                                    v___y_2145_ = v___y_2133_;
                                    v___y_2146_ = v___y_2134_;
                                    v___y_2147_ = v___y_2135_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_snd_2260_);
                                    lean_dec(v_fst_2259_);
                                    lean_dec_ref(v_a_2129_);
                                    lean_dec(v_mvarId_2128_);
                                    v_a_2295_ = lean_ctor_get(v___x_2293_, 0);
                                    v_isSharedCheck_2302_ = (!lean_is_exclusive(v___x_2293_)) as u8;
                                    if v_isSharedCheck_2302_ == 0 {
                                        v___x_2297_ = v___x_2293_;
                                        v_isShared_2298_ = v_isSharedCheck_2302_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2295_);
                                        lean_dec(v___x_2293_);
                                        v___x_2297_ = lean_box(0);
                                        v_isShared_2298_ = v_isSharedCheck_2302_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_snd_2273_);
                            lean_dec(v_fst_2272_);
                            lean_dec(v_snd_2260_);
                            lean_dec(v_fst_2259_);
                            lean_dec_ref(v_a_2129_);
                            lean_dec(v_mvarId_2128_);
                            state = 22;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_2273_);
                        lean_dec(v_fst_2272_);
                        lean_dec(v_snd_2260_);
                        lean_dec(v_fst_2259_);
                        lean_dec_ref(v_a_2129_);
                        lean_dec(v_mvarId_2128_);
                        state = 22;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2264_);
                    lean_dec(v_a_2262_);
                    lean_dec(v_snd_2260_);
                    lean_dec(v_fst_2259_);
                    lean_dec_ref(v_a_2129_);
                    lean_dec(v_mvarId_2128_);
                    v___x_2303_ = lean_box(0);
                    if v_isShared_2257_ == 0 {
                        lean_ctor_set(v___x_2256_, 0, v___x_2303_);
                        v___x_2305_ = v___x_2256_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
                        v___x_2305_ = v_reuseFailAlloc_2306_;
                        state = 28;
                        continue;
                    }
                }
            }
            22 => {
                v___x_2267_ = lean_box(0);
                if v_isShared_2265_ == 0 {
                    lean_ctor_set(v___x_2264_, 0, v___x_2267_);
                    v___x_2269_ = v___x_2264_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
                    v___x_2269_ = v_reuseFailAlloc_2270_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2269_;
            }
            24 => {
                if v_isShared_2286_ == 0 {
                    v___x_2288_ = v___x_2285_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
                    v___x_2288_ = v_reuseFailAlloc_2289_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2288_;
            }
            26 => {
                if v_isShared_2298_ == 0 {
                    v___x_2300_ = v___x_2297_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
                    v___x_2300_ = v_reuseFailAlloc_2301_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2300_;
            }
            28 => {
                return v___x_2305_;
            }
            29 => {
                if v_isShared_2311_ == 0 {
                    v___x_2313_ = v___x_2310_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
                    v___x_2313_ = v_reuseFailAlloc_2314_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2313_;
            }
            31 => {
                return v___x_2318_;
            }
            32 => {
                if v_isShared_2324_ == 0 {
                    v___x_2326_ = v___x_2323_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
                    v___x_2326_ = v_reuseFailAlloc_2327_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_unifyEq_x3f___lam__0___boxed(
    mut v___x_2329_: *mut LeanObject,
    mut v_mvarId_2330_: *mut LeanObject,
    mut v_a_2331_: *mut LeanObject,
    mut v_a_2332_: *mut LeanObject,
    mut v_b_2333_: *mut LeanObject,
    mut v___y_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9563__boxed_2339_: u8 = 0;
    let mut v_res_2340_: *mut LeanObject = core::ptr::null_mut();
    v___x_9563__boxed_2339_ = (lean_unbox(v___x_2329_) as u8);
    v_res_2340_ = l_Lean_Meta_unifyEq_x3f___lam__0(
        v___x_9563__boxed_2339_,
        v_mvarId_2330_,
        v_a_2331_,
        v_a_2332_,
        v_b_2333_,
        v___y_2334_,
        v___y_2335_,
        v___y_2336_,
        v___y_2337_,
    );
    lean_dec(v___y_2337_);
    lean_dec_ref(v___y_2336_);
    lean_dec(v___y_2335_);
    lean_dec_ref(v___y_2334_);
    return v_res_2340_;
}
pub unsafe fn _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Lean_Meta_unifyEq_x3f___lam__1___closed__2;
    v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_Meta_unifyEq_x3f___lam__1(
    mut v_eqFVarId_2347_: *mut LeanObject,
    mut v_mvarId_2348_: *mut LeanObject,
    mut v_subst_2349_: *mut LeanObject,
    mut v_acyclic_2350_: *mut LeanObject,
    mut v_caseName_x3f_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
    mut v___y_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
    mut v___y_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: u8 = 0;
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2392_: u8 = 0;
    let mut v_a_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2400_: u8 = 0;
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2417_: u8 = 0;
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_a_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2430_: u8 = 0;
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut v_a_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2438_: u8 = 0;
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut v_isSharedCheck_2443_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2448_: u8 = 0;
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2455_: u8 = 0;
    let mut v_a_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2459_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2463_: u8 = 0;
    let mut v_a_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_eqFVarId_2347_);
                v___x_2357_ = l_Lean_FVarId_getDecl___redArg(
                    v_eqFVarId_2347_,
                    v___y_2352_,
                    v___y_2354_,
                    v___y_2355_,
                );
                if lean_obj_tag(v___x_2357_) == 0 {
                    v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
                    lean_inc(v_a_2358_);
                    lean_dec_ref_known(v___x_2357_, 1);
                    v___x_2359_ = l_Lean_LocalDecl_type(v_a_2358_);
                    v___x_2360_ = l_Lean_Expr_isHEq(v___x_2359_);
                    if v___x_2360_ == 0 {
                        v___x_2361_ = l_Lean_Meta_unifyEq_x3f___lam__1___closed__1;
                        v___x_2362_ = lean_unsigned_to_nat(3);
                        v___x_2363_ =
                            l_Lean_Expr_isAppOfArity(v___x_2359_, v___x_2361_, v___x_2362_);
                        if v___x_2363_ == 0 {
                            lean_dec(v_a_2358_);
                            lean_dec(v_caseName_x3f_2351_);
                            lean_dec_ref(v_acyclic_2350_);
                            lean_dec(v_subst_2349_);
                            lean_dec(v_mvarId_2348_);
                            lean_dec(v_eqFVarId_2347_);
                            v___x_2364_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unifyEq_x3f___lam__1___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unifyEq_x3f___lam__1___closed__3_once
                                ),
                                _init_l_Lean_Meta_unifyEq_x3f___lam__1___closed__3,
                            );
                            v___x_2365_ = l_Lean_indentExpr(v___x_2359_);
                            v___x_2366_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2366_, 0, v___x_2364_);
                            lean_ctor_set(v___x_2366_, 1, v___x_2365_);
                            v___x_2367_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq_spec__1___redArg(v___x_2366_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
                            return v___x_2367_;
                        } else {
                            v___x_2368_ = l_Lean_Expr_appFn_x21(v___x_2359_);
                            v___x_2369_ = l_Lean_Expr_appArg_x21(v___x_2368_);
                            lean_dec_ref(v___x_2368_);
                            lean_inc_ref(v___x_2369_);
                            v___x_2370_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v___x_2369_, v___y_2353_);
                            v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
                            lean_inc(v_a_2371_);
                            lean_dec_ref(v___x_2370_);
                            v___x_2372_ = l_Lean_Expr_appArg_x21(v___x_2359_);
                            lean_dec_ref(v___x_2359_);
                            lean_inc_ref(v___x_2372_);
                            v___x_2373_ = l_Lean_instantiateMVars___at___00Lean_Meta_unifyEq_x3f_spec__0___redArg(v___x_2372_, v___y_2353_);
                            if lean_obj_tag(v_a_2371_) == 1 {
                                lean_dec(v_caseName_x3f_2351_);
                                v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
                                lean_inc(v_a_2374_);
                                lean_dec_ref(v___x_2373_);
                                if lean_obj_tag(v_a_2374_) == 1 {
                                    v_fvarId_2375_ = lean_ctor_get(v_a_2371_, 0);
                                    lean_inc(v_fvarId_2375_);
                                    lean_dec_ref_known(v_a_2371_, 1);
                                    v_fvarId_2376_ = lean_ctor_get(v_a_2374_, 0);
                                    lean_inc(v_fvarId_2376_);
                                    lean_dec_ref_known(v_a_2374_, 1);
                                    v___x_2377_ = l_Lean_FVarId_getDecl___redArg(
                                        v_fvarId_2375_,
                                        v___y_2352_,
                                        v___y_2354_,
                                        v___y_2355_,
                                    );
                                    if lean_obj_tag(v___x_2377_) == 0 {
                                        v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
                                        lean_inc(v_a_2378_);
                                        lean_dec_ref_known(v___x_2377_, 1);
                                        v___x_2379_ = l_Lean_FVarId_getDecl___redArg(
                                            v_fvarId_2376_,
                                            v___y_2352_,
                                            v___y_2354_,
                                            v___y_2355_,
                                        );
                                        if lean_obj_tag(v___x_2379_) == 0 {
                                            v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
                                            lean_inc(v_a_2380_);
                                            lean_dec_ref_known(v___x_2379_, 1);
                                            v___x_2381_ = l_Lean_LocalDecl_index(v_a_2378_);
                                            lean_dec(v_a_2378_);
                                            v___x_2382_ = l_Lean_LocalDecl_index(v_a_2380_);
                                            lean_dec(v_a_2380_);
                                            v___x_2383_ = lean_nat_dec_lt(v___x_2381_, v___x_2382_);
                                            lean_dec(v___x_2382_);
                                            lean_dec(v___x_2381_);
                                            v___x_2384_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_2348_, v_eqFVarId_2347_, v_subst_2349_, v_acyclic_2350_, v_a_2358_, v___x_2369_, v___x_2372_, v___x_2383_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
                                            lean_dec(v_a_2358_);
                                            return v___x_2384_;
                                        } else {
                                            lean_dec(v_a_2378_);
                                            lean_dec_ref(v___x_2372_);
                                            lean_dec_ref(v___x_2369_);
                                            lean_dec(v_a_2358_);
                                            lean_dec_ref(v_acyclic_2350_);
                                            lean_dec(v_subst_2349_);
                                            lean_dec(v_mvarId_2348_);
                                            lean_dec(v_eqFVarId_2347_);
                                            v_a_2385_ = lean_ctor_get(v___x_2379_, 0);
                                            v_isSharedCheck_2392_ =
                                                (!lean_is_exclusive(v___x_2379_)) as u8;
                                            if v_isSharedCheck_2392_ == 0 {
                                                v___x_2387_ = v___x_2379_;
                                                v_isShared_2388_ = v_isSharedCheck_2392_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2385_);
                                                lean_dec(v___x_2379_);
                                                v___x_2387_ = lean_box(0);
                                                v_isShared_2388_ = v_isSharedCheck_2392_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_fvarId_2376_);
                                        lean_dec_ref(v___x_2372_);
                                        lean_dec_ref(v___x_2369_);
                                        lean_dec(v_a_2358_);
                                        lean_dec_ref(v_acyclic_2350_);
                                        lean_dec(v_subst_2349_);
                                        lean_dec(v_mvarId_2348_);
                                        lean_dec(v_eqFVarId_2347_);
                                        v_a_2393_ = lean_ctor_get(v___x_2377_, 0);
                                        v_isSharedCheck_2400_ =
                                            (!lean_is_exclusive(v___x_2377_)) as u8;
                                        if v_isSharedCheck_2400_ == 0 {
                                            v___x_2395_ = v___x_2377_;
                                            v_isShared_2396_ = v_isSharedCheck_2400_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2393_);
                                            lean_dec(v___x_2377_);
                                            v___x_2395_ = lean_box(0);
                                            v_isShared_2396_ = v_isSharedCheck_2400_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2374_);
                                    lean_dec_ref_known(v_a_2371_, 1);
                                    v___x_2401_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(v_mvarId_2348_, v_eqFVarId_2347_, v_subst_2349_, v_acyclic_2350_, v_a_2358_, v___x_2369_, v___x_2372_, v___x_2360_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
                                    lean_dec(v_a_2358_);
                                    return v___x_2401_;
                                }
                            } else {
                                v_a_2402_ = lean_ctor_get(v___x_2373_, 0);
                                v_isSharedCheck_2443_ = (!lean_is_exclusive(v___x_2373_)) as u8;
                                if v_isSharedCheck_2443_ == 0 {
                                    v___x_2404_ = v___x_2373_;
                                    v_isShared_2405_ = v_isSharedCheck_2443_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_2402_);
                                    lean_dec(v___x_2373_);
                                    v___x_2404_ = lean_box(0);
                                    v_isShared_2405_ = v_isSharedCheck_2443_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2359_);
                        lean_dec(v_caseName_x3f_2351_);
                        lean_dec_ref(v_acyclic_2350_);
                        lean_dec(v_eqFVarId_2347_);
                        v___x_2444_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(
                            v_mvarId_2348_,
                            v_a_2358_,
                            v___y_2352_,
                            v___y_2353_,
                            v___y_2354_,
                            v___y_2355_,
                        );
                        lean_dec(v_a_2358_);
                        if lean_obj_tag(v___x_2444_) == 0 {
                            v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
                            v_isSharedCheck_2455_ = (!lean_is_exclusive(v___x_2444_)) as u8;
                            if v_isSharedCheck_2455_ == 0 {
                                v___x_2447_ = v___x_2444_;
                                v_isShared_2448_ = v_isSharedCheck_2455_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_2445_);
                                lean_dec(v___x_2444_);
                                v___x_2447_ = lean_box(0);
                                v_isShared_2448_ = v_isSharedCheck_2455_;
                                state = 13;
                                continue;
                            }
                        } else {
                            lean_dec(v_subst_2349_);
                            v_a_2456_ = lean_ctor_get(v___x_2444_, 0);
                            v_isSharedCheck_2463_ = (!lean_is_exclusive(v___x_2444_)) as u8;
                            if v_isSharedCheck_2463_ == 0 {
                                v___x_2458_ = v___x_2444_;
                                v_isShared_2459_ = v_isSharedCheck_2463_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_2456_);
                                lean_dec(v___x_2444_);
                                v___x_2458_ = lean_box(0);
                                v_isShared_2459_ = v_isSharedCheck_2463_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_caseName_x3f_2351_);
                    lean_dec_ref(v_acyclic_2350_);
                    lean_dec(v_subst_2349_);
                    lean_dec(v_mvarId_2348_);
                    lean_dec(v_eqFVarId_2347_);
                    v_a_2464_ = lean_ctor_get(v___x_2357_, 0);
                    v_isSharedCheck_2471_ = (!lean_is_exclusive(v___x_2357_)) as u8;
                    if v_isSharedCheck_2471_ == 0 {
                        v___x_2466_ = v___x_2357_;
                        v_isShared_2467_ = v_isSharedCheck_2471_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_2464_);
                        lean_dec(v___x_2357_);
                        v___x_2466_ = lean_box(0);
                        v_isShared_2467_ = v_isSharedCheck_2471_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2388_ == 0 {
                    v___x_2390_ = v___x_2387_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
                    v___x_2390_ = v_reuseFailAlloc_2391_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2390_;
            }
            3 => {
                if v_isShared_2396_ == 0 {
                    v___x_2398_ = v___x_2395_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
                    v___x_2398_ = v_reuseFailAlloc_2399_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2398_;
            }
            5 => {
                if lean_obj_tag(v_a_2402_) == 1 {
                    lean_dec_ref_known(v_a_2402_, 1);
                    lean_del_object(v___x_2404_);
                    lean_dec(v_a_2371_);
                    lean_dec(v_caseName_x3f_2351_);
                    v___x_2406_ =
                        l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_substEq(
                            v_mvarId_2348_,
                            v_eqFVarId_2347_,
                            v_subst_2349_,
                            v_acyclic_2350_,
                            v_a_2358_,
                            v___x_2369_,
                            v___x_2372_,
                            v___x_2363_,
                            v___y_2352_,
                            v___y_2353_,
                            v___y_2354_,
                            v___y_2355_,
                        );
                    lean_dec(v_a_2358_);
                    return v___x_2406_;
                } else {
                    lean_dec_ref(v___x_2372_);
                    lean_dec_ref(v___x_2369_);
                    lean_dec_ref(v_acyclic_2350_);
                    lean_inc(v_a_2402_);
                    lean_inc(v_a_2371_);
                    v___x_2407_ = l_Lean_Meta_isExprDefEq(
                        v_a_2371_,
                        v_a_2402_,
                        v___y_2352_,
                        v___y_2353_,
                        v___y_2354_,
                        v___y_2355_,
                    );
                    if lean_obj_tag(v___x_2407_) == 0 {
                        v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
                        lean_inc(v_a_2408_);
                        lean_dec_ref_known(v___x_2407_, 1);
                        v___x_2409_ = (lean_unbox(v_a_2408_) as u8);
                        lean_dec(v_a_2408_);
                        if v___x_2409_ == 0 {
                            lean_del_object(v___x_2404_);
                            v___x_2410_ = lean_box((v___x_2363_) as usize);
                            lean_inc(v_a_2358_);
                            lean_inc(v_mvarId_2348_);
                            v___f_2411_ = lean_alloc_closure(
                                l_Lean_Meta_unifyEq_x3f___lam__0___boxed as *mut core::ffi::c_void,
                                10,
                                3,
                            );
                            lean_closure_set(v___f_2411_, 0, v___x_2410_);
                            lean_closure_set(v___f_2411_, 1, v_mvarId_2348_);
                            lean_closure_set(v___f_2411_, 2, v_a_2358_);
                            v___x_2412_ = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_unifyEq_x3f_injection(v_mvarId_2348_, v_eqFVarId_2347_, v_subst_2349_, v_caseName_x3f_2351_, v_a_2358_, v___f_2411_, v_a_2371_, v_a_2402_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
                            lean_dec(v_a_2358_);
                            return v___x_2412_;
                        } else {
                            lean_dec(v_a_2402_);
                            lean_dec(v_a_2371_);
                            lean_dec(v_a_2358_);
                            lean_dec(v_caseName_x3f_2351_);
                            v___x_2413_ = l_Lean_MVarId_clear(
                                v_mvarId_2348_,
                                v_eqFVarId_2347_,
                                v___y_2352_,
                                v___y_2353_,
                                v___y_2354_,
                                v___y_2355_,
                            );
                            if lean_obj_tag(v___x_2413_) == 0 {
                                v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
                                v_isSharedCheck_2426_ = (!lean_is_exclusive(v___x_2413_)) as u8;
                                if v_isSharedCheck_2426_ == 0 {
                                    v___x_2416_ = v___x_2413_;
                                    v_isShared_2417_ = v_isSharedCheck_2426_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_2414_);
                                    lean_dec(v___x_2413_);
                                    v___x_2416_ = lean_box(0);
                                    v_isShared_2417_ = v_isSharedCheck_2426_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_2404_);
                                lean_dec(v_subst_2349_);
                                v_a_2427_ = lean_ctor_get(v___x_2413_, 0);
                                v_isSharedCheck_2434_ = (!lean_is_exclusive(v___x_2413_)) as u8;
                                if v_isSharedCheck_2434_ == 0 {
                                    v___x_2429_ = v___x_2413_;
                                    v_isShared_2430_ = v_isSharedCheck_2434_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2427_);
                                    lean_dec(v___x_2413_);
                                    v___x_2429_ = lean_box(0);
                                    v_isShared_2430_ = v_isSharedCheck_2434_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_2404_);
                        lean_dec(v_a_2402_);
                        lean_dec(v_a_2371_);
                        lean_dec(v_a_2358_);
                        lean_dec(v_caseName_x3f_2351_);
                        lean_dec(v_subst_2349_);
                        lean_dec(v_mvarId_2348_);
                        lean_dec(v_eqFVarId_2347_);
                        v_a_2435_ = lean_ctor_get(v___x_2407_, 0);
                        v_isSharedCheck_2442_ = (!lean_is_exclusive(v___x_2407_)) as u8;
                        if v_isSharedCheck_2442_ == 0 {
                            v___x_2437_ = v___x_2407_;
                            v_isShared_2438_ = v_isSharedCheck_2442_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_2435_);
                            lean_dec(v___x_2407_);
                            v___x_2437_ = lean_box(0);
                            v_isShared_2438_ = v_isSharedCheck_2442_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_2418_ = lean_unsigned_to_nat(0);
                v___x_2419_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2419_, 0, v_a_2414_);
                lean_ctor_set(v___x_2419_, 1, v_subst_2349_);
                lean_ctor_set(v___x_2419_, 2, v___x_2418_);
                if v_isShared_2405_ == 0 {
                    lean_ctor_set_tag(v___x_2404_, 1);
                    lean_ctor_set(v___x_2404_, 0, v___x_2419_);
                    v___x_2421_ = v___x_2404_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2419_);
                    v___x_2421_ = v_reuseFailAlloc_2425_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2417_ == 0 {
                    lean_ctor_set(v___x_2416_, 0, v___x_2421_);
                    v___x_2423_ = v___x_2416_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
                    v___x_2423_ = v_reuseFailAlloc_2424_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2423_;
            }
            9 => {
                if v_isShared_2430_ == 0 {
                    v___x_2432_ = v___x_2429_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
                    v___x_2432_ = v_reuseFailAlloc_2433_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2432_;
            }
            11 => {
                if v_isShared_2438_ == 0 {
                    v___x_2440_ = v___x_2437_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
                    v___x_2440_ = v_reuseFailAlloc_2441_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2440_;
            }
            13 => {
                v___x_2449_ = lean_unsigned_to_nat(1);
                v___x_2450_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2450_, 0, v_a_2445_);
                lean_ctor_set(v___x_2450_, 1, v_subst_2349_);
                lean_ctor_set(v___x_2450_, 2, v___x_2449_);
                v___x_2451_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2451_, 0, v___x_2450_);
                if v_isShared_2448_ == 0 {
                    lean_ctor_set(v___x_2447_, 0, v___x_2451_);
                    v___x_2453_ = v___x_2447_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
                    v___x_2453_ = v_reuseFailAlloc_2454_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2453_;
            }
            15 => {
                if v_isShared_2459_ == 0 {
                    v___x_2461_ = v___x_2458_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
                    v___x_2461_ = v_reuseFailAlloc_2462_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2461_;
            }
            17 => {
                if v_isShared_2467_ == 0 {
                    v___x_2469_ = v___x_2466_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
                    v___x_2469_ = v_reuseFailAlloc_2470_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_unifyEq_x3f___lam__1___boxed(
    mut v_eqFVarId_2472_: *mut LeanObject,
    mut v_mvarId_2473_: *mut LeanObject,
    mut v_subst_2474_: *mut LeanObject,
    mut v_acyclic_2475_: *mut LeanObject,
    mut v_caseName_x3f_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
    mut v___y_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2482_: *mut LeanObject = core::ptr::null_mut();
    v_res_2482_ = l_Lean_Meta_unifyEq_x3f___lam__1(
        v_eqFVarId_2472_,
        v_mvarId_2473_,
        v_subst_2474_,
        v_acyclic_2475_,
        v_caseName_x3f_2476_,
        v___y_2477_,
        v___y_2478_,
        v___y_2479_,
        v___y_2480_,
    );
    lean_dec(v___y_2480_);
    lean_dec_ref(v___y_2479_);
    lean_dec(v___y_2478_);
    lean_dec_ref(v___y_2477_);
    return v_res_2482_;
}
pub unsafe fn l_Lean_Meta_unifyEq_x3f(
    mut v_mvarId_2483_: *mut LeanObject,
    mut v_eqFVarId_2484_: *mut LeanObject,
    mut v_subst_2485_: *mut LeanObject,
    mut v_acyclic_2486_: *mut LeanObject,
    mut v_caseName_x3f_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
    mut v_a_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_2483_);
    v___f_2493_ = lean_alloc_closure(
        l_Lean_Meta_unifyEq_x3f___lam__1___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___f_2493_, 0, v_eqFVarId_2484_);
    lean_closure_set(v___f_2493_, 1, v_mvarId_2483_);
    lean_closure_set(v___f_2493_, 2, v_subst_2485_);
    lean_closure_set(v___f_2493_, 3, v_acyclic_2486_);
    lean_closure_set(v___f_2493_, 4, v_caseName_x3f_2487_);
    v___x_2494_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unifyEq_x3f_spec__2___redArg(
        v_mvarId_2483_,
        v___f_2493_,
        v_a_2488_,
        v_a_2489_,
        v_a_2490_,
        v_a_2491_,
    );
    return v___x_2494_;
}
pub unsafe fn l_Lean_Meta_unifyEq_x3f___boxed(
    mut v_mvarId_2495_: *mut LeanObject,
    mut v_eqFVarId_2496_: *mut LeanObject,
    mut v_subst_2497_: *mut LeanObject,
    mut v_acyclic_2498_: *mut LeanObject,
    mut v_caseName_x3f_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
    mut v_a_2501_: *mut LeanObject,
    mut v_a_2502_: *mut LeanObject,
    mut v_a_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2505_: *mut LeanObject = core::ptr::null_mut();
    v_res_2505_ = l_Lean_Meta_unifyEq_x3f(
        v_mvarId_2495_,
        v_eqFVarId_2496_,
        v_subst_2497_,
        v_acyclic_2498_,
        v_caseName_x3f_2499_,
        v_a_2500_,
        v_a_2501_,
        v_a_2502_,
        v_a_2503_,
    );
    lean_dec(v_a_2503_);
    lean_dec_ref(v_a_2502_);
    lean_dec(v_a_2501_);
    lean_dec_ref(v_a_2500_);
    return v_res_2505_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1(
    mut v_mvarId_2506_: *mut LeanObject,
    mut v_val_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
    mut v___y_2509_: *mut LeanObject,
    mut v___y_2510_: *mut LeanObject,
    mut v___y_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___redArg(
        v_mvarId_2506_,
        v_val_2507_,
        v___y_2509_,
    );
    return v___x_2513_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1___boxed(
    mut v_mvarId_2514_: *mut LeanObject,
    mut v_val_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
    mut v___y_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2521_: *mut LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1(
        v_mvarId_2514_,
        v_val_2515_,
        v___y_2516_,
        v___y_2517_,
        v___y_2518_,
        v___y_2519_,
    );
    lean_dec(v___y_2519_);
    lean_dec_ref(v___y_2518_);
    lean_dec(v___y_2517_);
    lean_dec_ref(v___y_2516_);
    return v_res_2521_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1(
    mut v_00_u03b2_2522_: *mut LeanObject,
    mut v_x_2523_: *mut LeanObject,
    mut v_x_2524_: *mut LeanObject,
    mut v_x_2525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    v___x_2526_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1___redArg(v_x_2523_, v_x_2524_, v_x_2525_);
    return v___x_2526_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3(
    mut v_00_u03b2_2527_: *mut LeanObject,
    mut v_x_2528_: *mut LeanObject,
    mut v_x_2529_: usize,
    mut v_x_2530_: usize,
    mut v_x_2531_: *mut LeanObject,
    mut v_x_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    v___x_2533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___redArg(v_x_2528_, v_x_2529_, v_x_2530_, v_x_2531_, v_x_2532_);
    return v___x_2533_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_2534_: *mut LeanObject,
    mut v_x_2535_: *mut LeanObject,
    mut v_x_2536_: *mut LeanObject,
    mut v_x_2537_: *mut LeanObject,
    mut v_x_2538_: *mut LeanObject,
    mut v_x_2539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_10272__boxed_2540_: usize = 0;
    let mut v_x_10273__boxed_2541_: usize = 0;
    let mut v_res_2542_: *mut LeanObject = core::ptr::null_mut();
    v_x_10272__boxed_2540_ = lean_unbox_usize(v_x_2536_);
    lean_dec(v_x_2536_);
    v_x_10273__boxed_2541_ = lean_unbox_usize(v_x_2537_);
    lean_dec(v_x_2537_);
    v_res_2542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3(v_00_u03b2_2534_, v_x_2535_, v_x_10272__boxed_2540_, v_x_10273__boxed_2541_, v_x_2538_, v_x_2539_);
    return v_res_2542_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4(
    mut v_00_u03b2_2543_: *mut LeanObject,
    mut v_n_2544_: *mut LeanObject,
    mut v_k_2545_: *mut LeanObject,
    mut v_v_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4___redArg(v_n_2544_, v_k_2545_, v_v_2546_);
    return v___x_2547_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5(
    mut v_00_u03b2_2548_: *mut LeanObject,
    mut v_depth_2549_: usize,
    mut v_keys_2550_: *mut LeanObject,
    mut v_vals_2551_: *mut LeanObject,
    mut v_heq_2552_: *mut LeanObject,
    mut v_i_2553_: *mut LeanObject,
    mut v_entries_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    v___x_2555_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_2549_, v_keys_2550_, v_vals_2551_, v_i_2553_, v_entries_2554_);
    return v___x_2555_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b2_2556_: *mut LeanObject,
    mut v_depth_2557_: *mut LeanObject,
    mut v_keys_2558_: *mut LeanObject,
    mut v_vals_2559_: *mut LeanObject,
    mut v_heq_2560_: *mut LeanObject,
    mut v_i_2561_: *mut LeanObject,
    mut v_entries_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2563_: usize = 0;
    let mut v_res_2564_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2563_ = lean_unbox_usize(v_depth_2557_);
    lean_dec(v_depth_2557_);
    v_res_2564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_2556_, v_depth_boxed_2563_, v_keys_2558_, v_vals_2559_, v_heq_2560_, v_i_2561_, v_entries_2562_);
    lean_dec_ref(v_vals_2559_);
    lean_dec_ref(v_keys_2558_);
    return v_res_2564_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_2565_: *mut LeanObject,
    mut v_x_2566_: *mut LeanObject,
    mut v_x_2567_: *mut LeanObject,
    mut v_x_2568_: *mut LeanObject,
    mut v_x_2569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    v___x_2570_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_unifyEq_x3f_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2566_, v_x_2567_, v_x_2568_, v_x_2569_);
    return v___x_2570_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_UnifyEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_UnifyEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_UnifyEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Injection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_UnifyEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_UnifyEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_UnifyEq(builtin);
}
