// Lean compiler output
// Module: Lean.Meta.Tactic.Unfold
// Imports: Lean.Meta.Tactic.Delta Lean.Meta.Tactic.Simp.Main Lean.Meta.WHNF
use crate::r#gen::Init::MetaTypes::l_Lean_Meta_Simp_neutralConfig;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_fvar___override, l_Lean_Expr_hasMVar, l_Lean_mkConst};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getType___redArg,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
};
use crate::r#gen::Lean::Meta::Eqns::l_Lean_Meta_getUnfoldEqnFor_x3f;
use crate::r#gen::Lean::Meta::Tactic::Delta::{
    initialize_Lean_Meta_Tactic_Delta, l_Lean_Meta_deltaExpand,
    runtime_initialize_Lean_Meta_Tactic_Delta,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    l_Lean_MVarId_replaceLocalDeclDefEq, l_Lean_MVarId_replaceTargetDefEq,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_Simp_main,
    l_Lean_Meta_applySimpResultToLocalDecl, runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Rewrite::l_Lean_Meta_Simp_tryTheorem_x3f;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_isBackwardRflTheorem, l_Lean_Meta_isRflTheorem,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    l_Lean_Meta_Simp_mkContext___redArg, l_Lean_Meta_applySimpResultToTarget,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::Meta::Transform::l_Lean_Meta_zetaDeltaFVars;
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_reduceMatcher_x3f, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0_value:
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
static mut l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1: u64 = 0;
pub static l_Lean_Meta_unfold___lam__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Meta_unfold___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfold___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_unfold___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_unfold___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_unfold___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfold___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_unfold___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_unfold___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_unfold___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfold___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_unfold___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_unfold___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_unfold___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfold___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_unfold___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_unfold___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_unfold___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfold___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_unfold___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfold___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_unfold___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfold___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_unfold___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfold___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_unfold___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfold___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_unfold___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfold___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_unfold___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfold___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_unfold___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfold___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_unfoldTarget___lam__0___closed__0_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            84, 97, 99, 116, 105, 99, 32, 96, 117, 110, 102, 111, 108, 100, 96, 32, 102, 97, 105,
            108, 101, 100, 32, 116, 111, 32, 117, 110, 102, 111, 108, 100, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_unfoldTarget___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfoldTarget___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_unfoldTarget___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfoldTarget___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_unfoldTarget___lam__0___closed__2_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [96, 32, 105, 110, 0],
    };
static mut l_Lean_Meta_unfoldTarget___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfoldTarget___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_unfoldTarget___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfoldTarget___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 85, 110, 102,
            111, 108, 100, 0,
        ],
    };
static mut l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1_value: LeanStringObject<26> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 117, 110, 102, 111, 108, 100, 76, 111, 99,
            97, 108, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2_value: LeanStringObject<34> =
    LeanStringObject {
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(
    mut v_a_962_: *mut LeanObject,
    mut v_a_963_: *mut LeanObject,
    mut v_a_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxDischargeDepth_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextual_971_: u8 = 0;
    let mut v_memoize_972_: u8 = 0;
    let mut v_singlePass_973_: u8 = 0;
    let mut v_zeta_974_: u8 = 0;
    let mut v_beta_975_: u8 = 0;
    let mut v_eta_976_: u8 = 0;
    let mut v_etaStruct_977_: u8 = 0;
    let mut v_iota_978_: u8 = 0;
    let mut v_proj_979_: u8 = 0;
    let mut v_decide_980_: u8 = 0;
    let mut v_arith_981_: u8 = 0;
    let mut v_autoUnfold_982_: u8 = 0;
    let mut v_dsimp_983_: u8 = 0;
    let mut v_failIfUnchanged_984_: u8 = 0;
    let mut v_ground_985_: u8 = 0;
    let mut v_unfoldPartialApp_986_: u8 = 0;
    let mut v_zetaDelta_987_: u8 = 0;
    let mut v_index_988_: u8 = 0;
    let mut v_implicitDefEqProofs_989_: u8 = 0;
    let mut v_zetaUnused_990_: u8 = 0;
    let mut v_catchRuntime_991_: u8 = 0;
    let mut v_zetaHave_992_: u8 = 0;
    let mut v_congrConsts_993_: u8 = 0;
    let mut v_bitVecOfNat_994_: u8 = 0;
    let mut v_warnExponents_995_: u8 = 0;
    let mut v_suggestions_996_: u8 = 0;
    let mut v_maxSuggestions_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_locals_998_: u8 = 0;
    let mut v_instances_999_: u8 = 0;
    let mut v___x_1000_: u8 = 0;
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1008_: u8 = 0;
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_966_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_964_);
                if lean_obj_tag(v___x_966_) == 0 {
                    v_a_967_ = lean_ctor_get(v___x_966_, 0);
                    lean_inc(v_a_967_);
                    lean_dec_ref_known(v___x_966_, 1);
                    v___x_968_ = l_Lean_Meta_Simp_neutralConfig;
                    v_maxSteps_969_ = lean_ctor_get(v___x_968_, 0);
                    v_maxDischargeDepth_970_ = lean_ctor_get(v___x_968_, 1);
                    v_contextual_971_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_memoize_972_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_singlePass_973_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_zeta_974_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_beta_975_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_eta_976_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 5) as u32,
                    );
                    v_etaStruct_977_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 6) as u32,
                    );
                    v_iota_978_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 7) as u32,
                    );
                    v_proj_979_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    v_decide_980_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 9) as u32,
                    );
                    v_arith_981_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 10) as u32,
                    );
                    v_autoUnfold_982_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 11) as u32,
                    );
                    v_dsimp_983_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 12) as u32,
                    );
                    v_failIfUnchanged_984_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 13) as u32,
                    );
                    v_ground_985_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 14) as u32,
                    );
                    v_unfoldPartialApp_986_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 15) as u32,
                    );
                    v_zetaDelta_987_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    );
                    v_index_988_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 17) as u32,
                    );
                    v_implicitDefEqProofs_989_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 18) as u32,
                    );
                    v_zetaUnused_990_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 19) as u32,
                    );
                    v_catchRuntime_991_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 20) as u32,
                    );
                    v_zetaHave_992_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 21) as u32,
                    );
                    v_congrConsts_993_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 23) as u32,
                    );
                    v_bitVecOfNat_994_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 24) as u32,
                    );
                    v_warnExponents_995_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 25) as u32,
                    );
                    v_suggestions_996_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 26) as u32,
                    );
                    v_maxSuggestions_997_ = lean_ctor_get(v___x_968_, 2);
                    v_locals_998_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 27) as u32,
                    );
                    v_instances_999_ = lean_ctor_get_uint8(
                        v___x_968_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 28) as u32,
                    );
                    v___x_1000_ = 1;
                    lean_inc(v_maxSuggestions_997_);
                    lean_inc(v_maxDischargeDepth_970_);
                    lean_inc(v_maxSteps_969_);
                    v___x_1001_ = lean_alloc_ctor(0, 3, (29) as u32);
                    lean_ctor_set(v___x_1001_, 0, v_maxSteps_969_);
                    lean_ctor_set(v___x_1001_, 1, v_maxDischargeDepth_970_);
                    lean_ctor_set(v___x_1001_, 2, v_maxSuggestions_997_);
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_contextual_971_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_memoize_972_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_singlePass_973_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_zeta_974_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_beta_975_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 5) as u32,
                        v_eta_976_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 6) as u32,
                        v_etaStruct_977_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 7) as u32,
                        v_iota_978_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v_proj_979_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 9) as u32,
                        v_decide_980_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 10) as u32,
                        v_arith_981_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 11) as u32,
                        v_autoUnfold_982_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 12) as u32,
                        v_dsimp_983_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 13) as u32,
                        v_failIfUnchanged_984_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 14) as u32,
                        v_ground_985_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 15) as u32,
                        v_unfoldPartialApp_986_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v_zetaDelta_987_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 17) as u32,
                        v_index_988_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 18) as u32,
                        v_implicitDefEqProofs_989_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 19) as u32,
                        v_zetaUnused_990_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 20) as u32,
                        v_catchRuntime_991_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 21) as u32,
                        v_zetaHave_992_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 22) as u32,
                        v___x_1000_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 23) as u32,
                        v_congrConsts_993_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 24) as u32,
                        v_bitVecOfNat_994_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 25) as u32,
                        v_warnExponents_995_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 26) as u32,
                        v_suggestions_996_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 27) as u32,
                        v_locals_998_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 28) as u32,
                        v_instances_999_,
                    );
                    v___x_1002_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0;
                    v___x_1003_ = l_Lean_Options_empty;
                    v___x_1004_ = l_Lean_Meta_Simp_mkContext___redArg(
                        v___x_1001_,
                        v___x_1002_,
                        v_a_967_,
                        v___x_1003_,
                        v_a_962_,
                        v_a_963_,
                        v_a_964_,
                    );
                    return v___x_1004_;
                } else {
                    v_a_1005_ = lean_ctor_get(v___x_966_, 0);
                    v_isSharedCheck_1012_ = (!lean_is_exclusive(v___x_966_)) as u8;
                    if v_isSharedCheck_1012_ == 0 {
                        v___x_1007_ = v___x_966_;
                        v_isShared_1008_ = v_isSharedCheck_1012_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1005_);
                        lean_dec(v___x_966_);
                        v___x_1007_ = lean_box(0);
                        v_isShared_1008_ = v_isSharedCheck_1012_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1008_ == 0 {
                    v___x_1010_ = v___x_1007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
                    v___x_1010_ = v_reuseFailAlloc_1011_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1010_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___boxed(
    mut v_a_1013_: *mut LeanObject,
    mut v_a_1014_: *mut LeanObject,
    mut v_a_1015_: *mut LeanObject,
    mut v_a_1016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1017_: *mut LeanObject = core::ptr::null_mut();
    v_res_1017_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(
        v_a_1013_, v_a_1014_, v_a_1015_,
    );
    lean_dec(v_a_1015_);
    lean_dec_ref(v_a_1014_);
    lean_dec_ref(v_a_1013_);
    return v_res_1017_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(
    mut v_a_1018_: *mut LeanObject,
    mut v_a_1019_: *mut LeanObject,
    mut v_a_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v___x_1023_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(
        v_a_1018_, v_a_1020_, v_a_1021_,
    );
    return v___x_1023_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___boxed(
    mut v_a_1024_: *mut LeanObject,
    mut v_a_1025_: *mut LeanObject,
    mut v_a_1026_: *mut LeanObject,
    mut v_a_1027_: *mut LeanObject,
    mut v_a_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1029_: *mut LeanObject = core::ptr::null_mut();
    v_res_1029_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(
        v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_,
    );
    lean_dec(v_a_1027_);
    lean_dec_ref(v_a_1026_);
    lean_dec(v_a_1025_);
    lean_dec_ref(v_a_1024_);
    return v_res_1029_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1() -> u64
{
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u64 = 0;
    v___x_1032_ = 2;
    v___x_1033_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1032_);
    return v___x_1033_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(
    mut v_unfoldThm_1034_: *mut LeanObject,
    mut v_e_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
    mut v_a_1041_: *mut LeanObject,
    mut v_a_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1051_: u8 = 0;
    let mut v_expr_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_x3f_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1054_: u8 = 0;
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1062_: u8 = 0;
    let mut v_val_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1076_: u8 = 0;
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut v_unused_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1086_: u8 = 0;
    let mut v_a_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1090_: u8 = 0;
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut v_isSharedCheck_1095_: u8 = 0;
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1103_: u8 = 0;
    let mut v_ctxApprox_1104_: u8 = 0;
    let mut v_quasiPatternApprox_1105_: u8 = 0;
    let mut v_constApprox_1106_: u8 = 0;
    let mut v_isDefEqStuckEx_1107_: u8 = 0;
    let mut v_unificationHints_1108_: u8 = 0;
    let mut v_proofIrrelevance_1109_: u8 = 0;
    let mut v_assignSyntheticOpaque_1110_: u8 = 0;
    let mut v_offsetCnstrs_1111_: u8 = 0;
    let mut v_etaStruct_1112_: u8 = 0;
    let mut v_univApprox_1113_: u8 = 0;
    let mut v_iota_1114_: u8 = 0;
    let mut v_beta_1115_: u8 = 0;
    let mut v_proj_1116_: u8 = 0;
    let mut v_zeta_1117_: u8 = 0;
    let mut v_zetaDelta_1118_: u8 = 0;
    let mut v_zetaUnused_1119_: u8 = 0;
    let mut v_zetaHave_1120_: u8 = 0;
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1123_: u8 = 0;
    let mut v_trackZetaDelta_1124_: u8 = 0;
    let mut v_zetaDeltaSet_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1131_: u8 = 0;
    let mut v_inTypeClassResolution_1132_: u8 = 0;
    let mut v_cacheInferType_1133_: u8 = 0;
    let mut v___x_1134_: u8 = 0;
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v_config_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: u64 = 0;
    let mut v___x_1141_: u64 = 0;
    let mut v___x_1142_: u64 = 0;
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: u8 = 0;
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: u64 = 0;
    let mut v___x_1149_: u64 = 0;
    let mut v_key_1150_: u64 = 0;
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1159_: u8 = 0;
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut v_reuseFailAlloc_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1165_: u8 = 0;
    let mut v_a_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1169_: u8 = 0;
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut v_a_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_unfoldThm_1034_);
                v___x_1096_ = l_Lean_Meta_isRflTheorem(v_unfoldThm_1034_, v_a_1041_, v_a_1042_);
                if lean_obj_tag(v___x_1096_) == 0 {
                    v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
                    lean_inc(v_a_1097_);
                    lean_dec_ref_known(v___x_1096_, 1);
                    lean_inc(v_unfoldThm_1034_);
                    v___x_1098_ =
                        l_Lean_Meta_isBackwardRflTheorem(v_unfoldThm_1034_, v_a_1041_, v_a_1042_);
                    if lean_obj_tag(v___x_1098_) == 0 {
                        v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
                        lean_inc(v_a_1099_);
                        lean_dec_ref_known(v___x_1098_, 1);
                        v___x_1100_ = lean_box(0);
                        lean_inc(v_unfoldThm_1034_);
                        v___x_1101_ = l_Lean_mkConst(v_unfoldThm_1034_, v___x_1100_);
                        v___x_1102_ = l_Lean_Meta_Context_config(v_a_1039_);
                        v_foApprox_1103_ = lean_ctor_get_uint8(v___x_1102_, 0 as u32);
                        v_ctxApprox_1104_ = lean_ctor_get_uint8(v___x_1102_, 1 as u32);
                        v_quasiPatternApprox_1105_ = lean_ctor_get_uint8(v___x_1102_, 2 as u32);
                        v_constApprox_1106_ = lean_ctor_get_uint8(v___x_1102_, 3 as u32);
                        v_isDefEqStuckEx_1107_ = lean_ctor_get_uint8(v___x_1102_, 4 as u32);
                        v_unificationHints_1108_ = lean_ctor_get_uint8(v___x_1102_, 5 as u32);
                        v_proofIrrelevance_1109_ = lean_ctor_get_uint8(v___x_1102_, 6 as u32);
                        v_assignSyntheticOpaque_1110_ = lean_ctor_get_uint8(v___x_1102_, 7 as u32);
                        v_offsetCnstrs_1111_ = lean_ctor_get_uint8(v___x_1102_, 8 as u32);
                        v_etaStruct_1112_ = lean_ctor_get_uint8(v___x_1102_, 10 as u32);
                        v_univApprox_1113_ = lean_ctor_get_uint8(v___x_1102_, 11 as u32);
                        v_iota_1114_ = lean_ctor_get_uint8(v___x_1102_, 12 as u32);
                        v_beta_1115_ = lean_ctor_get_uint8(v___x_1102_, 13 as u32);
                        v_proj_1116_ = lean_ctor_get_uint8(v___x_1102_, 14 as u32);
                        v_zeta_1117_ = lean_ctor_get_uint8(v___x_1102_, 15 as u32);
                        v_zetaDelta_1118_ = lean_ctor_get_uint8(v___x_1102_, 16 as u32);
                        v_zetaUnused_1119_ = lean_ctor_get_uint8(v___x_1102_, 17 as u32);
                        v_zetaHave_1120_ = lean_ctor_get_uint8(v___x_1102_, 18 as u32);
                        v_isSharedCheck_1165_ = (!lean_is_exclusive(v___x_1102_)) as u8;
                        if v_isSharedCheck_1165_ == 0 {
                            v___x_1122_ = v___x_1102_;
                            v_isShared_1123_ = v_isSharedCheck_1165_;
                            state = 13;
                            continue;
                        } else {
                            lean_dec(v___x_1102_);
                            v___x_1122_ = lean_box(0);
                            v_isShared_1123_ = v_isSharedCheck_1165_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1097_);
                        lean_dec_ref(v_e_1035_);
                        lean_dec(v_unfoldThm_1034_);
                        v_a_1166_ = lean_ctor_get(v___x_1098_, 0);
                        v_isSharedCheck_1173_ = (!lean_is_exclusive(v___x_1098_)) as u8;
                        if v_isSharedCheck_1173_ == 0 {
                            v___x_1168_ = v___x_1098_;
                            v_isShared_1169_ = v_isSharedCheck_1173_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_1166_);
                            lean_dec(v___x_1098_);
                            v___x_1168_ = lean_box(0);
                            v_isShared_1169_ = v_isSharedCheck_1173_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1035_);
                    lean_dec(v_unfoldThm_1034_);
                    v_a_1174_ = lean_ctor_get(v___x_1096_, 0);
                    v_isSharedCheck_1181_ = (!lean_is_exclusive(v___x_1096_)) as u8;
                    if v_isSharedCheck_1181_ == 0 {
                        v___x_1176_ = v___x_1096_;
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_1174_);
                        lean_dec(v___x_1096_);
                        v___x_1176_ = lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1045_) == 0 {
                    v___x_1046_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v___x_1046_, 0, v_a_1045_);
                    v___x_1047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1047_, 0, v___x_1046_);
                    return v___x_1047_;
                } else {
                    v_val_1048_ = lean_ctor_get(v_a_1045_, 0);
                    v_isSharedCheck_1095_ = (!lean_is_exclusive(v_a_1045_)) as u8;
                    if v_isSharedCheck_1095_ == 0 {
                        v___x_1050_ = v_a_1045_;
                        v_isShared_1051_ = v_isSharedCheck_1095_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1048_);
                        lean_dec(v_a_1045_);
                        v___x_1050_ = lean_box(0);
                        v_isShared_1051_ = v_isSharedCheck_1095_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_expr_1052_ = lean_ctor_get(v_val_1048_, 0);
                v_proof_x3f_1053_ = lean_ctor_get(v_val_1048_, 1);
                v_cache_1054_ = lean_ctor_get_uint8(
                    v_val_1048_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v___x_1055_ = l_Lean_Meta_reduceMatcher_x3f(
                    v_expr_1052_,
                    v_a_1039_,
                    v_a_1040_,
                    v_a_1041_,
                    v_a_1042_,
                );
                if lean_obj_tag(v___x_1055_) == 0 {
                    v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
                    v_isSharedCheck_1086_ = (!lean_is_exclusive(v___x_1055_)) as u8;
                    if v_isSharedCheck_1086_ == 0 {
                        v___x_1058_ = v___x_1055_;
                        v_isShared_1059_ = v_isSharedCheck_1086_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1056_);
                        lean_dec(v___x_1055_);
                        v___x_1058_ = lean_box(0);
                        v_isShared_1059_ = v_isSharedCheck_1086_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1050_);
                    lean_dec(v_val_1048_);
                    v_a_1087_ = lean_ctor_get(v___x_1055_, 0);
                    v_isSharedCheck_1094_ = (!lean_is_exclusive(v___x_1055_)) as u8;
                    if v_isSharedCheck_1094_ == 0 {
                        v___x_1089_ = v___x_1055_;
                        v_isShared_1090_ = v_isSharedCheck_1094_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1087_);
                        lean_dec(v___x_1055_);
                        v___x_1089_ = lean_box(0);
                        v_isShared_1090_ = v_isSharedCheck_1094_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_1056_) == 0 {
                    lean_inc(v_proof_x3f_1053_);
                    lean_del_object(v___x_1050_);
                    v_isSharedCheck_1077_ = (!lean_is_exclusive(v_val_1048_)) as u8;
                    if v_isSharedCheck_1077_ == 0 {
                        v_unused_1078_ = lean_ctor_get(v_val_1048_, 1);
                        lean_dec(v_unused_1078_);
                        v_unused_1079_ = lean_ctor_get(v_val_1048_, 0);
                        lean_dec(v_unused_1079_);
                        v___x_1061_ = v_val_1048_;
                        v_isShared_1062_ = v_isSharedCheck_1077_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_val_1048_);
                        v___x_1061_ = lean_box(0);
                        v_isShared_1062_ = v_isSharedCheck_1077_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1056_);
                    if v_isShared_1051_ == 0 {
                        lean_ctor_set_tag(v___x_1050_, 0);
                        v___x_1081_ = v___x_1050_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_val_1048_);
                        v___x_1081_ = v_reuseFailAlloc_1085_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_val_1063_ = lean_ctor_get(v_a_1056_, 0);
                v_isSharedCheck_1076_ = (!lean_is_exclusive(v_a_1056_)) as u8;
                if v_isSharedCheck_1076_ == 0 {
                    v___x_1065_ = v_a_1056_;
                    v_isShared_1066_ = v_isSharedCheck_1076_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_val_1063_);
                    lean_dec(v_a_1056_);
                    v___x_1065_ = lean_box(0);
                    v_isShared_1066_ = v_isSharedCheck_1076_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1062_ == 0 {
                    lean_ctor_set(v___x_1061_, 0, v_val_1063_);
                    v___x_1068_ = v___x_1061_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_val_1063_);
                    lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_proof_x3f_1053_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1075_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_cache_1054_,
                    );
                    v___x_1068_ = v_reuseFailAlloc_1075_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1066_ == 0 {
                    lean_ctor_set(v___x_1065_, 0, v___x_1068_);
                    v___x_1070_ = v___x_1065_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1068_);
                    v___x_1070_ = v_reuseFailAlloc_1074_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1059_ == 0 {
                    lean_ctor_set(v___x_1058_, 0, v___x_1070_);
                    v___x_1072_ = v___x_1058_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
                    v___x_1072_ = v_reuseFailAlloc_1073_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1072_;
            }
            9 => {
                if v_isShared_1059_ == 0 {
                    lean_ctor_set(v___x_1058_, 0, v___x_1081_);
                    v___x_1083_ = v___x_1058_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
                    v___x_1083_ = v_reuseFailAlloc_1084_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1083_;
            }
            11 => {
                if v_isShared_1090_ == 0 {
                    v___x_1092_ = v___x_1089_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
                    v___x_1092_ = v_reuseFailAlloc_1093_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1092_;
            }
            13 => {
                v_trackZetaDelta_1124_ = lean_ctor_get_uint8(
                    v_a_1039_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1125_ = lean_ctor_get(v_a_1039_, 1);
                v_lctx_1126_ = lean_ctor_get(v_a_1039_, 2);
                v_localInstances_1127_ = lean_ctor_get(v_a_1039_, 3);
                v_defEqCtx_x3f_1128_ = lean_ctor_get(v_a_1039_, 4);
                v_synthPendingDepth_1129_ = lean_ctor_get(v_a_1039_, 5);
                v_canUnfold_x3f_1130_ = lean_ctor_get(v_a_1039_, 6);
                v_univApprox_1131_ = lean_ctor_get_uint8(
                    v_a_1039_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1132_ = lean_ctor_get_uint8(
                    v_a_1039_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1133_ = lean_ctor_get_uint8(
                    v_a_1039_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_1134_ = 1;
                v___x_1135_ = 0;
                v___x_1136_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_1136_, 0, v_unfoldThm_1034_);
                lean_ctor_set_uint8(
                    v___x_1136_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1134_,
                );
                lean_ctor_set_uint8(
                    v___x_1136_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_1135_,
                );
                v___x_1137_ = 2;
                if v_isShared_1123_ == 0 {
                    v_config_1139_ = v___x_1122_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 0 as u32, v_foApprox_1103_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 1 as u32, v_ctxApprox_1104_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1164_,
                        2 as u32,
                        v_quasiPatternApprox_1105_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 3 as u32, v_constApprox_1106_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 4 as u32, v_isDefEqStuckEx_1107_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 5 as u32, v_unificationHints_1108_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 6 as u32, v_proofIrrelevance_1109_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1164_,
                        7 as u32,
                        v_assignSyntheticOpaque_1110_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 8 as u32, v_offsetCnstrs_1111_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 10 as u32, v_etaStruct_1112_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 11 as u32, v_univApprox_1113_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 12 as u32, v_iota_1114_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 13 as u32, v_beta_1115_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 14 as u32, v_proj_1116_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 15 as u32, v_zeta_1117_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 16 as u32, v_zetaDelta_1118_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 17 as u32, v_zetaUnused_1119_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1164_, 18 as u32, v_zetaHave_1120_);
                    v_config_1139_ = v_reuseFailAlloc_1164_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                lean_ctor_set_uint8(v_config_1139_, 9 as u32, v___x_1137_);
                v___x_1140_ = l_Lean_Meta_Context_configKey(v_a_1039_);
                v___x_1141_ = 3u64;
                v___x_1142_ = lean_uint64_shift_right(v___x_1140_, v___x_1141_);
                v___x_1143_ =
                    l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0;
                v___x_1144_ = lean_unsigned_to_nat(1000);
                v___x_1145_ = lean_alloc_ctor(0, 5, (4) as u32);
                lean_ctor_set(v___x_1145_, 0, v___x_1143_);
                lean_ctor_set(v___x_1145_, 1, v___x_1143_);
                lean_ctor_set(v___x_1145_, 2, v___x_1101_);
                lean_ctor_set(v___x_1145_, 3, v___x_1144_);
                lean_ctor_set(v___x_1145_, 4, v___x_1136_);
                lean_ctor_set_uint8(
                    v___x_1145_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_1134_,
                );
                lean_ctor_set_uint8(
                    v___x_1145_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_1135_,
                );
                v___x_1146_ = (lean_unbox(v_a_1097_) as u8);
                lean_dec(v_a_1097_);
                lean_ctor_set_uint8(
                    v___x_1145_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v___x_1146_,
                );
                v___x_1147_ = (lean_unbox(v_a_1099_) as u8);
                lean_dec(v_a_1099_);
                lean_ctor_set_uint8(
                    v___x_1145_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 3) as u32,
                    v___x_1147_,
                );
                v___x_1148_ = lean_uint64_shift_left(v___x_1142_, v___x_1141_);
                v___x_1149_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1_once), _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1);
                v_key_1150_ = lean_uint64_lor(v___x_1148_, v___x_1149_);
                v___x_1151_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_1151_, 0, v_config_1139_);
                lean_ctor_set_uint64(
                    v___x_1151_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_1150_,
                );
                lean_inc(v_canUnfold_x3f_1130_);
                lean_inc(v_synthPendingDepth_1129_);
                lean_inc(v_defEqCtx_x3f_1128_);
                lean_inc_ref(v_localInstances_1127_);
                lean_inc_ref(v_lctx_1126_);
                lean_inc(v_zetaDeltaSet_1125_);
                v___x_1152_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_1152_, 0, v___x_1151_);
                lean_ctor_set(v___x_1152_, 1, v_zetaDeltaSet_1125_);
                lean_ctor_set(v___x_1152_, 2, v_lctx_1126_);
                lean_ctor_set(v___x_1152_, 3, v_localInstances_1127_);
                lean_ctor_set(v___x_1152_, 4, v_defEqCtx_x3f_1128_);
                lean_ctor_set(v___x_1152_, 5, v_synthPendingDepth_1129_);
                lean_ctor_set(v___x_1152_, 6, v_canUnfold_x3f_1130_);
                lean_ctor_set_uint8(
                    v___x_1152_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1124_,
                );
                lean_ctor_set_uint8(
                    v___x_1152_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1131_,
                );
                lean_ctor_set_uint8(
                    v___x_1152_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1132_,
                );
                lean_ctor_set_uint8(
                    v___x_1152_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1133_,
                );
                v___x_1153_ = l_Lean_Meta_Simp_tryTheorem_x3f(
                    v_e_1035_,
                    v___x_1145_,
                    v_a_1036_,
                    v_a_1037_,
                    v_a_1038_,
                    v___x_1152_,
                    v_a_1040_,
                    v_a_1041_,
                    v_a_1042_,
                );
                lean_dec_ref_known(v___x_1152_, 7);
                if lean_obj_tag(v___x_1153_) == 0 {
                    v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
                    lean_inc(v_a_1154_);
                    lean_dec_ref_known(v___x_1153_, 1);
                    v_a_1045_ = v_a_1154_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v___x_1153_) == 0 {
                        v_a_1155_ = lean_ctor_get(v___x_1153_, 0);
                        lean_inc(v_a_1155_);
                        lean_dec_ref_known(v___x_1153_, 1);
                        v_a_1045_ = v_a_1155_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1156_ = lean_ctor_get(v___x_1153_, 0);
                        v_isSharedCheck_1163_ = (!lean_is_exclusive(v___x_1153_)) as u8;
                        if v_isSharedCheck_1163_ == 0 {
                            v___x_1158_ = v___x_1153_;
                            v_isShared_1159_ = v_isSharedCheck_1163_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_1156_);
                            lean_dec(v___x_1153_);
                            v___x_1158_ = lean_box(0);
                            v_isShared_1159_ = v_isSharedCheck_1163_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            15 => {
                if v_isShared_1159_ == 0 {
                    v___x_1161_ = v___x_1158_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
                    v___x_1161_ = v_reuseFailAlloc_1162_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1161_;
            }
            17 => {
                if v_isShared_1169_ == 0 {
                    v___x_1171_ = v___x_1168_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
                    v___x_1171_ = v_reuseFailAlloc_1172_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1171_;
            }
            19 => {
                if v_isShared_1177_ == 0 {
                    v___x_1179_ = v___x_1176_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
                    v___x_1179_ = v_reuseFailAlloc_1180_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(
    mut v_unfoldThm_1182_: *mut LeanObject,
    mut v_e_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
    mut v_a_1190_: *mut LeanObject,
    mut v_a_1191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1192_: *mut LeanObject = core::ptr::null_mut();
    v_res_1192_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(
        v_unfoldThm_1182_,
        v_e_1183_,
        v_a_1184_,
        v_a_1185_,
        v_a_1186_,
        v_a_1187_,
        v_a_1188_,
        v_a_1189_,
        v_a_1190_,
    );
    lean_dec(v_a_1190_);
    lean_dec_ref(v_a_1189_);
    lean_dec(v_a_1188_);
    lean_dec_ref(v_a_1187_);
    lean_dec(v_a_1186_);
    lean_dec_ref(v_a_1185_);
    lean_dec(v_a_1184_);
    return v_res_1192_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__0(
    mut v_e_1193_: *mut LeanObject,
    mut v___y_1194_: *mut LeanObject,
    mut v___y_1195_: *mut LeanObject,
    mut v___y_1196_: *mut LeanObject,
    mut v___y_1197_: *mut LeanObject,
    mut v___y_1198_: *mut LeanObject,
    mut v___y_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    v___x_1202_ = lean_box(0);
    v___x_1203_ = 1;
    v___x_1204_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_1204_, 0, v_e_1193_);
    lean_ctor_set(v___x_1204_, 1, v___x_1202_);
    lean_ctor_set_uint8(
        v___x_1204_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_1203_,
    );
    v___x_1205_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1205_, 0, v___x_1204_);
    v___x_1206_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1206_, 0, v___x_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__0___boxed(
    mut v_e_1207_: *mut LeanObject,
    mut v___y_1208_: *mut LeanObject,
    mut v___y_1209_: *mut LeanObject,
    mut v___y_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1216_: *mut LeanObject = core::ptr::null_mut();
    v_res_1216_ = l_Lean_Meta_unfold___lam__0(
        v_e_1207_,
        v___y_1208_,
        v___y_1209_,
        v___y_1210_,
        v___y_1211_,
        v___y_1212_,
        v___y_1213_,
        v___y_1214_,
    );
    lean_dec(v___y_1214_);
    lean_dec_ref(v___y_1213_);
    lean_dec(v___y_1212_);
    lean_dec_ref(v___y_1211_);
    lean_dec(v___y_1210_);
    lean_dec_ref(v___y_1209_);
    lean_dec(v___y_1208_);
    return v_res_1216_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__1(
    mut v_x_1219_: *mut LeanObject,
    mut v___y_1220_: *mut LeanObject,
    mut v___y_1221_: *mut LeanObject,
    mut v___y_1222_: *mut LeanObject,
    mut v___y_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    v___x_1228_ = l_Lean_Meta_unfold___lam__1___closed__0;
    v___x_1229_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1229_, 0, v___x_1228_);
    return v___x_1229_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__1___boxed(
    mut v_x_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
    mut v___y_1232_: *mut LeanObject,
    mut v___y_1233_: *mut LeanObject,
    mut v___y_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
    mut v___y_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1239_: *mut LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Lean_Meta_unfold___lam__1(
        v_x_1230_,
        v___y_1231_,
        v___y_1232_,
        v___y_1233_,
        v___y_1234_,
        v___y_1235_,
        v___y_1236_,
        v___y_1237_,
    );
    lean_dec(v___y_1237_);
    lean_dec_ref(v___y_1236_);
    lean_dec(v___y_1235_);
    lean_dec_ref(v___y_1234_);
    lean_dec(v___y_1233_);
    lean_dec_ref(v___y_1232_);
    lean_dec(v___y_1231_);
    lean_dec_ref(v_x_1230_);
    return v_res_1239_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__2(
    mut v_e_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    v___x_1249_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1249_, 0, v_e_1240_);
    v___x_1250_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1250_, 0, v___x_1249_);
    return v___x_1250_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__2___boxed(
    mut v_e_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1260_: *mut LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_Lean_Meta_unfold___lam__2(
        v_e_1251_,
        v___y_1252_,
        v___y_1253_,
        v___y_1254_,
        v___y_1255_,
        v___y_1256_,
        v___y_1257_,
        v___y_1258_,
    );
    lean_dec(v___y_1258_);
    lean_dec_ref(v___y_1257_);
    lean_dec(v___y_1256_);
    lean_dec_ref(v___y_1255_);
    lean_dec(v___y_1254_);
    lean_dec_ref(v___y_1253_);
    lean_dec(v___y_1252_);
    return v_res_1260_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__3(
    mut v_x_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    v___x_1270_ = lean_box(0);
    v___x_1271_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1271_, 0, v___x_1270_);
    return v___x_1271_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__3___boxed(
    mut v_x_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1281_: *mut LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Lean_Meta_unfold___lam__3(
        v_x_1272_,
        v___y_1273_,
        v___y_1274_,
        v___y_1275_,
        v___y_1276_,
        v___y_1277_,
        v___y_1278_,
        v___y_1279_,
    );
    lean_dec(v___y_1279_);
    lean_dec_ref(v___y_1278_);
    lean_dec(v___y_1277_);
    lean_dec_ref(v___y_1276_);
    lean_dec(v___y_1275_);
    lean_dec_ref(v___y_1274_);
    lean_dec(v___y_1273_);
    lean_dec_ref(v_x_1272_);
    return v_res_1281_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__4(
    mut v_declName_1282_: *mut LeanObject,
    mut v_x_1283_: *mut LeanObject,
) -> u8 {
    let mut v___x_1284_: u8 = 0;
    v___x_1284_ = lean_name_eq(v_x_1283_, v_declName_1282_);
    return v___x_1284_;
}
pub unsafe fn l_Lean_Meta_unfold___lam__4___boxed(
    mut v_declName_1285_: *mut LeanObject,
    mut v_x_1286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1287_: u8 = 0;
    let mut v_r_1288_: *mut LeanObject = core::ptr::null_mut();
    v_res_1287_ = l_Lean_Meta_unfold___lam__4(v_declName_1285_, v_x_1286_);
    lean_dec(v_x_1286_);
    lean_dec(v_declName_1285_);
    v_r_1288_ = lean_box((v_res_1287_) as usize);
    return v_r_1288_;
}
pub unsafe fn _init_l_Lean_Meta_unfold___closed__4() -> *mut LeanObject {
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    v___x_1293_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1293_;
}
pub unsafe fn _init_l_Lean_Meta_unfold___closed__5() -> *mut LeanObject {
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    v___x_1294_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__4_once),
        _init_l_Lean_Meta_unfold___closed__4,
    );
    v___x_1295_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1295_, 0, v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn _init_l_Lean_Meta_unfold___closed__6() -> *mut LeanObject {
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    v___x_1296_ = lean_unsigned_to_nat(0);
    v___x_1297_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__5_once),
        _init_l_Lean_Meta_unfold___closed__5,
    );
    v___x_1298_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1298_, 0, v___x_1297_);
    lean_ctor_set(v___x_1298_, 1, v___x_1296_);
    return v___x_1298_;
}
pub unsafe fn _init_l_Lean_Meta_unfold___closed__7() -> *mut LeanObject {
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    v___x_1299_ = lean_unsigned_to_nat(32);
    v___x_1300_ = lean_mk_empty_array_with_capacity(v___x_1299_);
    v___x_1301_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1301_, 0, v___x_1300_);
    return v___x_1301_;
}
pub unsafe fn _init_l_Lean_Meta_unfold___closed__8() -> *mut LeanObject {
    let mut v___x_1302_: usize = 0;
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = 5usize;
    v___x_1303_ = lean_unsigned_to_nat(0);
    v___x_1304_ = lean_unsigned_to_nat(32);
    v___x_1305_ = lean_mk_empty_array_with_capacity(v___x_1304_);
    v___x_1306_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__7_once),
        _init_l_Lean_Meta_unfold___closed__7,
    );
    v___x_1307_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1307_, 0, v___x_1306_);
    lean_ctor_set(v___x_1307_, 1, v___x_1305_);
    lean_ctor_set(v___x_1307_, 2, v___x_1303_);
    lean_ctor_set(v___x_1307_, 3, v___x_1303_);
    lean_ctor_set_usize(v___x_1307_, 4, v___x_1302_);
    return v___x_1307_;
}
pub unsafe fn _init_l_Lean_Meta_unfold___closed__9() -> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    v___x_1308_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__8_once),
        _init_l_Lean_Meta_unfold___closed__8,
    );
    v___x_1309_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__5_once),
        _init_l_Lean_Meta_unfold___closed__5,
    );
    v___x_1310_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1310_, 0, v___x_1309_);
    lean_ctor_set(v___x_1310_, 1, v___x_1309_);
    lean_ctor_set(v___x_1310_, 2, v___x_1309_);
    lean_ctor_set(v___x_1310_, 3, v___x_1308_);
    return v___x_1310_;
}
pub unsafe fn _init_l_Lean_Meta_unfold___closed__10() -> *mut LeanObject {
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    v___x_1311_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__9_once),
        _init_l_Lean_Meta_unfold___closed__9,
    );
    v___x_1312_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__6_once),
        _init_l_Lean_Meta_unfold___closed__6,
    );
    v___x_1313_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1313_, 0, v___x_1312_);
    lean_ctor_set(v___x_1313_, 1, v___x_1311_);
    return v___x_1313_;
}
pub unsafe fn l_Lean_Meta_unfold(
    mut v_e_1314_: *mut LeanObject,
    mut v_declName_1315_: *mut LeanObject,
    mut v_a_1316_: *mut LeanObject,
    mut v_a_1317_: *mut LeanObject,
    mut v_a_1318_: *mut LeanObject,
    mut v_a_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v_fst_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut v_a_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_a_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1356_: u8 = 0;
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1360_: u8 = 0;
    let mut v___f_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1366_: u8 = 0;
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v_a_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1377_: u8 = 0;
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut v_a_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1385_: u8 = 0;
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1321_ = 0;
                lean_inc(v_declName_1315_);
                v___x_1322_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                    v_declName_1315_,
                    v___x_1321_,
                    v_a_1316_,
                    v_a_1317_,
                    v_a_1318_,
                    v_a_1319_,
                );
                if lean_obj_tag(v___x_1322_) == 0 {
                    v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
                    lean_inc(v_a_1323_);
                    lean_dec_ref_known(v___x_1322_, 1);
                    if lean_obj_tag(v_a_1323_) == 1 {
                        lean_dec(v_declName_1315_);
                        v_val_1324_ = lean_ctor_get(v_a_1323_, 0);
                        lean_inc(v_val_1324_);
                        lean_dec_ref_known(v_a_1323_, 1);
                        v___x_1325_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_1316_, v_a_1318_, v_a_1319_);
                        if lean_obj_tag(v___x_1325_) == 0 {
                            v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
                            lean_inc(v_a_1326_);
                            lean_dec_ref_known(v___x_1325_, 1);
                            v___f_1327_ = l_Lean_Meta_unfold___closed__0;
                            v___f_1328_ = l_Lean_Meta_unfold___closed__1;
                            v___f_1329_ = l_Lean_Meta_unfold___closed__2;
                            v___f_1330_ = l_Lean_Meta_unfold___closed__3;
                            v___x_1331_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__10),
                                core::ptr::addr_of_mut!(l_Lean_Meta_unfold___closed__10_once),
                                _init_l_Lean_Meta_unfold___closed__10,
                            );
                            v___x_1332_ = lean_alloc_closure(
                                l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                1,
                            );
                            lean_closure_set(v___x_1332_, 0, v_val_1324_);
                            v___x_1333_ = 1;
                            v___x_1334_ = lean_alloc_ctor(0, 5, (1) as u32);
                            lean_ctor_set(v___x_1334_, 0, v___x_1332_);
                            lean_ctor_set(v___x_1334_, 1, v___f_1327_);
                            lean_ctor_set(v___x_1334_, 2, v___f_1328_);
                            lean_ctor_set(v___x_1334_, 3, v___f_1329_);
                            lean_ctor_set(v___x_1334_, 4, v___f_1330_);
                            lean_ctor_set_uint8(
                                v___x_1334_,
                                (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                                v___x_1333_,
                            );
                            v___x_1335_ = l_Lean_Meta_Simp_main(
                                v_e_1314_,
                                v_a_1326_,
                                v___x_1331_,
                                v___x_1334_,
                                v_a_1316_,
                                v_a_1317_,
                                v_a_1318_,
                                v_a_1319_,
                            );
                            if lean_obj_tag(v___x_1335_) == 0 {
                                v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
                                v_isSharedCheck_1344_ = (!lean_is_exclusive(v___x_1335_)) as u8;
                                if v_isSharedCheck_1344_ == 0 {
                                    v___x_1338_ = v___x_1335_;
                                    v_isShared_1339_ = v_isSharedCheck_1344_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_1336_);
                                    lean_dec(v___x_1335_);
                                    v___x_1338_ = lean_box(0);
                                    v_isShared_1339_ = v_isSharedCheck_1344_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_1345_ = lean_ctor_get(v___x_1335_, 0);
                                v_isSharedCheck_1352_ = (!lean_is_exclusive(v___x_1335_)) as u8;
                                if v_isSharedCheck_1352_ == 0 {
                                    v___x_1347_ = v___x_1335_;
                                    v_isShared_1348_ = v_isSharedCheck_1352_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1345_);
                                    lean_dec(v___x_1335_);
                                    v___x_1347_ = lean_box(0);
                                    v_isShared_1348_ = v_isSharedCheck_1352_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_1324_);
                            lean_dec_ref(v_e_1314_);
                            v_a_1353_ = lean_ctor_get(v___x_1325_, 0);
                            v_isSharedCheck_1360_ = (!lean_is_exclusive(v___x_1325_)) as u8;
                            if v_isSharedCheck_1360_ == 0 {
                                v___x_1355_ = v___x_1325_;
                                v_isShared_1356_ = v_isSharedCheck_1360_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1353_);
                                lean_dec(v___x_1325_);
                                v___x_1355_ = lean_box(0);
                                v_isShared_1356_ = v_isSharedCheck_1360_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1323_);
                        v___f_1361_ = lean_alloc_closure(
                            l_Lean_Meta_unfold___lam__4___boxed as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        lean_closure_set(v___f_1361_, 0, v_declName_1315_);
                        v___x_1362_ = l_Lean_Meta_deltaExpand(
                            v_e_1314_,
                            v___f_1361_,
                            v___x_1321_,
                            v_a_1318_,
                            v_a_1319_,
                        );
                        if lean_obj_tag(v___x_1362_) == 0 {
                            v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
                            v_isSharedCheck_1373_ = (!lean_is_exclusive(v___x_1362_)) as u8;
                            if v_isSharedCheck_1373_ == 0 {
                                v___x_1365_ = v___x_1362_;
                                v_isShared_1366_ = v_isSharedCheck_1373_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_1363_);
                                lean_dec(v___x_1362_);
                                v___x_1365_ = lean_box(0);
                                v_isShared_1366_ = v_isSharedCheck_1373_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_1374_ = lean_ctor_get(v___x_1362_, 0);
                            v_isSharedCheck_1381_ = (!lean_is_exclusive(v___x_1362_)) as u8;
                            if v_isSharedCheck_1381_ == 0 {
                                v___x_1376_ = v___x_1362_;
                                v_isShared_1377_ = v_isSharedCheck_1381_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_1374_);
                                lean_dec(v___x_1362_);
                                v___x_1376_ = lean_box(0);
                                v_isShared_1377_ = v_isSharedCheck_1381_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_declName_1315_);
                    lean_dec_ref(v_e_1314_);
                    v_a_1382_ = lean_ctor_get(v___x_1322_, 0);
                    v_isSharedCheck_1389_ = (!lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1384_ = v___x_1322_;
                        v_isShared_1385_ = v_isSharedCheck_1389_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1382_);
                        lean_dec(v___x_1322_);
                        v___x_1384_ = lean_box(0);
                        v_isShared_1385_ = v_isSharedCheck_1389_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1340_ = lean_ctor_get(v_a_1336_, 0);
                lean_inc(v_fst_1340_);
                lean_dec(v_a_1336_);
                if v_isShared_1339_ == 0 {
                    lean_ctor_set(v___x_1338_, 0, v_fst_1340_);
                    v___x_1342_ = v___x_1338_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_fst_1340_);
                    v___x_1342_ = v_reuseFailAlloc_1343_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1342_;
            }
            3 => {
                if v_isShared_1348_ == 0 {
                    v___x_1350_ = v___x_1347_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
                    v___x_1350_ = v_reuseFailAlloc_1351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1350_;
            }
            5 => {
                if v_isShared_1356_ == 0 {
                    v___x_1358_ = v___x_1355_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
                    v___x_1358_ = v_reuseFailAlloc_1359_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1358_;
            }
            7 => {
                v___x_1367_ = lean_box(0);
                v___x_1368_ = 1;
                v___x_1369_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_1369_, 0, v_a_1363_);
                lean_ctor_set(v___x_1369_, 1, v___x_1367_);
                lean_ctor_set_uint8(
                    v___x_1369_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_1368_,
                );
                if v_isShared_1366_ == 0 {
                    lean_ctor_set(v___x_1365_, 0, v___x_1369_);
                    v___x_1371_ = v___x_1365_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
                    v___x_1371_ = v_reuseFailAlloc_1372_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1371_;
            }
            9 => {
                if v_isShared_1377_ == 0 {
                    v___x_1379_ = v___x_1376_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
                    v___x_1379_ = v_reuseFailAlloc_1380_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1379_;
            }
            11 => {
                if v_isShared_1385_ == 0 {
                    v___x_1387_ = v___x_1384_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
                    v___x_1387_ = v_reuseFailAlloc_1388_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_unfold___boxed(
    mut v_e_1390_: *mut LeanObject,
    mut v_declName_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
    mut v_a_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
    mut v_a_1396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1397_: *mut LeanObject = core::ptr::null_mut();
    v_res_1397_ = l_Lean_Meta_unfold(
        v_e_1390_,
        v_declName_1391_,
        v_a_1392_,
        v_a_1393_,
        v_a_1394_,
        v_a_1395_,
    );
    lean_dec(v_a_1395_);
    lean_dec_ref(v_a_1394_);
    lean_dec(v_a_1393_);
    lean_dec_ref(v_a_1392_);
    return v_res_1397_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(
    mut v_e_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut v_unused_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1401_ = l_Lean_Expr_hasMVar(v_e_1398_);
                if v___x_1401_ == 0 {
                    v___x_1402_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1402_, 0, v_e_1398_);
                    return v___x_1402_;
                } else {
                    v___x_1403_ = lean_st_ref_get(v___y_1399_);
                    v_mctx_1404_ = lean_ctor_get(v___x_1403_, 0);
                    lean_inc_ref(v_mctx_1404_);
                    lean_dec(v___x_1403_);
                    v___x_1405_ = l_Lean_instantiateMVarsCore(v_mctx_1404_, v_e_1398_);
                    v_fst_1406_ = lean_ctor_get(v___x_1405_, 0);
                    lean_inc(v_fst_1406_);
                    v_snd_1407_ = lean_ctor_get(v___x_1405_, 1);
                    lean_inc(v_snd_1407_);
                    lean_dec_ref(v___x_1405_);
                    v___x_1408_ = lean_st_ref_take(v___y_1399_);
                    v_cache_1409_ = lean_ctor_get(v___x_1408_, 1);
                    v_zetaDeltaFVarIds_1410_ = lean_ctor_get(v___x_1408_, 2);
                    v_postponed_1411_ = lean_ctor_get(v___x_1408_, 3);
                    v_diag_1412_ = lean_ctor_get(v___x_1408_, 4);
                    v_isSharedCheck_1421_ = (!lean_is_exclusive(v___x_1408_)) as u8;
                    if v_isSharedCheck_1421_ == 0 {
                        v_unused_1422_ = lean_ctor_get(v___x_1408_, 0);
                        lean_dec(v_unused_1422_);
                        v___x_1414_ = v___x_1408_;
                        v_isShared_1415_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1412_);
                        lean_inc(v_postponed_1411_);
                        lean_inc(v_zetaDeltaFVarIds_1410_);
                        lean_inc(v_cache_1409_);
                        lean_dec(v___x_1408_);
                        v___x_1414_ = lean_box(0);
                        v_isShared_1415_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1415_ == 0 {
                    lean_ctor_set(v___x_1414_, 0, v_snd_1407_);
                    v___x_1417_ = v___x_1414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_snd_1407_);
                    lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_cache_1409_);
                    lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_zetaDeltaFVarIds_1410_);
                    lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_postponed_1411_);
                    lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_diag_1412_);
                    v___x_1417_ = v_reuseFailAlloc_1420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1418_ = lean_st_ref_set(v___y_1399_, v___x_1417_);
                v___x_1419_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1419_, 0, v_fst_1406_);
                return v___x_1419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(
    mut v_e_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1426_: *mut LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(
        v_e_1423_,
        v___y_1424_,
    );
    lean_dec(v___y_1424_);
    return v_res_1426_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(
    mut v_e_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
    mut v___y_1429_: *mut LeanObject,
    mut v___y_1430_: *mut LeanObject,
    mut v___y_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(
        v_e_1427_,
        v___y_1429_,
    );
    return v___x_1433_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(
    mut v_e_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
    mut v___y_1436_: *mut LeanObject,
    mut v___y_1437_: *mut LeanObject,
    mut v___y_1438_: *mut LeanObject,
    mut v___y_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1440_: *mut LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(
        v_e_1434_,
        v___y_1435_,
        v___y_1436_,
        v___y_1437_,
        v___y_1438_,
    );
    lean_dec(v___y_1438_);
    lean_dec_ref(v___y_1437_);
    lean_dec(v___y_1436_);
    lean_dec_ref(v___y_1435_);
    return v_res_1440_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(
    mut v_mvarId_1441_: *mut LeanObject,
    mut v_x_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v_a_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1460_: u8 = 0;
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1448_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1441_,
                    v_x_1442_,
                    v___y_1443_,
                    v___y_1444_,
                    v___y_1445_,
                    v___y_1446_,
                );
                if lean_obj_tag(v___x_1448_) == 0 {
                    v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
                    v_isSharedCheck_1456_ = (!lean_is_exclusive(v___x_1448_)) as u8;
                    if v_isSharedCheck_1456_ == 0 {
                        v___x_1451_ = v___x_1448_;
                        v_isShared_1452_ = v_isSharedCheck_1456_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1449_);
                        lean_dec(v___x_1448_);
                        v___x_1451_ = lean_box(0);
                        v_isShared_1452_ = v_isSharedCheck_1456_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1457_ = lean_ctor_get(v___x_1448_, 0);
                    v_isSharedCheck_1464_ = (!lean_is_exclusive(v___x_1448_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v___x_1459_ = v___x_1448_;
                        v_isShared_1460_ = v_isSharedCheck_1464_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1457_);
                        lean_dec(v___x_1448_);
                        v___x_1459_ = lean_box(0);
                        v_isShared_1460_ = v_isSharedCheck_1464_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1452_ == 0 {
                    v___x_1454_ = v___x_1451_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
                    v___x_1454_ = v_reuseFailAlloc_1455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1454_;
            }
            3 => {
                if v_isShared_1460_ == 0 {
                    v___x_1462_ = v___x_1459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
                    v___x_1462_ = v_reuseFailAlloc_1463_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg___boxed(
    mut v_mvarId_1465_: *mut LeanObject,
    mut v_x_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1472_: *mut LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(
        v_mvarId_1465_,
        v_x_1466_,
        v___y_1467_,
        v___y_1468_,
        v___y_1469_,
        v___y_1470_,
    );
    lean_dec(v___y_1470_);
    lean_dec_ref(v___y_1469_);
    lean_dec(v___y_1468_);
    lean_dec_ref(v___y_1467_);
    return v_res_1472_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(
    mut v_00_u03b1_1473_: *mut LeanObject,
    mut v_mvarId_1474_: *mut LeanObject,
    mut v_x_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
    mut v___y_1478_: *mut LeanObject,
    mut v___y_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(
        v_mvarId_1474_,
        v_x_1475_,
        v___y_1476_,
        v___y_1477_,
        v___y_1478_,
        v___y_1479_,
    );
    return v___x_1481_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___boxed(
    mut v_00_u03b1_1482_: *mut LeanObject,
    mut v_mvarId_1483_: *mut LeanObject,
    mut v_x_1484_: *mut LeanObject,
    mut v___y_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
    mut v___y_1488_: *mut LeanObject,
    mut v___y_1489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1490_: *mut LeanObject = core::ptr::null_mut();
    v_res_1490_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(
        v_00_u03b1_1482_,
        v_mvarId_1483_,
        v_x_1484_,
        v___y_1485_,
        v___y_1486_,
        v___y_1487_,
        v___y_1488_,
    );
    lean_dec(v___y_1488_);
    lean_dec_ref(v___y_1487_);
    lean_dec(v___y_1486_);
    lean_dec_ref(v___y_1485_);
    return v_res_1490_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(
    mut v_msgData_1491_: *mut LeanObject,
    mut v___y_1492_: *mut LeanObject,
    mut v___y_1493_: *mut LeanObject,
    mut v___y_1494_: *mut LeanObject,
    mut v___y_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    v___x_1497_ = lean_st_ref_get(v___y_1495_);
    v_env_1498_ = lean_ctor_get(v___x_1497_, 0);
    lean_inc_ref(v_env_1498_);
    lean_dec(v___x_1497_);
    v___x_1499_ = lean_st_ref_get(v___y_1493_);
    v_mctx_1500_ = lean_ctor_get(v___x_1499_, 0);
    lean_inc_ref(v_mctx_1500_);
    lean_dec(v___x_1499_);
    v_lctx_1501_ = lean_ctor_get(v___y_1492_, 2);
    v_options_1502_ = lean_ctor_get(v___y_1494_, 2);
    lean_inc_ref(v_options_1502_);
    lean_inc_ref(v_lctx_1501_);
    v___x_1503_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1503_, 0, v_env_1498_);
    lean_ctor_set(v___x_1503_, 1, v_mctx_1500_);
    lean_ctor_set(v___x_1503_, 2, v_lctx_1501_);
    lean_ctor_set(v___x_1503_, 3, v_options_1502_);
    v___x_1504_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1504_, 0, v___x_1503_);
    lean_ctor_set(v___x_1504_, 1, v_msgData_1491_);
    v___x_1505_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1505_, 0, v___x_1504_);
    return v___x_1505_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(
    mut v_msgData_1506_: *mut LeanObject,
    mut v___y_1507_: *mut LeanObject,
    mut v___y_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
    mut v___y_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1512_: *mut LeanObject = core::ptr::null_mut();
    v_res_1512_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msgData_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
    lean_dec(v___y_1510_);
    lean_dec_ref(v___y_1509_);
    lean_dec(v___y_1508_);
    lean_dec_ref(v___y_1507_);
    return v_res_1512_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(
    mut v_msg_1513_: *mut LeanObject,
    mut v___y_1514_: *mut LeanObject,
    mut v___y_1515_: *mut LeanObject,
    mut v___y_1516_: *mut LeanObject,
    mut v___y_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1519_ = lean_ctor_get(v___y_1516_, 5);
                v___x_1520_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msg_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
                v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
                v_isSharedCheck_1529_ = (!lean_is_exclusive(v___x_1520_)) as u8;
                if v_isSharedCheck_1529_ == 0 {
                    v___x_1523_ = v___x_1520_;
                    v_isShared_1524_ = v_isSharedCheck_1529_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1521_);
                    lean_dec(v___x_1520_);
                    v___x_1523_ = lean_box(0);
                    v_isShared_1524_ = v_isSharedCheck_1529_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1519_);
                v___x_1525_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1525_, 0, v_ref_1519_);
                lean_ctor_set(v___x_1525_, 1, v_a_1521_);
                if v_isShared_1524_ == 0 {
                    lean_ctor_set_tag(v___x_1523_, 1);
                    lean_ctor_set(v___x_1523_, 0, v___x_1525_);
                    v___x_1527_ = v___x_1523_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
                    v___x_1527_ = v_reuseFailAlloc_1528_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg___boxed(
    mut v_msg_1530_: *mut LeanObject,
    mut v___y_1531_: *mut LeanObject,
    mut v___y_1532_: *mut LeanObject,
    mut v___y_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1536_: *mut LeanObject = core::ptr::null_mut();
    v_res_1536_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(
        v_msg_1530_,
        v___y_1531_,
        v___y_1532_,
        v___y_1533_,
        v___y_1534_,
    );
    lean_dec(v___y_1534_);
    lean_dec_ref(v___y_1533_);
    lean_dec(v___y_1532_);
    lean_dec_ref(v___y_1531_);
    return v_res_1536_;
}
pub unsafe fn _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_Lean_Meta_unfoldTarget___lam__0___closed__0;
    v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    v___x_1541_ = l_Lean_Meta_unfoldTarget___lam__0___closed__2;
    v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
    return v___x_1542_;
}
pub unsafe fn l_Lean_Meta_unfoldTarget___lam__0(
    mut v_mvarId_1543_: *mut LeanObject,
    mut v_declName_1544_: *mut LeanObject,
    mut v___y_1545_: *mut LeanObject,
    mut v___y_1546_: *mut LeanObject,
    mut v___y_1547_: *mut LeanObject,
    mut v___y_1548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: u8 = 0;
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1575_: u8 = 0;
    let mut v_a_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1583_: u8 = 0;
    let mut v_a_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_1543_);
                v___x_1550_ = l_Lean_MVarId_getType(
                    v_mvarId_1543_,
                    v___y_1545_,
                    v___y_1546_,
                    v___y_1547_,
                    v___y_1548_,
                );
                if lean_obj_tag(v___x_1550_) == 0 {
                    v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
                    lean_inc(v_a_1551_);
                    lean_dec_ref_known(v___x_1550_, 1);
                    v___x_1552_ =
                        l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(
                            v_a_1551_,
                            v___y_1546_,
                        );
                    v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
                    lean_inc_n(v_a_1553_, 2);
                    lean_dec_ref(v___x_1552_);
                    lean_inc(v_declName_1544_);
                    v___x_1554_ = l_Lean_Meta_unfold(
                        v_a_1553_,
                        v_declName_1544_,
                        v___y_1545_,
                        v___y_1546_,
                        v___y_1547_,
                        v___y_1548_,
                    );
                    if lean_obj_tag(v___x_1554_) == 0 {
                        v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
                        lean_inc(v_a_1555_);
                        lean_dec_ref_known(v___x_1554_, 1);
                        v_expr_1556_ = lean_ctor_get(v_a_1555_, 0);
                        v___x_1557_ = lean_expr_eqv(v_expr_1556_, v_a_1553_);
                        if v___x_1557_ == 0 {
                            lean_dec(v_declName_1544_);
                            v___x_1558_ = l_Lean_Meta_applySimpResultToTarget(
                                v_mvarId_1543_,
                                v_a_1553_,
                                v_a_1555_,
                                v___y_1545_,
                                v___y_1546_,
                                v___y_1547_,
                                v___y_1548_,
                            );
                            lean_dec(v_a_1553_);
                            return v___x_1558_;
                        } else {
                            lean_dec(v_a_1555_);
                            lean_dec(v_mvarId_1543_);
                            v___x_1559_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__1_once
                                ),
                                _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1,
                            );
                            v___x_1560_ = 0;
                            v___x_1561_ =
                                l_Lean_MessageData_ofConstName(v_declName_1544_, v___x_1560_);
                            v___x_1562_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1562_, 0, v___x_1559_);
                            lean_ctor_set(v___x_1562_, 1, v___x_1561_);
                            v___x_1563_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__3_once
                                ),
                                _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3,
                            );
                            v___x_1564_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1564_, 0, v___x_1562_);
                            lean_ctor_set(v___x_1564_, 1, v___x_1563_);
                            v___x_1565_ = l_Lean_indentExpr(v_a_1553_);
                            v___x_1566_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1566_, 0, v___x_1564_);
                            lean_ctor_set(v___x_1566_, 1, v___x_1565_);
                            v___x_1567_ =
                                l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(
                                    v___x_1566_,
                                    v___y_1545_,
                                    v___y_1546_,
                                    v___y_1547_,
                                    v___y_1548_,
                                );
                            v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
                            v_isSharedCheck_1575_ = (!lean_is_exclusive(v___x_1567_)) as u8;
                            if v_isSharedCheck_1575_ == 0 {
                                v___x_1570_ = v___x_1567_;
                                v_isShared_1571_ = v_isSharedCheck_1575_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1568_);
                                lean_dec(v___x_1567_);
                                v___x_1570_ = lean_box(0);
                                v_isShared_1571_ = v_isSharedCheck_1575_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1553_);
                        lean_dec(v_declName_1544_);
                        lean_dec(v_mvarId_1543_);
                        v_a_1576_ = lean_ctor_get(v___x_1554_, 0);
                        v_isSharedCheck_1583_ = (!lean_is_exclusive(v___x_1554_)) as u8;
                        if v_isSharedCheck_1583_ == 0 {
                            v___x_1578_ = v___x_1554_;
                            v_isShared_1579_ = v_isSharedCheck_1583_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1576_);
                            lean_dec(v___x_1554_);
                            v___x_1578_ = lean_box(0);
                            v_isShared_1579_ = v_isSharedCheck_1583_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_1544_);
                    lean_dec(v_mvarId_1543_);
                    v_a_1584_ = lean_ctor_get(v___x_1550_, 0);
                    v_isSharedCheck_1591_ = (!lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1591_ == 0 {
                        v___x_1586_ = v___x_1550_;
                        v_isShared_1587_ = v_isSharedCheck_1591_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1584_);
                        lean_dec(v___x_1550_);
                        v___x_1586_ = lean_box(0);
                        v_isShared_1587_ = v_isSharedCheck_1591_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1571_ == 0 {
                    v___x_1573_ = v___x_1570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
                    v___x_1573_ = v_reuseFailAlloc_1574_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1573_;
            }
            3 => {
                if v_isShared_1579_ == 0 {
                    v___x_1581_ = v___x_1578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
                    v___x_1581_ = v_reuseFailAlloc_1582_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1581_;
            }
            5 => {
                if v_isShared_1587_ == 0 {
                    v___x_1589_ = v___x_1586_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
                    v___x_1589_ = v_reuseFailAlloc_1590_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_unfoldTarget___lam__0___boxed(
    mut v_mvarId_1592_: *mut LeanObject,
    mut v_declName_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Lean_Meta_unfoldTarget___lam__0(
        v_mvarId_1592_,
        v_declName_1593_,
        v___y_1594_,
        v___y_1595_,
        v___y_1596_,
        v___y_1597_,
    );
    lean_dec(v___y_1597_);
    lean_dec_ref(v___y_1596_);
    lean_dec(v___y_1595_);
    lean_dec_ref(v___y_1594_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_Meta_unfoldTarget(
    mut v_mvarId_1600_: *mut LeanObject,
    mut v_declName_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_1600_);
    v___f_1607_ = lean_alloc_closure(
        l_Lean_Meta_unfoldTarget___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_1607_, 0, v_mvarId_1600_);
    lean_closure_set(v___f_1607_, 1, v_declName_1601_);
    v___x_1608_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(
        v_mvarId_1600_,
        v___f_1607_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
    );
    return v___x_1608_;
}
pub unsafe fn l_Lean_Meta_unfoldTarget___boxed(
    mut v_mvarId_1609_: *mut LeanObject,
    mut v_declName_1610_: *mut LeanObject,
    mut v_a_1611_: *mut LeanObject,
    mut v_a_1612_: *mut LeanObject,
    mut v_a_1613_: *mut LeanObject,
    mut v_a_1614_: *mut LeanObject,
    mut v_a_1615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1616_: *mut LeanObject = core::ptr::null_mut();
    v_res_1616_ = l_Lean_Meta_unfoldTarget(
        v_mvarId_1609_,
        v_declName_1610_,
        v_a_1611_,
        v_a_1612_,
        v_a_1613_,
        v_a_1614_,
    );
    lean_dec(v_a_1614_);
    lean_dec_ref(v_a_1613_);
    lean_dec(v_a_1612_);
    lean_dec_ref(v_a_1611_);
    return v_res_1616_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(
    mut v_00_u03b1_1617_: *mut LeanObject,
    mut v_msg_1618_: *mut LeanObject,
    mut v___y_1619_: *mut LeanObject,
    mut v___y_1620_: *mut LeanObject,
    mut v___y_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    v___x_1624_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(
        v_msg_1618_,
        v___y_1619_,
        v___y_1620_,
        v___y_1621_,
        v___y_1622_,
    );
    return v___x_1624_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(
    mut v_00_u03b1_1625_: *mut LeanObject,
    mut v_msg_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
    mut v___y_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1632_: *mut LeanObject = core::ptr::null_mut();
    v_res_1632_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(
        v_00_u03b1_1625_,
        v_msg_1626_,
        v___y_1627_,
        v___y_1628_,
        v___y_1629_,
        v___y_1630_,
    );
    lean_dec(v___y_1630_);
    lean_dec_ref(v___y_1629_);
    lean_dec(v___y_1628_);
    lean_dec_ref(v___y_1627_);
    return v_res_1632_;
}
pub unsafe fn l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(
    mut v_msg_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976__overap_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    v___f_1640_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0;
    v___x_976__overap_1641_ = lean_panic_fn_borrowed(v___f_1640_, v_msg_1634_);
    lean_inc(v___y_1638_);
    lean_inc_ref(v___y_1637_);
    lean_inc(v___y_1636_);
    lean_inc_ref(v___y_1635_);
    v___x_1642_ = lean_apply_5(
        v___x_976__overap_1641_,
        v___y_1635_,
        v___y_1636_,
        v___y_1637_,
        v___y_1638_,
        lean_box(0),
    );
    return v___x_1642_;
}
pub unsafe fn l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(
    mut v_msg_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
    mut v___y_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1649_: *mut LeanObject = core::ptr::null_mut();
    v_res_1649_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(
        v_msg_1643_,
        v___y_1644_,
        v___y_1645_,
        v___y_1646_,
        v___y_1647_,
    );
    lean_dec(v___y_1647_);
    lean_dec_ref(v___y_1646_);
    lean_dec(v___y_1645_);
    lean_dec_ref(v___y_1644_);
    return v_res_1649_;
}
pub unsafe fn _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    v___x_1653_ = l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2;
    v___x_1654_ = lean_unsigned_to_nat(94);
    v___x_1655_ = lean_unsigned_to_nat(43);
    v___x_1656_ = l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1;
    v___x_1657_ = l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0;
    v___x_1658_ = l_mkPanicMessageWithDecl(
        v___x_1657_,
        v___x_1656_,
        v___x_1655_,
        v___x_1654_,
        v___x_1653_,
    );
    return v___x_1658_;
}
pub unsafe fn l_Lean_Meta_unfoldLocalDecl___lam__0(
    mut v_fvarId_1659_: *mut LeanObject,
    mut v_declName_1660_: *mut LeanObject,
    mut v_mvarId_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: u8 = 0;
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v_val_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut v_a_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1699_: u8 = 0;
    let mut v_expr_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: u8 = 0;
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1714_: u8 = 0;
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_a_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1722_: u8 = 0;
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1726_: u8 = 0;
    let mut v_a_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_1659_);
                v___x_1667_ = l_Lean_FVarId_getType___redArg(
                    v_fvarId_1659_,
                    v___y_1662_,
                    v___y_1664_,
                    v___y_1665_,
                );
                if lean_obj_tag(v___x_1667_) == 0 {
                    v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
                    lean_inc_n(v_a_1668_, 2);
                    lean_dec_ref_known(v___x_1667_, 1);
                    v___x_1669_ =
                        l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(
                            v_a_1668_,
                            v___y_1663_,
                        );
                    v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
                    lean_inc(v_a_1670_);
                    lean_dec_ref(v___x_1669_);
                    lean_inc(v_declName_1660_);
                    v___x_1671_ = l_Lean_Meta_unfold(
                        v_a_1670_,
                        v_declName_1660_,
                        v___y_1662_,
                        v___y_1663_,
                        v___y_1664_,
                        v___y_1665_,
                    );
                    if lean_obj_tag(v___x_1671_) == 0 {
                        v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
                        lean_inc(v_a_1672_);
                        lean_dec_ref_known(v___x_1671_, 1);
                        v_expr_1700_ = lean_ctor_get(v_a_1672_, 0);
                        v___x_1701_ = lean_expr_eqv(v_expr_1700_, v_a_1668_);
                        if v___x_1701_ == 0 {
                            lean_dec(v_a_1668_);
                            lean_dec(v_declName_1660_);
                            v___y_1674_ = v___y_1662_;
                            v___y_1675_ = v___y_1663_;
                            v___y_1676_ = v___y_1664_;
                            v___y_1677_ = v___y_1665_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_1672_);
                            lean_dec(v_mvarId_1661_);
                            lean_dec(v_fvarId_1659_);
                            v___x_1702_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__1_once
                                ),
                                _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1,
                            );
                            v___x_1703_ = 0;
                            v___x_1704_ =
                                l_Lean_MessageData_ofConstName(v_declName_1660_, v___x_1703_);
                            v___x_1705_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1705_, 0, v___x_1702_);
                            lean_ctor_set(v___x_1705_, 1, v___x_1704_);
                            v___x_1706_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__3_once
                                ),
                                _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3,
                            );
                            v___x_1707_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1707_, 0, v___x_1705_);
                            lean_ctor_set(v___x_1707_, 1, v___x_1706_);
                            v___x_1708_ = l_Lean_indentExpr(v_a_1668_);
                            v___x_1709_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1709_, 0, v___x_1707_);
                            lean_ctor_set(v___x_1709_, 1, v___x_1708_);
                            v___x_1710_ =
                                l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(
                                    v___x_1709_,
                                    v___y_1662_,
                                    v___y_1663_,
                                    v___y_1664_,
                                    v___y_1665_,
                                );
                            v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
                            v_isSharedCheck_1718_ = (!lean_is_exclusive(v___x_1710_)) as u8;
                            if v_isSharedCheck_1718_ == 0 {
                                v___x_1713_ = v___x_1710_;
                                v_isShared_1714_ = v_isSharedCheck_1718_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1711_);
                                lean_dec(v___x_1710_);
                                v___x_1713_ = lean_box(0);
                                v_isShared_1714_ = v_isSharedCheck_1718_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1668_);
                        lean_dec(v_mvarId_1661_);
                        lean_dec(v_declName_1660_);
                        lean_dec(v_fvarId_1659_);
                        v_a_1719_ = lean_ctor_get(v___x_1671_, 0);
                        v_isSharedCheck_1726_ = (!lean_is_exclusive(v___x_1671_)) as u8;
                        if v_isSharedCheck_1726_ == 0 {
                            v___x_1721_ = v___x_1671_;
                            v_isShared_1722_ = v_isSharedCheck_1726_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1719_);
                            lean_dec(v___x_1671_);
                            v___x_1721_ = lean_box(0);
                            v_isShared_1722_ = v_isSharedCheck_1726_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_1661_);
                    lean_dec(v_declName_1660_);
                    lean_dec(v_fvarId_1659_);
                    v_a_1727_ = lean_ctor_get(v___x_1667_, 0);
                    v_isSharedCheck_1734_ = (!lean_is_exclusive(v___x_1667_)) as u8;
                    if v_isSharedCheck_1734_ == 0 {
                        v___x_1729_ = v___x_1667_;
                        v_isShared_1730_ = v_isSharedCheck_1734_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1727_);
                        lean_dec(v___x_1667_);
                        v___x_1729_ = lean_box(0);
                        v_isShared_1730_ = v_isSharedCheck_1734_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1678_ = 0;
                v___x_1679_ = l_Lean_Meta_applySimpResultToLocalDecl(
                    v_mvarId_1661_,
                    v_fvarId_1659_,
                    v_a_1672_,
                    v___x_1678_,
                    v___y_1674_,
                    v___y_1675_,
                    v___y_1676_,
                    v___y_1677_,
                );
                if lean_obj_tag(v___x_1679_) == 0 {
                    v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
                    v_isSharedCheck_1691_ = (!lean_is_exclusive(v___x_1679_)) as u8;
                    if v_isSharedCheck_1691_ == 0 {
                        v___x_1682_ = v___x_1679_;
                        v_isShared_1683_ = v_isSharedCheck_1691_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1680_);
                        lean_dec(v___x_1679_);
                        v___x_1682_ = lean_box(0);
                        v_isShared_1683_ = v_isSharedCheck_1691_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1692_ = lean_ctor_get(v___x_1679_, 0);
                    v_isSharedCheck_1699_ = (!lean_is_exclusive(v___x_1679_)) as u8;
                    if v_isSharedCheck_1699_ == 0 {
                        v___x_1694_ = v___x_1679_;
                        v_isShared_1695_ = v_isSharedCheck_1699_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1692_);
                        lean_dec(v___x_1679_);
                        v___x_1694_ = lean_box(0);
                        v_isShared_1695_ = v_isSharedCheck_1699_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1680_) == 1 {
                    v_val_1684_ = lean_ctor_get(v_a_1680_, 0);
                    lean_inc(v_val_1684_);
                    lean_dec_ref_known(v_a_1680_, 1);
                    v_snd_1685_ = lean_ctor_get(v_val_1684_, 1);
                    lean_inc(v_snd_1685_);
                    lean_dec(v_val_1684_);
                    if v_isShared_1683_ == 0 {
                        lean_ctor_set(v___x_1682_, 0, v_snd_1685_);
                        v___x_1687_ = v___x_1682_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_snd_1685_);
                        v___x_1687_ = v_reuseFailAlloc_1688_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1682_);
                    lean_dec(v_a_1680_);
                    v___x_1689_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3,
                    );
                    v___x_1690_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(
                        v___x_1689_,
                        v___y_1674_,
                        v___y_1675_,
                        v___y_1676_,
                        v___y_1677_,
                    );
                    return v___x_1690_;
                }
            }
            3 => {
                return v___x_1687_;
            }
            4 => {
                if v_isShared_1695_ == 0 {
                    v___x_1697_ = v___x_1694_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
                    v___x_1697_ = v_reuseFailAlloc_1698_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1697_;
            }
            6 => {
                if v_isShared_1714_ == 0 {
                    v___x_1716_ = v___x_1713_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
                    v___x_1716_ = v_reuseFailAlloc_1717_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1716_;
            }
            8 => {
                if v_isShared_1722_ == 0 {
                    v___x_1724_ = v___x_1721_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
                    v___x_1724_ = v_reuseFailAlloc_1725_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1724_;
            }
            10 => {
                if v_isShared_1730_ == 0 {
                    v___x_1732_ = v___x_1729_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
                    v___x_1732_ = v_reuseFailAlloc_1733_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(
    mut v_fvarId_1735_: *mut LeanObject,
    mut v_declName_1736_: *mut LeanObject,
    mut v_mvarId_1737_: *mut LeanObject,
    mut v___y_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1743_: *mut LeanObject = core::ptr::null_mut();
    v_res_1743_ = l_Lean_Meta_unfoldLocalDecl___lam__0(
        v_fvarId_1735_,
        v_declName_1736_,
        v_mvarId_1737_,
        v___y_1738_,
        v___y_1739_,
        v___y_1740_,
        v___y_1741_,
    );
    lean_dec(v___y_1741_);
    lean_dec_ref(v___y_1740_);
    lean_dec(v___y_1739_);
    lean_dec_ref(v___y_1738_);
    return v_res_1743_;
}
pub unsafe fn l_Lean_Meta_unfoldLocalDecl(
    mut v_mvarId_1744_: *mut LeanObject,
    mut v_fvarId_1745_: *mut LeanObject,
    mut v_declName_1746_: *mut LeanObject,
    mut v_a_1747_: *mut LeanObject,
    mut v_a_1748_: *mut LeanObject,
    mut v_a_1749_: *mut LeanObject,
    mut v_a_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_1744_);
    v___f_1752_ = lean_alloc_closure(
        l_Lean_Meta_unfoldLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_1752_, 0, v_fvarId_1745_);
    lean_closure_set(v___f_1752_, 1, v_declName_1746_);
    lean_closure_set(v___f_1752_, 2, v_mvarId_1744_);
    v___x_1753_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(
        v_mvarId_1744_,
        v___f_1752_,
        v_a_1747_,
        v_a_1748_,
        v_a_1749_,
        v_a_1750_,
    );
    return v___x_1753_;
}
pub unsafe fn l_Lean_Meta_unfoldLocalDecl___boxed(
    mut v_mvarId_1754_: *mut LeanObject,
    mut v_fvarId_1755_: *mut LeanObject,
    mut v_declName_1756_: *mut LeanObject,
    mut v_a_1757_: *mut LeanObject,
    mut v_a_1758_: *mut LeanObject,
    mut v_a_1759_: *mut LeanObject,
    mut v_a_1760_: *mut LeanObject,
    mut v_a_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Lean_Meta_unfoldLocalDecl(
        v_mvarId_1754_,
        v_fvarId_1755_,
        v_declName_1756_,
        v_a_1757_,
        v_a_1758_,
        v_a_1759_,
        v_a_1760_,
    );
    lean_dec(v_a_1760_);
    lean_dec_ref(v_a_1759_);
    lean_dec(v_a_1758_);
    lean_dec_ref(v_a_1757_);
    return v_res_1762_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaTarget___lam__0(
    mut v_mvarId_1763_: *mut LeanObject,
    mut v_declFVarId_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
    mut v___y_1766_: *mut LeanObject,
    mut v___y_1767_: *mut LeanObject,
    mut v___y_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut v_a_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1801_: u8 = 0;
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut v_a_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_1763_);
                v___x_1770_ = l_Lean_MVarId_getType(
                    v_mvarId_1763_,
                    v___y_1765_,
                    v___y_1766_,
                    v___y_1767_,
                    v___y_1768_,
                );
                if lean_obj_tag(v___x_1770_) == 0 {
                    v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
                    lean_inc(v_a_1771_);
                    lean_dec_ref_known(v___x_1770_, 1);
                    v___x_1772_ =
                        l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(
                            v_a_1771_,
                            v___y_1766_,
                        );
                    v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
                    lean_inc_n(v_a_1773_, 2);
                    lean_dec_ref(v___x_1772_);
                    v___x_1774_ = lean_unsigned_to_nat(1);
                    v___x_1775_ = lean_mk_empty_array_with_capacity(v___x_1774_);
                    lean_inc(v_declFVarId_1764_);
                    v___x_1776_ = lean_array_push(v___x_1775_, v_declFVarId_1764_);
                    v___x_1777_ = l_Lean_Meta_zetaDeltaFVars(
                        v_a_1773_,
                        v___x_1776_,
                        v___y_1765_,
                        v___y_1766_,
                        v___y_1767_,
                        v___y_1768_,
                    );
                    if lean_obj_tag(v___x_1777_) == 0 {
                        v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
                        lean_inc(v_a_1778_);
                        lean_dec_ref_known(v___x_1777_, 1);
                        v___x_1779_ = lean_expr_eqv(v_a_1778_, v_a_1773_);
                        if v___x_1779_ == 0 {
                            lean_dec(v_a_1773_);
                            lean_dec(v_declFVarId_1764_);
                            v___x_1780_ = l_Lean_MVarId_replaceTargetDefEq(
                                v_mvarId_1763_,
                                v_a_1778_,
                                v___y_1765_,
                                v___y_1766_,
                                v___y_1767_,
                                v___y_1768_,
                            );
                            return v___x_1780_;
                        } else {
                            lean_dec(v_a_1778_);
                            lean_dec(v_mvarId_1763_);
                            v___x_1781_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__1_once
                                ),
                                _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1,
                            );
                            v___x_1782_ = l_Lean_Expr_fvar___override(v_declFVarId_1764_);
                            v___x_1783_ = l_Lean_MessageData_ofExpr(v___x_1782_);
                            v___x_1784_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1784_, 0, v___x_1781_);
                            lean_ctor_set(v___x_1784_, 1, v___x_1783_);
                            v___x_1785_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__3_once
                                ),
                                _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3,
                            );
                            v___x_1786_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1786_, 0, v___x_1784_);
                            lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                            v___x_1787_ = l_Lean_indentExpr(v_a_1773_);
                            v___x_1788_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1788_, 0, v___x_1786_);
                            lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                            v___x_1789_ =
                                l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(
                                    v___x_1788_,
                                    v___y_1765_,
                                    v___y_1766_,
                                    v___y_1767_,
                                    v___y_1768_,
                                );
                            v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
                            v_isSharedCheck_1797_ = (!lean_is_exclusive(v___x_1789_)) as u8;
                            if v_isSharedCheck_1797_ == 0 {
                                v___x_1792_ = v___x_1789_;
                                v_isShared_1793_ = v_isSharedCheck_1797_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1790_);
                                lean_dec(v___x_1789_);
                                v___x_1792_ = lean_box(0);
                                v_isShared_1793_ = v_isSharedCheck_1797_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1773_);
                        lean_dec(v_declFVarId_1764_);
                        lean_dec(v_mvarId_1763_);
                        v_a_1798_ = lean_ctor_get(v___x_1777_, 0);
                        v_isSharedCheck_1805_ = (!lean_is_exclusive(v___x_1777_)) as u8;
                        if v_isSharedCheck_1805_ == 0 {
                            v___x_1800_ = v___x_1777_;
                            v_isShared_1801_ = v_isSharedCheck_1805_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1798_);
                            lean_dec(v___x_1777_);
                            v___x_1800_ = lean_box(0);
                            v_isShared_1801_ = v_isSharedCheck_1805_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declFVarId_1764_);
                    lean_dec(v_mvarId_1763_);
                    v_a_1806_ = lean_ctor_get(v___x_1770_, 0);
                    v_isSharedCheck_1813_ = (!lean_is_exclusive(v___x_1770_)) as u8;
                    if v_isSharedCheck_1813_ == 0 {
                        v___x_1808_ = v___x_1770_;
                        v_isShared_1809_ = v_isSharedCheck_1813_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1806_);
                        lean_dec(v___x_1770_);
                        v___x_1808_ = lean_box(0);
                        v_isShared_1809_ = v_isSharedCheck_1813_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1793_ == 0 {
                    v___x_1795_ = v___x_1792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
                    v___x_1795_ = v_reuseFailAlloc_1796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1795_;
            }
            3 => {
                if v_isShared_1801_ == 0 {
                    v___x_1803_ = v___x_1800_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
                    v___x_1803_ = v_reuseFailAlloc_1804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1803_;
            }
            5 => {
                if v_isShared_1809_ == 0 {
                    v___x_1811_ = v___x_1808_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
                    v___x_1811_ = v_reuseFailAlloc_1812_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(
    mut v_mvarId_1814_: *mut LeanObject,
    mut v_declFVarId_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1821_: *mut LeanObject = core::ptr::null_mut();
    v_res_1821_ = l_Lean_Meta_zetaDeltaTarget___lam__0(
        v_mvarId_1814_,
        v_declFVarId_1815_,
        v___y_1816_,
        v___y_1817_,
        v___y_1818_,
        v___y_1819_,
    );
    lean_dec(v___y_1819_);
    lean_dec_ref(v___y_1818_);
    lean_dec(v___y_1817_);
    lean_dec_ref(v___y_1816_);
    return v_res_1821_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaTarget(
    mut v_mvarId_1822_: *mut LeanObject,
    mut v_declFVarId_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_1822_);
    v___f_1829_ = lean_alloc_closure(
        l_Lean_Meta_zetaDeltaTarget___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_1829_, 0, v_mvarId_1822_);
    lean_closure_set(v___f_1829_, 1, v_declFVarId_1823_);
    v___x_1830_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(
        v_mvarId_1822_,
        v___f_1829_,
        v_a_1824_,
        v_a_1825_,
        v_a_1826_,
        v_a_1827_,
    );
    return v___x_1830_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaTarget___boxed(
    mut v_mvarId_1831_: *mut LeanObject,
    mut v_declFVarId_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1838_: *mut LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lean_Meta_zetaDeltaTarget(
        v_mvarId_1831_,
        v_declFVarId_1832_,
        v_a_1833_,
        v_a_1834_,
        v_a_1835_,
        v_a_1836_,
    );
    lean_dec(v_a_1836_);
    lean_dec_ref(v_a_1835_);
    lean_dec(v_a_1834_);
    lean_dec_ref(v_a_1833_);
    return v_res_1838_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaLocalDecl___lam__0(
    mut v_fvarId_1839_: *mut LeanObject,
    mut v_declFVarId_1840_: *mut LeanObject,
    mut v_mvarId_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1870_: u8 = 0;
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut v_a_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1878_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut v_a_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_1839_);
                v___x_1847_ = l_Lean_FVarId_getType___redArg(
                    v_fvarId_1839_,
                    v___y_1842_,
                    v___y_1844_,
                    v___y_1845_,
                );
                if lean_obj_tag(v___x_1847_) == 0 {
                    v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
                    lean_inc_n(v_a_1848_, 2);
                    lean_dec_ref_known(v___x_1847_, 1);
                    v___x_1849_ =
                        l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(
                            v_a_1848_,
                            v___y_1843_,
                        );
                    v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
                    lean_inc(v_a_1850_);
                    lean_dec_ref(v___x_1849_);
                    v___x_1851_ = lean_unsigned_to_nat(1);
                    v___x_1852_ = lean_mk_empty_array_with_capacity(v___x_1851_);
                    v___x_1853_ = lean_array_push(v___x_1852_, v_declFVarId_1840_);
                    v___x_1854_ = l_Lean_Meta_zetaDeltaFVars(
                        v_a_1850_,
                        v___x_1853_,
                        v___y_1842_,
                        v___y_1843_,
                        v___y_1844_,
                        v___y_1845_,
                    );
                    if lean_obj_tag(v___x_1854_) == 0 {
                        v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
                        lean_inc(v_a_1855_);
                        lean_dec_ref_known(v___x_1854_, 1);
                        v___x_1856_ = lean_expr_eqv(v_a_1855_, v_a_1848_);
                        if v___x_1856_ == 0 {
                            lean_dec(v_a_1848_);
                            v___x_1857_ = l_Lean_MVarId_replaceLocalDeclDefEq(
                                v_mvarId_1841_,
                                v_fvarId_1839_,
                                v_a_1855_,
                                v___y_1842_,
                                v___y_1843_,
                                v___y_1844_,
                                v___y_1845_,
                            );
                            return v___x_1857_;
                        } else {
                            lean_dec(v_a_1855_);
                            lean_dec(v_mvarId_1841_);
                            v___x_1858_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__1_once
                                ),
                                _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1,
                            );
                            v___x_1859_ = l_Lean_Expr_fvar___override(v_fvarId_1839_);
                            v___x_1860_ = l_Lean_MessageData_ofExpr(v___x_1859_);
                            v___x_1861_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1861_, 0, v___x_1858_);
                            lean_ctor_set(v___x_1861_, 1, v___x_1860_);
                            v___x_1862_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_unfoldTarget___lam__0___closed__3_once
                                ),
                                _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3,
                            );
                            v___x_1863_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1863_, 0, v___x_1861_);
                            lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                            v___x_1864_ = l_Lean_indentExpr(v_a_1848_);
                            v___x_1865_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1865_, 0, v___x_1863_);
                            lean_ctor_set(v___x_1865_, 1, v___x_1864_);
                            v___x_1866_ =
                                l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(
                                    v___x_1865_,
                                    v___y_1842_,
                                    v___y_1843_,
                                    v___y_1844_,
                                    v___y_1845_,
                                );
                            v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
                            v_isSharedCheck_1874_ = (!lean_is_exclusive(v___x_1866_)) as u8;
                            if v_isSharedCheck_1874_ == 0 {
                                v___x_1869_ = v___x_1866_;
                                v_isShared_1870_ = v_isSharedCheck_1874_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1867_);
                                lean_dec(v___x_1866_);
                                v___x_1869_ = lean_box(0);
                                v_isShared_1870_ = v_isSharedCheck_1874_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1848_);
                        lean_dec(v_mvarId_1841_);
                        lean_dec(v_fvarId_1839_);
                        v_a_1875_ = lean_ctor_get(v___x_1854_, 0);
                        v_isSharedCheck_1882_ = (!lean_is_exclusive(v___x_1854_)) as u8;
                        if v_isSharedCheck_1882_ == 0 {
                            v___x_1877_ = v___x_1854_;
                            v_isShared_1878_ = v_isSharedCheck_1882_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1875_);
                            lean_dec(v___x_1854_);
                            v___x_1877_ = lean_box(0);
                            v_isShared_1878_ = v_isSharedCheck_1882_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_1841_);
                    lean_dec(v_declFVarId_1840_);
                    lean_dec(v_fvarId_1839_);
                    v_a_1883_ = lean_ctor_get(v___x_1847_, 0);
                    v_isSharedCheck_1890_ = (!lean_is_exclusive(v___x_1847_)) as u8;
                    if v_isSharedCheck_1890_ == 0 {
                        v___x_1885_ = v___x_1847_;
                        v_isShared_1886_ = v_isSharedCheck_1890_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1883_);
                        lean_dec(v___x_1847_);
                        v___x_1885_ = lean_box(0);
                        v_isShared_1886_ = v_isSharedCheck_1890_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1870_ == 0 {
                    v___x_1872_ = v___x_1869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
                    v___x_1872_ = v_reuseFailAlloc_1873_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1872_;
            }
            3 => {
                if v_isShared_1878_ == 0 {
                    v___x_1880_ = v___x_1877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
                    v___x_1880_ = v_reuseFailAlloc_1881_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1880_;
            }
            5 => {
                if v_isShared_1886_ == 0 {
                    v___x_1888_ = v___x_1885_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
                    v___x_1888_ = v_reuseFailAlloc_1889_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(
    mut v_fvarId_1891_: *mut LeanObject,
    mut v_declFVarId_1892_: *mut LeanObject,
    mut v_mvarId_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
    mut v___y_1896_: *mut LeanObject,
    mut v___y_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1899_: *mut LeanObject = core::ptr::null_mut();
    v_res_1899_ = l_Lean_Meta_zetaDeltaLocalDecl___lam__0(
        v_fvarId_1891_,
        v_declFVarId_1892_,
        v_mvarId_1893_,
        v___y_1894_,
        v___y_1895_,
        v___y_1896_,
        v___y_1897_,
    );
    lean_dec(v___y_1897_);
    lean_dec_ref(v___y_1896_);
    lean_dec(v___y_1895_);
    lean_dec_ref(v___y_1894_);
    return v_res_1899_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaLocalDecl(
    mut v_mvarId_1900_: *mut LeanObject,
    mut v_fvarId_1901_: *mut LeanObject,
    mut v_declFVarId_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
    mut v_a_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_1900_);
    v___f_1908_ = lean_alloc_closure(
        l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_1908_, 0, v_fvarId_1901_);
    lean_closure_set(v___f_1908_, 1, v_declFVarId_1902_);
    lean_closure_set(v___f_1908_, 2, v_mvarId_1900_);
    v___x_1909_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(
        v_mvarId_1900_,
        v___f_1908_,
        v_a_1903_,
        v_a_1904_,
        v_a_1905_,
        v_a_1906_,
    );
    return v___x_1909_;
}
pub unsafe fn l_Lean_Meta_zetaDeltaLocalDecl___boxed(
    mut v_mvarId_1910_: *mut LeanObject,
    mut v_fvarId_1911_: *mut LeanObject,
    mut v_declFVarId_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
    mut v_a_1914_: *mut LeanObject,
    mut v_a_1915_: *mut LeanObject,
    mut v_a_1916_: *mut LeanObject,
    mut v_a_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1918_: *mut LeanObject = core::ptr::null_mut();
    v_res_1918_ = l_Lean_Meta_zetaDeltaLocalDecl(
        v_mvarId_1910_,
        v_fvarId_1911_,
        v_declFVarId_1912_,
        v_a_1913_,
        v_a_1914_,
        v_a_1915_,
        v_a_1916_,
    );
    lean_dec(v_a_1916_);
    lean_dec_ref(v_a_1915_);
    lean_dec(v_a_1914_);
    lean_dec_ref(v_a_1913_);
    return v_res_1918_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Unfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Unfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Unfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Unfold(builtin);
}
