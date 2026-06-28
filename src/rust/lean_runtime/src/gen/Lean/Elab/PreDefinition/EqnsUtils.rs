// Lean compiler output
// Module: Lean.Elab.PreDefinition.EqnsUtils
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.Split Lean.Meta.Tactic.Refl Lean.Meta.Tactic.Delta Lean.Meta.Tactic.SplitIf Lean.Meta.Tactic.Contradiction
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instBEqMVarId_beq, l_Lean_instInhabitedExpr, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEq;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_whnfR, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Contradiction::{
    initialize_Lean_Meta_Tactic_Contradiction, l_Lean_MVarId_contradictionCore,
    runtime_initialize_Lean_Meta_Tactic_Contradiction,
};
use crate::r#gen::Lean::Meta::Tactic::Delta::{
    initialize_Lean_Meta_Tactic_Delta, l_Lean_Meta_delta_x3f,
    runtime_initialize_Lean_Meta_Tactic_Delta,
};
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, l_Lean_MVarId_refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::l_Lean_MVarId_replaceTargetDefEq;
use crate::r#gen::Lean::Meta::Tactic::Split::{
    initialize_Lean_Meta_Tactic_Split, l_Lean_Meta_Split_simpMatchTarget,
    runtime_initialize_Lean_Meta_Tactic_Split,
};
use crate::r#gen::Lean::Meta::Tactic::SplitIf::{
    initialize_Lean_Meta_Tactic_SplitIf, l_Lean_Meta_simpIfTarget,
    runtime_initialize_Lean_Meta_Tactic_SplitIf,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType_x27, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_smartUnfolding;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_Eqns_tryURefl___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Eqns_tryURefl___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Eqns_tryURefl___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Eqns_tryURefl___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Eqns_tryURefl___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Eqns_tryURefl___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value: LeanStringObject<3> =
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
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [100, 101, 108, 116, 97, 76, 72, 83, 0],
    };
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value)
                as *mut LeanObject,
            6988479089575608528 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            101, 113, 117, 97, 108, 105, 116, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5_value) as *mut LeanObject;
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_value: LeanStringObject<27> =
    LeanStringObject {
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
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 100, 101, 108, 116, 97, 32, 114, 101,
            100, 117, 99, 101, 32, 108, 104, 115, 0,
        ],
    };
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Eqns_tryContradiction___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((16 as usize) << 1) | 1) as *mut LeanObject,
            65793 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Eqns_tryContradiction___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Eqns_tryContradiction___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2_value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 48, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 80, 114, 111, 106, 33, 73, 109, 112, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 111, 106, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Eqns_simpMatch_x3f(
    mut v_mvarId_566_: *mut LeanObject,
    mut v_a_567_: *mut LeanObject,
    mut v_a_568_: *mut LeanObject,
    mut v_a_569_: *mut LeanObject,
    mut v_a_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v___x_577_: u8 = 0;
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_586_: u8 = 0;
    let mut v_a_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_590_: u8 = 0;
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_566_);
                v___x_572_ = l_Lean_Meta_Split_simpMatchTarget(
                    v_mvarId_566_,
                    v_a_567_,
                    v_a_568_,
                    v_a_569_,
                    v_a_570_,
                );
                if lean_obj_tag(v___x_572_) == 0 {
                    v_a_573_ = lean_ctor_get(v___x_572_, 0);
                    v_isSharedCheck_586_ = (!lean_is_exclusive(v___x_572_)) as u8;
                    if v_isSharedCheck_586_ == 0 {
                        v___x_575_ = v___x_572_;
                        v_isShared_576_ = v_isSharedCheck_586_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_573_);
                        lean_dec(v___x_572_);
                        v___x_575_ = lean_box(0);
                        v_isShared_576_ = v_isSharedCheck_586_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_566_);
                    v_a_587_ = lean_ctor_get(v___x_572_, 0);
                    v_isSharedCheck_594_ = (!lean_is_exclusive(v___x_572_)) as u8;
                    if v_isSharedCheck_594_ == 0 {
                        v___x_589_ = v___x_572_;
                        v_isShared_590_ = v_isSharedCheck_594_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_587_);
                        lean_dec(v___x_572_);
                        v___x_589_ = lean_box(0);
                        v_isShared_590_ = v_isSharedCheck_594_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_577_ = l_Lean_instBEqMVarId_beq(v_mvarId_566_, v_a_573_);
                lean_dec(v_mvarId_566_);
                if v___x_577_ == 0 {
                    v___x_578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_578_, 0, v_a_573_);
                    if v_isShared_576_ == 0 {
                        lean_ctor_set(v___x_575_, 0, v___x_578_);
                        v___x_580_ = v___x_575_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
                        v___x_580_ = v_reuseFailAlloc_581_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_573_);
                    v___x_582_ = lean_box(0);
                    if v_isShared_576_ == 0 {
                        lean_ctor_set(v___x_575_, 0, v___x_582_);
                        v___x_584_ = v___x_575_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
                        v___x_584_ = v_reuseFailAlloc_585_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_580_;
            }
            3 => {
                return v___x_584_;
            }
            4 => {
                if v_isShared_590_ == 0 {
                    v___x_592_ = v___x_589_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
                    v___x_592_ = v_reuseFailAlloc_593_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Eqns_simpMatch_x3f___boxed(
    mut v_mvarId_595_: *mut LeanObject,
    mut v_a_596_: *mut LeanObject,
    mut v_a_597_: *mut LeanObject,
    mut v_a_598_: *mut LeanObject,
    mut v_a_599_: *mut LeanObject,
    mut v_a_600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_601_: *mut LeanObject = core::ptr::null_mut();
    v_res_601_ =
        l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
    lean_dec(v_a_599_);
    lean_dec_ref(v_a_598_);
    lean_dec(v_a_597_);
    lean_dec_ref(v_a_596_);
    return v_res_601_;
}
pub unsafe fn l_Lean_Elab_Eqns_simpIf_x3f(
    mut v_mvarId_602_: *mut LeanObject,
    mut v_useNewSemantics_603_: u8,
    mut v_a_604_: *mut LeanObject,
    mut v_a_605_: *mut LeanObject,
    mut v_a_606_: *mut LeanObject,
    mut v_a_607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_614_: u8 = 0;
    let mut v___x_615_: u8 = 0;
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_624_: u8 = 0;
    let mut v_a_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_628_: u8 = 0;
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_609_ = 1;
                lean_inc(v_mvarId_602_);
                v___x_610_ = l_Lean_Meta_simpIfTarget(
                    v_mvarId_602_,
                    v___x_609_,
                    v_useNewSemantics_603_,
                    v_a_604_,
                    v_a_605_,
                    v_a_606_,
                    v_a_607_,
                );
                if lean_obj_tag(v___x_610_) == 0 {
                    v_a_611_ = lean_ctor_get(v___x_610_, 0);
                    v_isSharedCheck_624_ = (!lean_is_exclusive(v___x_610_)) as u8;
                    if v_isSharedCheck_624_ == 0 {
                        v___x_613_ = v___x_610_;
                        v_isShared_614_ = v_isSharedCheck_624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_611_);
                        lean_dec(v___x_610_);
                        v___x_613_ = lean_box(0);
                        v_isShared_614_ = v_isSharedCheck_624_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_602_);
                    v_a_625_ = lean_ctor_get(v___x_610_, 0);
                    v_isSharedCheck_632_ = (!lean_is_exclusive(v___x_610_)) as u8;
                    if v_isSharedCheck_632_ == 0 {
                        v___x_627_ = v___x_610_;
                        v_isShared_628_ = v_isSharedCheck_632_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_625_);
                        lean_dec(v___x_610_);
                        v___x_627_ = lean_box(0);
                        v_isShared_628_ = v_isSharedCheck_632_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_615_ = l_Lean_instBEqMVarId_beq(v_mvarId_602_, v_a_611_);
                lean_dec(v_mvarId_602_);
                if v___x_615_ == 0 {
                    v___x_616_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_616_, 0, v_a_611_);
                    if v_isShared_614_ == 0 {
                        lean_ctor_set(v___x_613_, 0, v___x_616_);
                        v___x_618_ = v___x_613_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
                        v___x_618_ = v_reuseFailAlloc_619_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_611_);
                    v___x_620_ = lean_box(0);
                    if v_isShared_614_ == 0 {
                        lean_ctor_set(v___x_613_, 0, v___x_620_);
                        v___x_622_ = v___x_613_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
                        v___x_622_ = v_reuseFailAlloc_623_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_618_;
            }
            3 => {
                return v___x_622_;
            }
            4 => {
                if v_isShared_628_ == 0 {
                    v___x_630_ = v___x_627_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
                    v___x_630_ = v_reuseFailAlloc_631_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Eqns_simpIf_x3f___boxed(
    mut v_mvarId_633_: *mut LeanObject,
    mut v_useNewSemantics_634_: *mut LeanObject,
    mut v_a_635_: *mut LeanObject,
    mut v_a_636_: *mut LeanObject,
    mut v_a_637_: *mut LeanObject,
    mut v_a_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useNewSemantics_boxed_640_: u8 = 0;
    let mut v_res_641_: *mut LeanObject = core::ptr::null_mut();
    v_useNewSemantics_boxed_640_ = (lean_unbox(v_useNewSemantics_634_) as u8);
    v_res_641_ = l_Lean_Elab_Eqns_simpIf_x3f(
        v_mvarId_633_,
        v_useNewSemantics_boxed_640_,
        v_a_635_,
        v_a_636_,
        v_a_637_,
        v_a_638_,
    );
    lean_dec(v_a_638_);
    lean_dec_ref(v_a_637_);
    lean_dec(v_a_636_);
    lean_dec_ref(v_a_635_);
    return v_res_641_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(
    mut v_opts_642_: *mut LeanObject,
    mut v_opt_643_: *mut LeanObject,
) -> u8 {
    let mut v_name_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    v_name_644_ = lean_ctor_get(v_opt_643_, 0);
    v_defValue_645_ = lean_ctor_get(v_opt_643_, 1);
    v_map_646_ = lean_ctor_get(v_opts_642_, 0);
    v___x_647_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_646_,
            v_name_644_,
        );
    if lean_obj_tag(v___x_647_) == 0 {
        let mut v___x_648_: u8 = 0;
        v___x_648_ = (lean_unbox(v_defValue_645_) as u8);
        return v___x_648_;
    } else {
        let mut v_val_649_: *mut LeanObject = core::ptr::null_mut();
        v_val_649_ = lean_ctor_get(v___x_647_, 0);
        lean_inc(v_val_649_);
        lean_dec_ref_known(v___x_647_, 1);
        if lean_obj_tag(v_val_649_) == 1 {
            let mut v_v_650_: u8 = 0;
            v_v_650_ = lean_ctor_get_uint8(v_val_649_, 0 as u32);
            lean_dec_ref_known(v_val_649_, 0);
            return v_v_650_;
        } else {
            let mut v___x_651_: u8 = 0;
            lean_dec(v_val_649_);
            v___x_651_ = (lean_unbox(v_defValue_645_) as u8);
            return v___x_651_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(
    mut v_opts_652_: *mut LeanObject,
    mut v_opt_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_654_: u8 = 0;
    let mut v_r_655_: *mut LeanObject = core::ptr::null_mut();
    v_res_654_ =
        l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_opts_652_, v_opt_653_);
    lean_dec_ref(v_opt_653_);
    lean_dec_ref(v_opts_652_);
    v_r_655_ = lean_box((v_res_654_) as usize);
    return v_r_655_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(
    mut v_opts_656_: *mut LeanObject,
    mut v_opt_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    v_name_658_ = lean_ctor_get(v_opt_657_, 0);
    v_defValue_659_ = lean_ctor_get(v_opt_657_, 1);
    v_map_660_ = lean_ctor_get(v_opts_656_, 0);
    v___x_661_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_660_,
            v_name_658_,
        );
    if lean_obj_tag(v___x_661_) == 0 {
        lean_inc(v_defValue_659_);
        return v_defValue_659_;
    } else {
        let mut v_val_662_: *mut LeanObject = core::ptr::null_mut();
        v_val_662_ = lean_ctor_get(v___x_661_, 0);
        lean_inc(v_val_662_);
        lean_dec_ref_known(v___x_661_, 1);
        if lean_obj_tag(v_val_662_) == 3 {
            let mut v_v_663_: *mut LeanObject = core::ptr::null_mut();
            v_v_663_ = lean_ctor_get(v_val_662_, 0);
            lean_inc(v_v_663_);
            lean_dec_ref_known(v_val_662_, 1);
            return v_v_663_;
        } else {
            lean_dec(v_val_662_);
            lean_inc(v_defValue_659_);
            return v_defValue_659_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2___boxed(
    mut v_opts_664_: *mut LeanObject,
    mut v_opt_665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_666_: *mut LeanObject = core::ptr::null_mut();
    v_res_666_ =
        l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(v_opts_664_, v_opt_665_);
    lean_dec_ref(v_opt_665_);
    lean_dec_ref(v_opts_664_);
    return v_res_666_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(
    mut v_o_670_: *mut LeanObject,
    mut v_k_671_: *mut LeanObject,
    mut v_v_672_: u8,
) -> *mut LeanObject {
    let mut v_map_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_674_: u8 = 0;
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_673_ = lean_ctor_get(v_o_670_, 0);
                v_hasTrace_674_ = lean_ctor_get_uint8(
                    v_o_670_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_688_ = (!lean_is_exclusive(v_o_670_)) as u8;
                if v_isSharedCheck_688_ == 0 {
                    v___x_676_ = v_o_670_;
                    v_isShared_677_ = v_isSharedCheck_688_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_673_);
                    lean_dec(v_o_670_);
                    v___x_676_ = lean_box(0);
                    v_isShared_677_ = v_isSharedCheck_688_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_678_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_678_, 0 as u32, v_v_672_);
                lean_inc(v_k_671_);
                v___x_679_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_671_, v___x_678_, v_map_673_);
                if v_hasTrace_674_ == 0 {
                    v___x_680_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1;
                    v___x_681_ = l_Lean_Name_isPrefixOf(v___x_680_, v_k_671_);
                    lean_dec(v_k_671_);
                    if v_isShared_677_ == 0 {
                        lean_ctor_set(v___x_676_, 0, v___x_679_);
                        v___x_683_ = v___x_676_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_679_);
                        v___x_683_ = v_reuseFailAlloc_684_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_671_);
                    if v_isShared_677_ == 0 {
                        lean_ctor_set(v___x_676_, 0, v___x_679_);
                        v___x_686_ = v___x_676_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_679_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_687_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_674_,
                        );
                        v___x_686_ = v_reuseFailAlloc_687_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_683_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_681_,
                );
                return v___x_683_;
            }
            3 => {
                return v___x_686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___boxed(
    mut v_o_689_: *mut LeanObject,
    mut v_k_690_: *mut LeanObject,
    mut v_v_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_692_: u8 = 0;
    let mut v_res_693_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_692_ = (lean_unbox(v_v_691_) as u8);
    v_res_693_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(v_o_689_, v_k_690_, v_v_boxed_692_);
    return v_res_693_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(
    mut v_opts_694_: *mut LeanObject,
    mut v_opt_695_: *mut LeanObject,
    mut v_val_696_: u8,
) -> *mut LeanObject {
    let mut v_name_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v_name_697_ = lean_ctor_get(v_opt_695_, 0);
    lean_inc(v_name_697_);
    lean_dec_ref(v_opt_695_);
    v___x_698_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(v_opts_694_, v_name_697_, v_val_696_);
    return v___x_698_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(
    mut v_opts_699_: *mut LeanObject,
    mut v_opt_700_: *mut LeanObject,
    mut v_val_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_702_: u8 = 0;
    let mut v_res_703_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_702_ = (lean_unbox(v_val_701_) as u8);
    v_res_703_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(
        v_opts_699_,
        v_opt_700_,
        v_val_boxed_702_,
    );
    return v_res_703_;
}
pub unsafe fn _init_l_Lean_Elab_Eqns_tryURefl___closed__0() -> *mut LeanObject {
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_704_;
}
pub unsafe fn _init_l_Lean_Elab_Eqns_tryURefl___closed__1() -> *mut LeanObject {
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    v___x_705_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_tryURefl___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_tryURefl___closed__0_once),
        _init_l_Lean_Elab_Eqns_tryURefl___closed__0,
    );
    v___x_706_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_706_, 0, v___x_705_);
    return v___x_706_;
}
pub unsafe fn _init_l_Lean_Elab_Eqns_tryURefl___closed__2() -> *mut LeanObject {
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_707_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_tryURefl___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_tryURefl___closed__1_once),
        _init_l_Lean_Elab_Eqns_tryURefl___closed__1,
    );
    v___x_708_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_708_, 0, v___x_707_);
    lean_ctor_set(v___x_708_, 1, v___x_707_);
    return v___x_708_;
}
pub unsafe fn l_Lean_Elab_Eqns_tryURefl(
    mut v_mvarId_709_: *mut LeanObject,
    mut v_a_710_: *mut LeanObject,
    mut v_a_711_: *mut LeanObject,
    mut v_a_712_: *mut LeanObject,
    mut v_a_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_717_: u8 = 0;
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_734_: u8 = 0;
    let mut v_inheritedTraceOptions_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: u8 = 0;
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: u8 = 0;
    let mut v_fileName_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_755_: u8 = 0;
    let mut v_inheritedTraceOptions_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_764_: u8 = 0;
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_unused_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: u8 = 0;
    let mut v___x_773_: u8 = 0;
    let mut v___y_775_: u8 = 0;
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut v_unused_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_721_ = lean_st_ref_get(v_a_713_);
                v_fileName_722_ = lean_ctor_get(v_a_712_, 0);
                v_fileMap_723_ = lean_ctor_get(v_a_712_, 1);
                v_options_724_ = lean_ctor_get(v_a_712_, 2);
                v_currRecDepth_725_ = lean_ctor_get(v_a_712_, 3);
                v_ref_726_ = lean_ctor_get(v_a_712_, 5);
                v_currNamespace_727_ = lean_ctor_get(v_a_712_, 6);
                v_openDecls_728_ = lean_ctor_get(v_a_712_, 7);
                v_initHeartbeats_729_ = lean_ctor_get(v_a_712_, 8);
                v_maxHeartbeats_730_ = lean_ctor_get(v_a_712_, 9);
                v_quotContext_731_ = lean_ctor_get(v_a_712_, 10);
                v_currMacroScope_732_ = lean_ctor_get(v_a_712_, 11);
                v_cancelTk_x3f_733_ = lean_ctor_get(v_a_712_, 12);
                v_suppressElabErrors_734_ = lean_ctor_get_uint8(
                    v_a_712_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_735_ = lean_ctor_get(v_a_712_, 13);
                v_env_736_ = lean_ctor_get(v___x_721_, 0);
                lean_inc_ref(v_env_736_);
                lean_dec(v___x_721_);
                v___x_737_ = 1;
                v___x_738_ = l_Lean_Meta_smartUnfolding;
                v___x_739_ = 0;
                lean_inc_ref(v_options_724_);
                v___x_740_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(
                    v_options_724_,
                    v___x_738_,
                    v___x_739_,
                );
                v___x_741_ = l_Lean_diagnostics;
                v___x_742_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(
                    v___x_740_, v___x_741_,
                );
                v___x_796_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_736_);
                lean_dec_ref(v_env_736_);
                if v___x_796_ == 0 {
                    if v___x_742_ == 0 {
                        v_fileName_744_ = v_fileName_722_;
                        v_fileMap_745_ = v_fileMap_723_;
                        v_currRecDepth_746_ = v_currRecDepth_725_;
                        v_ref_747_ = v_ref_726_;
                        v_currNamespace_748_ = v_currNamespace_727_;
                        v_openDecls_749_ = v_openDecls_728_;
                        v_initHeartbeats_750_ = v_initHeartbeats_729_;
                        v_maxHeartbeats_751_ = v_maxHeartbeats_730_;
                        v_quotContext_752_ = v_quotContext_731_;
                        v_currMacroScope_753_ = v_currMacroScope_732_;
                        v_cancelTk_x3f_754_ = v_cancelTk_x3f_733_;
                        v_suppressElabErrors_755_ = v_suppressElabErrors_734_;
                        v_inheritedTraceOptions_756_ = v_inheritedTraceOptions_735_;
                        v___y_757_ = v_a_713_;
                        state = 2;
                        continue;
                    } else {
                        v___y_775_ = v___x_796_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_775_ = v___x_742_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                if v___y_717_ == 0 {
                    lean_dec_ref(v___y_716_);
                    v___x_718_ = lean_box((v___y_717_) as usize);
                    v___x_719_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_719_, 0, v___x_718_);
                    return v___x_719_;
                } else {
                    v___x_720_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_720_, 0, v___y_716_);
                    return v___x_720_;
                }
            }
            2 => {
                v___x_758_ = l_Lean_maxRecDepth;
                v___x_759_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(
                    v___x_740_, v___x_758_,
                );
                lean_inc_ref(v_inheritedTraceOptions_756_);
                lean_inc(v_cancelTk_x3f_754_);
                lean_inc(v_currMacroScope_753_);
                lean_inc(v_quotContext_752_);
                lean_inc(v_maxHeartbeats_751_);
                lean_inc(v_initHeartbeats_750_);
                lean_inc(v_openDecls_749_);
                lean_inc(v_currNamespace_748_);
                lean_inc(v_ref_747_);
                lean_inc(v_currRecDepth_746_);
                lean_inc_ref(v_fileMap_745_);
                lean_inc_ref(v_fileName_744_);
                v___x_760_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_760_, 0, v_fileName_744_);
                lean_ctor_set(v___x_760_, 1, v_fileMap_745_);
                lean_ctor_set(v___x_760_, 2, v___x_740_);
                lean_ctor_set(v___x_760_, 3, v_currRecDepth_746_);
                lean_ctor_set(v___x_760_, 4, v___x_759_);
                lean_ctor_set(v___x_760_, 5, v_ref_747_);
                lean_ctor_set(v___x_760_, 6, v_currNamespace_748_);
                lean_ctor_set(v___x_760_, 7, v_openDecls_749_);
                lean_ctor_set(v___x_760_, 8, v_initHeartbeats_750_);
                lean_ctor_set(v___x_760_, 9, v_maxHeartbeats_751_);
                lean_ctor_set(v___x_760_, 10, v_quotContext_752_);
                lean_ctor_set(v___x_760_, 11, v_currMacroScope_753_);
                lean_ctor_set(v___x_760_, 12, v_cancelTk_x3f_754_);
                lean_ctor_set(v___x_760_, 13, v_inheritedTraceOptions_756_);
                lean_ctor_set_uint8(
                    v___x_760_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_742_,
                );
                lean_ctor_set_uint8(
                    v___x_760_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_755_,
                );
                v___x_761_ = l_Lean_MVarId_refl(
                    v_mvarId_709_,
                    v___x_737_,
                    v_a_710_,
                    v_a_711_,
                    v___x_760_,
                    v___y_757_,
                );
                lean_dec_ref_known(v___x_760_, 14);
                if lean_obj_tag(v___x_761_) == 0 {
                    v_isSharedCheck_769_ = (!lean_is_exclusive(v___x_761_)) as u8;
                    if v_isSharedCheck_769_ == 0 {
                        v_unused_770_ = lean_ctor_get(v___x_761_, 0);
                        lean_dec(v_unused_770_);
                        v___x_763_ = v___x_761_;
                        v_isShared_764_ = v_isSharedCheck_769_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_761_);
                        v___x_763_ = lean_box(0);
                        v_isShared_764_ = v_isSharedCheck_769_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_771_ = lean_ctor_get(v___x_761_, 0);
                    lean_inc(v_a_771_);
                    lean_dec_ref_known(v___x_761_, 1);
                    v___x_772_ = l_Lean_Exception_isInterrupt(v_a_771_);
                    if v___x_772_ == 0 {
                        lean_inc(v_a_771_);
                        v___x_773_ = l_Lean_Exception_isRuntime(v_a_771_);
                        v___y_716_ = v_a_771_;
                        v___y_717_ = v___x_773_;
                        state = 1;
                        continue;
                    } else {
                        v___y_716_ = v_a_771_;
                        v___y_717_ = v___x_772_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_765_ = lean_box((v___x_737_) as usize);
                if v_isShared_764_ == 0 {
                    lean_ctor_set(v___x_763_, 0, v___x_765_);
                    v___x_767_ = v___x_763_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
                    v___x_767_ = v_reuseFailAlloc_768_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_767_;
            }
            5 => {
                if v___y_775_ == 0 {
                    v___x_776_ = lean_st_ref_take(v_a_713_);
                    v_env_777_ = lean_ctor_get(v___x_776_, 0);
                    v_nextMacroScope_778_ = lean_ctor_get(v___x_776_, 1);
                    v_ngen_779_ = lean_ctor_get(v___x_776_, 2);
                    v_auxDeclNGen_780_ = lean_ctor_get(v___x_776_, 3);
                    v_traceState_781_ = lean_ctor_get(v___x_776_, 4);
                    v_messages_782_ = lean_ctor_get(v___x_776_, 6);
                    v_infoState_783_ = lean_ctor_get(v___x_776_, 7);
                    v_snapshotTasks_784_ = lean_ctor_get(v___x_776_, 8);
                    v_isSharedCheck_794_ = (!lean_is_exclusive(v___x_776_)) as u8;
                    if v_isSharedCheck_794_ == 0 {
                        v_unused_795_ = lean_ctor_get(v___x_776_, 5);
                        lean_dec(v_unused_795_);
                        v___x_786_ = v___x_776_;
                        v_isShared_787_ = v_isSharedCheck_794_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_784_);
                        lean_inc(v_infoState_783_);
                        lean_inc(v_messages_782_);
                        lean_inc(v_traceState_781_);
                        lean_inc(v_auxDeclNGen_780_);
                        lean_inc(v_ngen_779_);
                        lean_inc(v_nextMacroScope_778_);
                        lean_inc(v_env_777_);
                        lean_dec(v___x_776_);
                        v___x_786_ = lean_box(0);
                        v_isShared_787_ = v_isSharedCheck_794_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_fileName_744_ = v_fileName_722_;
                    v_fileMap_745_ = v_fileMap_723_;
                    v_currRecDepth_746_ = v_currRecDepth_725_;
                    v_ref_747_ = v_ref_726_;
                    v_currNamespace_748_ = v_currNamespace_727_;
                    v_openDecls_749_ = v_openDecls_728_;
                    v_initHeartbeats_750_ = v_initHeartbeats_729_;
                    v_maxHeartbeats_751_ = v_maxHeartbeats_730_;
                    v_quotContext_752_ = v_quotContext_731_;
                    v_currMacroScope_753_ = v_currMacroScope_732_;
                    v_cancelTk_x3f_754_ = v_cancelTk_x3f_733_;
                    v_suppressElabErrors_755_ = v_suppressElabErrors_734_;
                    v_inheritedTraceOptions_756_ = v_inheritedTraceOptions_735_;
                    v___y_757_ = v_a_713_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_788_ = l_Lean_Kernel_enableDiag(v_env_777_, v___x_742_);
                v___x_789_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_tryURefl___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_tryURefl___closed__2_once),
                    _init_l_Lean_Elab_Eqns_tryURefl___closed__2,
                );
                if v_isShared_787_ == 0 {
                    lean_ctor_set(v___x_786_, 5, v___x_789_);
                    lean_ctor_set(v___x_786_, 0, v___x_788_);
                    v___x_791_ = v___x_786_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_788_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 1, v_nextMacroScope_778_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 2, v_ngen_779_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 3, v_auxDeclNGen_780_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 4, v_traceState_781_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 5, v___x_789_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 6, v_messages_782_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 7, v_infoState_783_);
                    lean_ctor_set(v_reuseFailAlloc_793_, 8, v_snapshotTasks_784_);
                    v___x_791_ = v_reuseFailAlloc_793_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_792_ = lean_st_ref_set(v_a_713_, v___x_791_);
                v_fileName_744_ = v_fileName_722_;
                v_fileMap_745_ = v_fileMap_723_;
                v_currRecDepth_746_ = v_currRecDepth_725_;
                v_ref_747_ = v_ref_726_;
                v_currNamespace_748_ = v_currNamespace_727_;
                v_openDecls_749_ = v_openDecls_728_;
                v_initHeartbeats_750_ = v_initHeartbeats_729_;
                v_maxHeartbeats_751_ = v_maxHeartbeats_730_;
                v_quotContext_752_ = v_quotContext_731_;
                v_currMacroScope_753_ = v_currMacroScope_732_;
                v_cancelTk_x3f_754_ = v_cancelTk_x3f_733_;
                v_suppressElabErrors_755_ = v_suppressElabErrors_734_;
                v_inheritedTraceOptions_756_ = v_inheritedTraceOptions_735_;
                v___y_757_ = v_a_713_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Eqns_tryURefl___boxed(
    mut v_mvarId_797_: *mut LeanObject,
    mut v_a_798_: *mut LeanObject,
    mut v_a_799_: *mut LeanObject,
    mut v_a_800_: *mut LeanObject,
    mut v_a_801_: *mut LeanObject,
    mut v_a_802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_803_: *mut LeanObject = core::ptr::null_mut();
    v_res_803_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
    lean_dec(v_a_801_);
    lean_dec_ref(v_a_800_);
    lean_dec(v_a_799_);
    lean_dec_ref(v_a_798_);
    return v_res_803_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(
    mut v_mvarId_804_: *mut LeanObject,
    mut v_x_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_815_: u8 = 0;
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_819_: u8 = 0;
    let mut v_a_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_811_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_804_,
                    v_x_805_,
                    v___y_806_,
                    v___y_807_,
                    v___y_808_,
                    v___y_809_,
                );
                if lean_obj_tag(v___x_811_) == 0 {
                    v_a_812_ = lean_ctor_get(v___x_811_, 0);
                    v_isSharedCheck_819_ = (!lean_is_exclusive(v___x_811_)) as u8;
                    if v_isSharedCheck_819_ == 0 {
                        v___x_814_ = v___x_811_;
                        v_isShared_815_ = v_isSharedCheck_819_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_812_);
                        lean_dec(v___x_811_);
                        v___x_814_ = lean_box(0);
                        v_isShared_815_ = v_isSharedCheck_819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_820_ = lean_ctor_get(v___x_811_, 0);
                    v_isSharedCheck_827_ = (!lean_is_exclusive(v___x_811_)) as u8;
                    if v_isSharedCheck_827_ == 0 {
                        v___x_822_ = v___x_811_;
                        v_isShared_823_ = v_isSharedCheck_827_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_820_);
                        lean_dec(v___x_811_);
                        v___x_822_ = lean_box(0);
                        v_isShared_823_ = v_isSharedCheck_827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_815_ == 0 {
                    v___x_817_ = v___x_814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
                    v___x_817_ = v_reuseFailAlloc_818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_817_;
            }
            3 => {
                if v_isShared_823_ == 0 {
                    v___x_825_ = v___x_822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
                    v___x_825_ = v_reuseFailAlloc_826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg___boxed(
    mut v_mvarId_828_: *mut LeanObject,
    mut v_x_829_: *mut LeanObject,
    mut v___y_830_: *mut LeanObject,
    mut v___y_831_: *mut LeanObject,
    mut v___y_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v___y_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_835_: *mut LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(
        v_mvarId_828_,
        v_x_829_,
        v___y_830_,
        v___y_831_,
        v___y_832_,
        v___y_833_,
    );
    lean_dec(v___y_833_);
    lean_dec_ref(v___y_832_);
    lean_dec(v___y_831_);
    lean_dec_ref(v___y_830_);
    return v_res_835_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(
    mut v_00_u03b1_836_: *mut LeanObject,
    mut v_mvarId_837_: *mut LeanObject,
    mut v_x_838_: *mut LeanObject,
    mut v___y_839_: *mut LeanObject,
    mut v___y_840_: *mut LeanObject,
    mut v___y_841_: *mut LeanObject,
    mut v___y_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    v___x_844_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(
        v_mvarId_837_,
        v_x_838_,
        v___y_839_,
        v___y_840_,
        v___y_841_,
        v___y_842_,
    );
    return v___x_844_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___boxed(
    mut v_00_u03b1_845_: *mut LeanObject,
    mut v_mvarId_846_: *mut LeanObject,
    mut v_x_847_: *mut LeanObject,
    mut v___y_848_: *mut LeanObject,
    mut v___y_849_: *mut LeanObject,
    mut v___y_850_: *mut LeanObject,
    mut v___y_851_: *mut LeanObject,
    mut v___y_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_853_: *mut LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(
        v_00_u03b1_845_,
        v_mvarId_846_,
        v_x_847_,
        v___y_848_,
        v___y_849_,
        v___y_850_,
        v___y_851_,
    );
    lean_dec(v___y_851_);
    lean_dec_ref(v___y_850_);
    lean_dec(v___y_849_);
    lean_dec_ref(v___y_848_);
    return v_res_853_;
}
pub unsafe fn l_Lean_Elab_Eqns_deltaLHS___lam__0(
    mut v___x_854_: u8,
    mut v_x_855_: *mut LeanObject,
) -> u8 {
    return v___x_854_;
}
pub unsafe fn l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(
    mut v___x_856_: *mut LeanObject,
    mut v_x_857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1020__boxed_858_: u8 = 0;
    let mut v_res_859_: u8 = 0;
    let mut v_r_860_: *mut LeanObject = core::ptr::null_mut();
    v___x_1020__boxed_858_ = (lean_unbox(v___x_856_) as u8);
    v_res_859_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_1020__boxed_858_, v_x_857_);
    lean_dec(v_x_857_);
    v_r_860_ = lean_box((v_res_859_) as usize);
    return v_r_860_;
}
pub unsafe fn _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6() -> *mut LeanObject {
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5;
    v___x_871_ = l_Lean_MessageData_ofFormat(v___x_870_);
    return v___x_871_;
}
pub unsafe fn _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7() -> *mut LeanObject {
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    v___x_872_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_once),
        _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6,
    );
    v___x_873_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_873_, 0, v___x_872_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10() -> *mut LeanObject {
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    v___x_877_ = l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9;
    v___x_878_ = l_Lean_MessageData_ofFormat(v___x_877_);
    return v___x_878_;
}
pub unsafe fn _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11() -> *mut LeanObject {
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    v___x_879_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10_once),
        _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10,
    );
    v___x_880_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_880_, 0, v___x_879_);
    return v___x_880_;
}
pub unsafe fn l_Lean_Elab_Eqns_deltaLHS___lam__1(
    mut v_mvarId_881_: *mut LeanObject,
    mut v___y_882_: *mut LeanObject,
    mut v___y_883_: *mut LeanObject,
    mut v___y_884_: *mut LeanObject,
    mut v___y_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: u8 = 0;
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: u8 = 0;
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_910_: u8 = 0;
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_914_: u8 = 0;
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_921_: u8 = 0;
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_925_: u8 = 0;
    let mut v_a_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_881_);
                v___x_887_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_881_,
                    v___y_882_,
                    v___y_883_,
                    v___y_884_,
                    v___y_885_,
                );
                if lean_obj_tag(v___x_887_) == 0 {
                    v_a_888_ = lean_ctor_get(v___x_887_, 0);
                    lean_inc(v_a_888_);
                    lean_dec_ref_known(v___x_887_, 1);
                    v___x_889_ = l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1;
                    v___x_890_ = lean_unsigned_to_nat(3);
                    v___x_891_ = l_Lean_Expr_isAppOfArity(v_a_888_, v___x_889_, v___x_890_);
                    if v___x_891_ == 0 {
                        lean_dec(v_a_888_);
                        v___x_892_ = l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3;
                        v___x_893_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_once
                            ),
                            _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7,
                        );
                        v___x_894_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_892_,
                            v_mvarId_881_,
                            v___x_893_,
                            v___y_882_,
                            v___y_883_,
                            v___y_884_,
                            v___y_885_,
                        );
                        return v___x_894_;
                    } else {
                        v___x_895_ = lean_box((v___x_891_) as usize);
                        v___f_896_ = lean_alloc_closure(
                            l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        lean_closure_set(v___f_896_, 0, v___x_895_);
                        v___x_897_ = l_Lean_Expr_appFn_x21(v_a_888_);
                        v___x_898_ = l_Lean_Expr_appArg_x21(v___x_897_);
                        lean_dec_ref(v___x_897_);
                        v___x_899_ = 0;
                        v___x_900_ = l_Lean_Meta_delta_x3f(
                            v___x_898_, v___f_896_, v___x_899_, v___y_884_, v___y_885_,
                        );
                        if lean_obj_tag(v___x_900_) == 0 {
                            v_a_901_ = lean_ctor_get(v___x_900_, 0);
                            lean_inc(v_a_901_);
                            lean_dec_ref_known(v___x_900_, 1);
                            if lean_obj_tag(v_a_901_) == 1 {
                                v_val_902_ = lean_ctor_get(v_a_901_, 0);
                                lean_inc(v_val_902_);
                                lean_dec_ref_known(v_a_901_, 1);
                                v___x_903_ = l_Lean_Expr_appArg_x21(v_a_888_);
                                lean_dec(v_a_888_);
                                v___x_904_ = l_Lean_Meta_mkEq(
                                    v_val_902_, v___x_903_, v___y_882_, v___y_883_, v___y_884_,
                                    v___y_885_,
                                );
                                if lean_obj_tag(v___x_904_) == 0 {
                                    v_a_905_ = lean_ctor_get(v___x_904_, 0);
                                    lean_inc(v_a_905_);
                                    lean_dec_ref_known(v___x_904_, 1);
                                    v___x_906_ = l_Lean_MVarId_replaceTargetDefEq(
                                        v_mvarId_881_,
                                        v_a_905_,
                                        v___y_882_,
                                        v___y_883_,
                                        v___y_884_,
                                        v___y_885_,
                                    );
                                    return v___x_906_;
                                } else {
                                    lean_dec(v_mvarId_881_);
                                    v_a_907_ = lean_ctor_get(v___x_904_, 0);
                                    v_isSharedCheck_914_ = (!lean_is_exclusive(v___x_904_)) as u8;
                                    if v_isSharedCheck_914_ == 0 {
                                        v___x_909_ = v___x_904_;
                                        v_isShared_910_ = v_isSharedCheck_914_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_907_);
                                        lean_dec(v___x_904_);
                                        v___x_909_ = lean_box(0);
                                        v_isShared_910_ = v_isSharedCheck_914_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_901_);
                                lean_dec(v_a_888_);
                                v___x_915_ = l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3;
                                v___x_916_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11_once
                                    ),
                                    _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11,
                                );
                                v___x_917_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_915_,
                                    v_mvarId_881_,
                                    v___x_916_,
                                    v___y_882_,
                                    v___y_883_,
                                    v___y_884_,
                                    v___y_885_,
                                );
                                return v___x_917_;
                            }
                        } else {
                            lean_dec(v_a_888_);
                            lean_dec(v_mvarId_881_);
                            v_a_918_ = lean_ctor_get(v___x_900_, 0);
                            v_isSharedCheck_925_ = (!lean_is_exclusive(v___x_900_)) as u8;
                            if v_isSharedCheck_925_ == 0 {
                                v___x_920_ = v___x_900_;
                                v_isShared_921_ = v_isSharedCheck_925_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_918_);
                                lean_dec(v___x_900_);
                                v___x_920_ = lean_box(0);
                                v_isShared_921_ = v_isSharedCheck_925_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_mvarId_881_);
                    v_a_926_ = lean_ctor_get(v___x_887_, 0);
                    v_isSharedCheck_933_ = (!lean_is_exclusive(v___x_887_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_928_ = v___x_887_;
                        v_isShared_929_ = v_isSharedCheck_933_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_926_);
                        lean_dec(v___x_887_);
                        v___x_928_ = lean_box(0);
                        v_isShared_929_ = v_isSharedCheck_933_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_910_ == 0 {
                    v___x_912_ = v___x_909_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
                    v___x_912_ = v_reuseFailAlloc_913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_912_;
            }
            3 => {
                if v_isShared_921_ == 0 {
                    v___x_923_ = v___x_920_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
                    v___x_923_ = v_reuseFailAlloc_924_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_923_;
            }
            5 => {
                if v_isShared_929_ == 0 {
                    v___x_931_ = v___x_928_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
                    v___x_931_ = v_reuseFailAlloc_932_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(
    mut v_mvarId_934_: *mut LeanObject,
    mut v___y_935_: *mut LeanObject,
    mut v___y_936_: *mut LeanObject,
    mut v___y_937_: *mut LeanObject,
    mut v___y_938_: *mut LeanObject,
    mut v___y_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_940_: *mut LeanObject = core::ptr::null_mut();
    v_res_940_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(
        v_mvarId_934_,
        v___y_935_,
        v___y_936_,
        v___y_937_,
        v___y_938_,
    );
    lean_dec(v___y_938_);
    lean_dec_ref(v___y_937_);
    lean_dec(v___y_936_);
    lean_dec_ref(v___y_935_);
    return v_res_940_;
}
pub unsafe fn l_Lean_Elab_Eqns_deltaLHS(
    mut v_mvarId_941_: *mut LeanObject,
    mut v_a_942_: *mut LeanObject,
    mut v_a_943_: *mut LeanObject,
    mut v_a_944_: *mut LeanObject,
    mut v_a_945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_941_);
    v___f_947_ = lean_alloc_closure(
        l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_947_, 0, v_mvarId_941_);
    v___x_948_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(
        v_mvarId_941_,
        v___f_947_,
        v_a_942_,
        v_a_943_,
        v_a_944_,
        v_a_945_,
    );
    return v___x_948_;
}
pub unsafe fn l_Lean_Elab_Eqns_deltaLHS___boxed(
    mut v_mvarId_949_: *mut LeanObject,
    mut v_a_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
    mut v_a_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_955_: *mut LeanObject = core::ptr::null_mut();
    v_res_955_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
    lean_dec(v_a_953_);
    lean_dec_ref(v_a_952_);
    lean_dec(v_a_951_);
    lean_dec_ref(v_a_950_);
    return v_res_955_;
}
pub unsafe fn l_Lean_Elab_Eqns_tryContradiction(
    mut v_mvarId_959_: *mut LeanObject,
    mut v_a_960_: *mut LeanObject,
    mut v_a_961_: *mut LeanObject,
    mut v_a_962_: *mut LeanObject,
    mut v_a_963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    v___x_965_ = l_Lean_Elab_Eqns_tryContradiction___closed__0;
    v___x_966_ = l_Lean_MVarId_contradictionCore(
        v_mvarId_959_,
        v___x_965_,
        v_a_960_,
        v_a_961_,
        v_a_962_,
        v_a_963_,
    );
    return v___x_966_;
}
pub unsafe fn l_Lean_Elab_Eqns_tryContradiction___boxed(
    mut v_mvarId_967_: *mut LeanObject,
    mut v_a_968_: *mut LeanObject,
    mut v_a_969_: *mut LeanObject,
    mut v_a_970_: *mut LeanObject,
    mut v_a_971_: *mut LeanObject,
    mut v_a_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_973_: *mut LeanObject = core::ptr::null_mut();
    v_res_973_ =
        l_Lean_Elab_Eqns_tryContradiction(v_mvarId_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
    lean_dec(v_a_971_);
    lean_dec_ref(v_a_970_);
    lean_dec(v_a_969_);
    lean_dec_ref(v_a_968_);
    return v_res_973_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(
    mut v_msg_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    v___x_975_ = l_Lean_instInhabitedExpr;
    v___x_976_ = lean_panic_fn_borrowed(v___x_975_, v_msg_974_);
    return v___x_976_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0()
-> *mut LeanObject {
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_978_: *mut LeanObject = core::ptr::null_mut();
    v___x_977_ = lean_box(0);
    v_dummy_978_ = l_Lean_Expr_sort___override(v___x_977_);
    return v_dummy_978_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4()
-> *mut LeanObject {
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    v___x_982_ =
        l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3;
    v___x_983_ = lean_unsigned_to_nat(18);
    v___x_984_ = lean_unsigned_to_nat(1887);
    v___x_985_ =
        l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2;
    v___x_986_ =
        l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1;
    v___x_987_ =
        l_mkPanicMessageWithDecl(v___x_986_, v___x_985_, v___x_984_, v___x_983_, v___x_982_);
    return v___x_987_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(
    mut v_e_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
    mut v_a_990_: *mut LeanObject,
    mut v_a_991_: *mut LeanObject,
    mut v_a_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v___y_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: usize = 0;
    let mut v___x_1019_: usize = 0;
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_994_ = l_Lean_Meta_whnfR(v_e_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
                if lean_obj_tag(v___x_994_) == 0 {
                    v_a_995_ = lean_ctor_get(v___x_994_, 0);
                    lean_inc(v_a_995_);
                    v___x_996_ = l_Lean_Expr_getAppFn(v_a_995_);
                    if lean_obj_tag(v___x_996_) == 11 {
                        lean_dec_ref_known(v___x_994_, 1);
                        v_struct_997_ = lean_ctor_get(v___x_996_, 2);
                        lean_inc_ref(v_struct_997_);
                        v___x_998_ =
                            l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(
                                v_struct_997_,
                                v_a_989_,
                                v_a_990_,
                                v_a_991_,
                                v_a_992_,
                            );
                        if lean_obj_tag(v___x_998_) == 0 {
                            v_a_999_ = lean_ctor_get(v___x_998_, 0);
                            v_isSharedCheck_1024_ = (!lean_is_exclusive(v___x_998_)) as u8;
                            if v_isSharedCheck_1024_ == 0 {
                                v___x_1001_ = v___x_998_;
                                v_isShared_1002_ = v_isSharedCheck_1024_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_999_);
                                lean_dec(v___x_998_);
                                v___x_1001_ = lean_box(0);
                                v_isShared_1002_ = v_isSharedCheck_1024_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v___x_996_, 3);
                            lean_dec(v_a_995_);
                            return v___x_998_;
                        }
                    } else {
                        lean_dec_ref(v___x_996_);
                        lean_dec(v_a_995_);
                        return v___x_994_;
                    }
                } else {
                    return v___x_994_;
                }
            }
            1 => {
                if lean_obj_tag(v___x_996_) == 11 {
                    v_typeName_1015_ = lean_ctor_get(v___x_996_, 0);
                    lean_inc(v_typeName_1015_);
                    v_idx_1016_ = lean_ctor_get(v___x_996_, 1);
                    lean_inc(v_idx_1016_);
                    v_struct_1017_ = lean_ctor_get(v___x_996_, 2);
                    lean_inc_ref(v_struct_1017_);
                    v___x_1018_ = lean_ptr_addr(v_struct_1017_);
                    lean_dec_ref(v_struct_1017_);
                    v___x_1019_ = lean_ptr_addr(v_a_999_);
                    v___x_1020_ = lean_usize_dec_eq(v___x_1018_, v___x_1019_);
                    if v___x_1020_ == 0 {
                        lean_dec_ref_known(v___x_996_, 3);
                        v___x_1021_ =
                            l_Lean_Expr_proj___override(v_typeName_1015_, v_idx_1016_, v_a_999_);
                        v___y_1004_ = v___x_1021_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_idx_1016_);
                        lean_dec(v_typeName_1015_);
                        lean_dec(v_a_999_);
                        v___y_1004_ = v___x_996_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_999_);
                    lean_dec_ref_known(v___x_996_, 3);
                    v___x_1022_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4);
                    v___x_1023_ = l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(v___x_1022_);
                    v___y_1004_ = v___x_1023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_dummy_1005_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once), _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0);
                v_nargs_1006_ = l_Lean_Expr_getAppNumArgs(v_a_995_);
                lean_inc(v_nargs_1006_);
                v___x_1007_ = lean_mk_array(v_nargs_1006_, v_dummy_1005_);
                v___x_1008_ = lean_unsigned_to_nat(1);
                v___x_1009_ = lean_nat_sub(v_nargs_1006_, v___x_1008_);
                lean_dec(v_nargs_1006_);
                v___x_1010_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_995_,
                    v___x_1007_,
                    v___x_1009_,
                );
                v___x_1011_ = l_Lean_mkAppN(v___y_1004_, v___x_1010_);
                lean_dec_ref(v___x_1010_);
                if v_isShared_1002_ == 0 {
                    lean_ctor_set(v___x_1001_, 0, v___x_1011_);
                    v___x_1013_ = v___x_1001_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
                    v___x_1013_ = v_reuseFailAlloc_1014_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(
    mut v_e_1025_: *mut LeanObject,
    mut v_a_1026_: *mut LeanObject,
    mut v_a_1027_: *mut LeanObject,
    mut v_a_1028_: *mut LeanObject,
    mut v_a_1029_: *mut LeanObject,
    mut v_a_1030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1031_: *mut LeanObject = core::ptr::null_mut();
    v_res_1031_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(
        v_e_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_,
    );
    lean_dec(v_a_1029_);
    lean_dec_ref(v_a_1028_);
    lean_dec(v_a_1027_);
    lean_dec_ref(v_a_1026_);
    return v_res_1031_;
}
pub unsafe fn l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(
    mut v_mvarId_1032_: *mut LeanObject,
    mut v___y_1033_: *mut LeanObject,
    mut v___y_1034_: *mut LeanObject,
    mut v___y_1035_: *mut LeanObject,
    mut v___y_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1042_: u8 = 0;
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v___x_1057_: u8 = 0;
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1065_: u8 = 0;
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1070_: u8 = 0;
    let mut v_a_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1078_: u8 = 0;
    let mut v_a_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1082_: u8 = 0;
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1086_: u8 = 0;
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1091_: u8 = 0;
    let mut v_a_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v_isSharedCheck_1100_: u8 = 0;
    let mut v_a_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_1032_);
                v___x_1038_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_1032_,
                    v___y_1033_,
                    v___y_1034_,
                    v___y_1035_,
                    v___y_1036_,
                );
                if lean_obj_tag(v___x_1038_) == 0 {
                    v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
                    v_isSharedCheck_1100_ = (!lean_is_exclusive(v___x_1038_)) as u8;
                    if v_isSharedCheck_1100_ == 0 {
                        v___x_1041_ = v___x_1038_;
                        v_isShared_1042_ = v_isSharedCheck_1100_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1039_);
                        lean_dec(v___x_1038_);
                        v___x_1041_ = lean_box(0);
                        v_isShared_1042_ = v_isSharedCheck_1100_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_1032_);
                    v_a_1101_ = lean_ctor_get(v___x_1038_, 0);
                    v_isSharedCheck_1108_ = (!lean_is_exclusive(v___x_1038_)) as u8;
                    if v_isSharedCheck_1108_ == 0 {
                        v___x_1103_ = v___x_1038_;
                        v_isShared_1104_ = v_isSharedCheck_1108_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_1101_);
                        lean_dec(v___x_1038_);
                        v___x_1103_ = lean_box(0);
                        v_isShared_1104_ = v_isSharedCheck_1108_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1043_ = l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1;
                v___x_1044_ = lean_unsigned_to_nat(3);
                v___x_1045_ = l_Lean_Expr_isAppOfArity(v_a_1039_, v___x_1043_, v___x_1044_);
                if v___x_1045_ == 0 {
                    lean_dec(v_a_1039_);
                    lean_dec(v_mvarId_1032_);
                    v___x_1046_ = lean_box(0);
                    if v_isShared_1042_ == 0 {
                        lean_ctor_set(v___x_1041_, 0, v___x_1046_);
                        v___x_1048_ = v___x_1041_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
                        v___x_1048_ = v_reuseFailAlloc_1049_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1041_);
                    v___x_1050_ = l_Lean_Expr_appFn_x21(v_a_1039_);
                    v___x_1051_ = l_Lean_Expr_appArg_x21(v___x_1050_);
                    lean_dec_ref(v___x_1050_);
                    lean_inc_ref(v___x_1051_);
                    v___x_1052_ =
                        l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(
                            v___x_1051_,
                            v___y_1033_,
                            v___y_1034_,
                            v___y_1035_,
                            v___y_1036_,
                        );
                    if lean_obj_tag(v___x_1052_) == 0 {
                        v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
                        v_isSharedCheck_1091_ = (!lean_is_exclusive(v___x_1052_)) as u8;
                        if v_isSharedCheck_1091_ == 0 {
                            v___x_1055_ = v___x_1052_;
                            v_isShared_1056_ = v_isSharedCheck_1091_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1053_);
                            lean_dec(v___x_1052_);
                            v___x_1055_ = lean_box(0);
                            v_isShared_1056_ = v_isSharedCheck_1091_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1051_);
                        lean_dec(v_a_1039_);
                        lean_dec(v_mvarId_1032_);
                        v_a_1092_ = lean_ctor_get(v___x_1052_, 0);
                        v_isSharedCheck_1099_ = (!lean_is_exclusive(v___x_1052_)) as u8;
                        if v_isSharedCheck_1099_ == 0 {
                            v___x_1094_ = v___x_1052_;
                            v_isShared_1095_ = v_isSharedCheck_1099_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_1092_);
                            lean_dec(v___x_1052_);
                            v___x_1094_ = lean_box(0);
                            v_isShared_1095_ = v_isSharedCheck_1099_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1048_;
            }
            3 => {
                v___x_1057_ = lean_expr_eqv(v_a_1053_, v___x_1051_);
                lean_dec_ref(v___x_1051_);
                if v___x_1057_ == 0 {
                    lean_del_object(v___x_1055_);
                    v___x_1058_ = l_Lean_Expr_appArg_x21(v_a_1039_);
                    lean_dec(v_a_1039_);
                    v___x_1059_ = l_Lean_Meta_mkEq(
                        v_a_1053_,
                        v___x_1058_,
                        v___y_1033_,
                        v___y_1034_,
                        v___y_1035_,
                        v___y_1036_,
                    );
                    if lean_obj_tag(v___x_1059_) == 0 {
                        v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
                        lean_inc(v_a_1060_);
                        lean_dec_ref_known(v___x_1059_, 1);
                        v___x_1061_ = l_Lean_MVarId_replaceTargetDefEq(
                            v_mvarId_1032_,
                            v_a_1060_,
                            v___y_1033_,
                            v___y_1034_,
                            v___y_1035_,
                            v___y_1036_,
                        );
                        if lean_obj_tag(v___x_1061_) == 0 {
                            v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
                            v_isSharedCheck_1070_ = (!lean_is_exclusive(v___x_1061_)) as u8;
                            if v_isSharedCheck_1070_ == 0 {
                                v___x_1064_ = v___x_1061_;
                                v_isShared_1065_ = v_isSharedCheck_1070_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1062_);
                                lean_dec(v___x_1061_);
                                v___x_1064_ = lean_box(0);
                                v_isShared_1065_ = v_isSharedCheck_1070_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_1071_ = lean_ctor_get(v___x_1061_, 0);
                            v_isSharedCheck_1078_ = (!lean_is_exclusive(v___x_1061_)) as u8;
                            if v_isSharedCheck_1078_ == 0 {
                                v___x_1073_ = v___x_1061_;
                                v_isShared_1074_ = v_isSharedCheck_1078_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1071_);
                                lean_dec(v___x_1061_);
                                v___x_1073_ = lean_box(0);
                                v_isShared_1074_ = v_isSharedCheck_1078_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_mvarId_1032_);
                        v_a_1079_ = lean_ctor_get(v___x_1059_, 0);
                        v_isSharedCheck_1086_ = (!lean_is_exclusive(v___x_1059_)) as u8;
                        if v_isSharedCheck_1086_ == 0 {
                            v___x_1081_ = v___x_1059_;
                            v_isShared_1082_ = v_isSharedCheck_1086_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1079_);
                            lean_dec(v___x_1059_);
                            v___x_1081_ = lean_box(0);
                            v_isShared_1082_ = v_isSharedCheck_1086_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1053_);
                    lean_dec(v_a_1039_);
                    lean_dec(v_mvarId_1032_);
                    v___x_1087_ = lean_box(0);
                    if v_isShared_1056_ == 0 {
                        lean_ctor_set(v___x_1055_, 0, v___x_1087_);
                        v___x_1089_ = v___x_1055_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
                        v___x_1089_ = v_reuseFailAlloc_1090_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1066_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1066_, 0, v_a_1062_);
                if v_isShared_1065_ == 0 {
                    lean_ctor_set(v___x_1064_, 0, v___x_1066_);
                    v___x_1068_ = v___x_1064_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
                    v___x_1068_ = v_reuseFailAlloc_1069_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1068_;
            }
            6 => {
                if v_isShared_1074_ == 0 {
                    v___x_1076_ = v___x_1073_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
                    v___x_1076_ = v_reuseFailAlloc_1077_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1076_;
            }
            8 => {
                if v_isShared_1082_ == 0 {
                    v___x_1084_ = v___x_1081_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
                    v___x_1084_ = v_reuseFailAlloc_1085_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1084_;
            }
            10 => {
                return v___x_1089_;
            }
            11 => {
                if v_isShared_1095_ == 0 {
                    v___x_1097_ = v___x_1094_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
                    v___x_1097_ = v_reuseFailAlloc_1098_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1097_;
            }
            13 => {
                if v_isShared_1104_ == 0 {
                    v___x_1106_ = v___x_1103_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
                    v___x_1106_ = v_reuseFailAlloc_1107_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(
    mut v_mvarId_1109_: *mut LeanObject,
    mut v___y_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
    mut v___y_1114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1115_: *mut LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(
        v_mvarId_1109_,
        v___y_1110_,
        v___y_1111_,
        v___y_1112_,
        v___y_1113_,
    );
    lean_dec(v___y_1113_);
    lean_dec_ref(v___y_1112_);
    lean_dec(v___y_1111_);
    lean_dec_ref(v___y_1110_);
    return v_res_1115_;
}
pub unsafe fn l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(
    mut v_mvarId_1116_: *mut LeanObject,
    mut v_a_1117_: *mut LeanObject,
    mut v_a_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_1116_);
    v___f_1122_ = lean_alloc_closure(
        l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1122_, 0, v_mvarId_1116_);
    v___x_1123_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(
        v_mvarId_1116_,
        v___f_1122_,
        v_a_1117_,
        v_a_1118_,
        v_a_1119_,
        v_a_1120_,
    );
    return v___x_1123_;
}
pub unsafe fn l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(
    mut v_mvarId_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
    mut v_a_1126_: *mut LeanObject,
    mut v_a_1127_: *mut LeanObject,
    mut v_a_1128_: *mut LeanObject,
    mut v_a_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1130_: *mut LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(
        v_mvarId_1124_,
        v_a_1125_,
        v_a_1126_,
        v_a_1127_,
        v_a_1128_,
    );
    lean_dec(v_a_1128_);
    lean_dec_ref(v_a_1127_);
    lean_dec(v_a_1126_);
    lean_dec_ref(v_a_1125_);
    return v_res_1130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_SplitIf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_SplitIf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
}
