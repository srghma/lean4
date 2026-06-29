// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Reify
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.Linear.Var
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_instInhabitedExpr, l_Lean_mkApp8,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isDefEqD,
};
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Var::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var, l_Lean_Meta_Grind_Arith_Linear_mkVar,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_addNewRawFact, l_Lean_Meta_Grind_alreadyInternalized___redArg,
    l_Lean_Meta_Grind_getGeneration___redArg,
};
use crate::ffi::lean_panic_fn_borrowed;
use crate::ffi::lean_infer_type;
use crate::ffi::lean_grind_internalize;
pub static l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0_value:
    crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 116, 101,
        114, 109, 32, 119, 105, 116, 104, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32,
        105, 110, 115, 116, 97, 110, 99, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 114, 100, 101, 114, 101, 100, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 97, 116, 67, 97, 115, 116, 95, 110, 111, 110, 110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value) as *mut crate::leanh::LeanObject,17867769263165242357 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value) as *mut crate::leanh::LeanObject,16743452394867191478 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [90, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value) as *mut crate::leanh::LeanObject,18263865437487147968 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value) as *mut crate::leanh::LeanObject,2651253468108498348 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value) as *mut crate::leanh::LeanObject,5779414593499529281 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7063772860359172143 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [72, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value) as *mut crate::leanh::LeanObject,15703084674812832738 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value) as *mut crate::leanh::LeanObject,13609749952674037527 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value) as *mut crate::leanh::LeanObject,16856108565602861689 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value) as *mut crate::leanh::LeanObject,4187025665268973031 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isAddInst(
    mut v_struct_1260_: *mut crate::leanh::LeanObject,
    mut v_inst_1261_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_addFn_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: u8 = 0;
    v_addFn_1262_ = crate::leanh::lean_ctor_get(v_struct_1260_, 22);
    v___x_1263_ = l_Lean_Expr_appArg_x21(v_addFn_1262_);
    v___x_1264_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1263_,
        v_inst_1261_,
    );
    crate::leanh::lean_dec_ref(v___x_1263_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(
    mut v_struct_1265_: *mut crate::leanh::LeanObject,
    mut v_inst_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1267_: u8 = 0;
    let mut v_r_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_struct_1265_, v_inst_1266_);
    crate::leanh::lean_dec_ref(v_inst_1266_);
    crate::leanh::lean_dec_ref(v_struct_1265_);
    v_r_1268_ = crate::leanh::lean_box((v_res_1267_) as usize);
    return v_r_1268_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isZeroInst(
    mut v_struct_1269_: *mut crate::leanh::LeanObject,
    mut v_inst_1270_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    v_zero_1271_ = crate::leanh::lean_ctor_get(v_struct_1269_, 17);
    v___x_1272_ = l_Lean_Expr_appArg_x21(v_zero_1271_);
    v___x_1273_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1272_,
        v_inst_1270_,
    );
    crate::leanh::lean_dec_ref(v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(
    mut v_struct_1274_: *mut crate::leanh::LeanObject,
    mut v_inst_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1276_: u8 = 0;
    let mut v_r_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_struct_1274_, v_inst_1275_);
    crate::leanh::lean_dec_ref(v_inst_1275_);
    crate::leanh::lean_dec_ref(v_struct_1274_);
    v_r_1277_ = crate::leanh::lean_box((v_res_1276_) as usize);
    return v_r_1277_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(
    mut v_struct_1278_: *mut crate::leanh::LeanObject,
    mut v_inst_1279_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zsmulFn_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: u8 = 0;
    v_zsmulFn_1280_ = crate::leanh::lean_ctor_get(v_struct_1278_, 23);
    v___x_1281_ = l_Lean_Expr_appArg_x21(v_zsmulFn_1280_);
    v___x_1282_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1281_,
        v_inst_1279_,
    );
    crate::leanh::lean_dec_ref(v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst___boxed(
    mut v_struct_1283_: *mut crate::leanh::LeanObject,
    mut v_inst_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1285_: u8 = 0;
    let mut v_r_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_struct_1283_, v_inst_1284_);
    crate::leanh::lean_dec_ref(v_inst_1284_);
    crate::leanh::lean_dec_ref(v_struct_1283_);
    v_r_1286_ = crate::leanh::lean_box((v_res_1285_) as usize);
    return v_r_1286_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(
    mut v_struct_1287_: *mut crate::leanh::LeanObject,
    mut v_inst_1288_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_nsmulFn_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    v_nsmulFn_1289_ = crate::leanh::lean_ctor_get(v_struct_1287_, 24);
    v___x_1290_ = l_Lean_Expr_appArg_x21(v_nsmulFn_1289_);
    v___x_1291_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1290_,
        v_inst_1288_,
    );
    crate::leanh::lean_dec_ref(v___x_1290_);
    return v___x_1291_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst___boxed(
    mut v_struct_1292_: *mut crate::leanh::LeanObject,
    mut v_inst_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1294_: u8 = 0;
    let mut v_r_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_struct_1292_, v_inst_1293_);
    crate::leanh::lean_dec_ref(v_inst_1293_);
    crate::leanh::lean_dec_ref(v_struct_1292_);
    v_r_1295_ = crate::leanh::lean_box((v_res_1294_) as usize);
    return v_r_1295_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(
    mut v_struct_1296_: *mut crate::leanh::LeanObject,
    mut v_inst_1297_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_homomulFn_x3f_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_homomulFn_x3f_1298_ = crate::leanh::lean_ctor_get(v_struct_1296_, 27);
    if crate::leanh::lean_obj_tag(v_homomulFn_x3f_1298_) == 1 {
        let mut v_val_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1300_: u8 = 0;
        v_val_1299_ = crate::leanh::lean_ctor_get(v_homomulFn_x3f_1298_, 0);
        v___x_1300_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v_val_1299_,
            v_inst_1297_,
        );
        return v___x_1300_;
    } else {
        let mut v___x_1301_: u8 = 0;
        v___x_1301_ = 0;
        return v___x_1301_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst___boxed(
    mut v_struct_1302_: *mut crate::leanh::LeanObject,
    mut v_inst_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1304_: u8 = 0;
    let mut v_r_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1304_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_struct_1302_, v_inst_1303_);
    crate::leanh::lean_dec_ref(v_inst_1303_);
    crate::leanh::lean_dec_ref(v_struct_1302_);
    v_r_1305_ = crate::leanh::lean_box((v_res_1304_) as usize);
    return v_r_1305_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(
    mut v_struct_1306_: *mut crate::leanh::LeanObject,
    mut v_inst_1307_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zsmulFn_x3f_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zsmulFn_x3f_1308_ = crate::leanh::lean_ctor_get(v_struct_1306_, 25);
    if crate::leanh::lean_obj_tag(v_zsmulFn_x3f_1308_) == 1 {
        let mut v_val_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1311_: u8 = 0;
        v_val_1309_ = crate::leanh::lean_ctor_get(v_zsmulFn_x3f_1308_, 0);
        v___x_1310_ = l_Lean_Expr_appArg_x21(v_val_1309_);
        v___x_1311_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v___x_1310_,
            v_inst_1307_,
        );
        crate::leanh::lean_dec_ref(v___x_1310_);
        return v___x_1311_;
    } else {
        let mut v___x_1312_: u8 = 0;
        v___x_1312_ = 0;
        return v___x_1312_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst___boxed(
    mut v_struct_1313_: *mut crate::leanh::LeanObject,
    mut v_inst_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1315_: u8 = 0;
    let mut v_r_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(v_struct_1313_, v_inst_1314_);
    crate::leanh::lean_dec_ref(v_inst_1314_);
    crate::leanh::lean_dec_ref(v_struct_1313_);
    v_r_1316_ = crate::leanh::lean_box((v_res_1315_) as usize);
    return v_r_1316_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(
    mut v_struct_1317_: *mut crate::leanh::LeanObject,
    mut v_inst_1318_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_nsmulFn_x3f_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nsmulFn_x3f_1319_ = crate::leanh::lean_ctor_get(v_struct_1317_, 26);
    if crate::leanh::lean_obj_tag(v_nsmulFn_x3f_1319_) == 1 {
        let mut v_val_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: u8 = 0;
        v_val_1320_ = crate::leanh::lean_ctor_get(v_nsmulFn_x3f_1319_, 0);
        v___x_1321_ = l_Lean_Expr_appArg_x21(v_val_1320_);
        v___x_1322_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v___x_1321_,
            v_inst_1318_,
        );
        crate::leanh::lean_dec_ref(v___x_1321_);
        return v___x_1322_;
    } else {
        let mut v___x_1323_: u8 = 0;
        v___x_1323_ = 0;
        return v___x_1323_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst___boxed(
    mut v_struct_1324_: *mut crate::leanh::LeanObject,
    mut v_inst_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1326_: u8 = 0;
    let mut v_r_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(v_struct_1324_, v_inst_1325_);
    crate::leanh::lean_dec_ref(v_inst_1325_);
    crate::leanh::lean_dec_ref(v_struct_1324_);
    v_r_1327_ = crate::leanh::lean_box((v_res_1326_) as usize);
    return v_r_1327_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSubInst(
    mut v_struct_1328_: *mut crate::leanh::LeanObject,
    mut v_inst_1329_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_subFn_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    v_subFn_1330_ = crate::leanh::lean_ctor_get(v_struct_1328_, 28);
    v___x_1331_ = l_Lean_Expr_appArg_x21(v_subFn_1330_);
    v___x_1332_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1331_,
        v_inst_1329_,
    );
    crate::leanh::lean_dec_ref(v___x_1331_);
    return v___x_1332_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSubInst___boxed(
    mut v_struct_1333_: *mut crate::leanh::LeanObject,
    mut v_inst_1334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1335_: u8 = 0;
    let mut v_r_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1335_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_struct_1333_, v_inst_1334_);
    crate::leanh::lean_dec_ref(v_inst_1334_);
    crate::leanh::lean_dec_ref(v_struct_1333_);
    v_r_1336_ = crate::leanh::lean_box((v_res_1335_) as usize);
    return v_r_1336_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isNegInst(
    mut v_struct_1337_: *mut crate::leanh::LeanObject,
    mut v_inst_1338_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_negFn_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    v_negFn_1339_ = crate::leanh::lean_ctor_get(v_struct_1337_, 29);
    v___x_1340_ = l_Lean_Expr_appArg_x21(v_negFn_1339_);
    v___x_1341_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1340_,
        v_inst_1338_,
    );
    crate::leanh::lean_dec_ref(v___x_1340_);
    return v___x_1341_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isNegInst___boxed(
    mut v_struct_1342_: *mut crate::leanh::LeanObject,
    mut v_inst_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1344_: u8 = 0;
    let mut v_r_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_struct_1342_, v_inst_1343_);
    crate::leanh::lean_dec_ref(v_inst_1343_);
    crate::leanh::lean_dec_ref(v_struct_1342_);
    v_r_1345_ = crate::leanh::lean_box((v_res_1344_) as usize);
    return v_r_1345_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0;
    v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
    mut v_e_1349_: *mut crate::leanh::LeanObject,
    mut v_a_1350_: *mut crate::leanh::LeanObject,
    mut v_a_1351_: *mut crate::leanh::LeanObject,
    mut v_a_1352_: *mut crate::leanh::LeanObject,
    mut v_a_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_a_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1357_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1350_);
                if crate::leanh::lean_obj_tag(v___x_1357_) == 0 {
                    v_a_1358_ = crate::leanh::lean_ctor_get(v___x_1357_, 0);
                    v_isSharedCheck_1371_ = (!crate::leanh::lean_is_exclusive(v___x_1357_)) as u8;
                    if v_isSharedCheck_1371_ == 0 {
                        v___x_1360_ = v___x_1357_;
                        v_isShared_1361_ = v_isSharedCheck_1371_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1358_);
                        crate::leanh::lean_dec(v___x_1357_);
                        v___x_1360_ = crate::leanh::lean_box(0);
                        v_isShared_1361_ = v_isSharedCheck_1371_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1349_);
                    v_a_1372_ = crate::leanh::lean_ctor_get(v___x_1357_, 0);
                    v_isSharedCheck_1379_ = (!crate::leanh::lean_is_exclusive(v___x_1357_)) as u8;
                    if v_isSharedCheck_1379_ == 0 {
                        v___x_1374_ = v___x_1357_;
                        v_isShared_1375_ = v_isSharedCheck_1379_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1372_);
                        crate::leanh::lean_dec(v___x_1357_);
                        v___x_1374_ = crate::leanh::lean_box(0);
                        v_isShared_1375_ = v_isSharedCheck_1379_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1362_ = (crate::leanh::lean_unbox(v_a_1358_) as u8);
                crate::leanh::lean_dec(v_a_1358_);
                if v___x_1362_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_1349_);
                    v___x_1363_ = crate::leanh::lean_box(0);
                    if v_isShared_1361_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1360_, 0, v___x_1363_);
                        v___x_1365_ = v___x_1360_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1366_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
                        v___x_1365_ = v_reuseFailAlloc_1366_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1360_);
                    v___x_1367_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1);
                    v___x_1368_ = l_Lean_indentExpr(v_e_1349_);
                    v___x_1369_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1369_, 0, v___x_1367_);
                    crate::leanh::lean_ctor_set(v___x_1369_, 1, v___x_1368_);
                    v___x_1370_ = l_Lean_Meta_Sym_reportIssue(
                        v___x_1369_,
                        v_a_1350_,
                        v_a_1351_,
                        v_a_1352_,
                        v_a_1353_,
                        v_a_1354_,
                        v_a_1355_,
                    );
                    return v___x_1370_;
                }
            }
            2 => {
                return v___x_1365_;
            }
            3 => {
                if v_isShared_1375_ == 0 {
                    v___x_1377_ = v___x_1374_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
                    v___x_1377_ = v_reuseFailAlloc_1378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___boxed(
    mut v_e_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_a_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
        v_e_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_,
    );
    crate::leanh::lean_dec(v_a_1386_);
    crate::leanh::lean_dec_ref(v_a_1385_);
    crate::leanh::lean_dec(v_a_1384_);
    crate::leanh::lean_dec_ref(v_a_1383_);
    crate::leanh::lean_dec(v_a_1382_);
    crate::leanh::lean_dec_ref(v_a_1381_);
    return v_res_1388_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(
    mut v_e_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_a_1393_: *mut crate::leanh::LeanObject,
    mut v_a_1394_: *mut crate::leanh::LeanObject,
    mut v_a_1395_: *mut crate::leanh::LeanObject,
    mut v_a_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
        v_e_1389_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_,
    );
    return v___x_1401_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___boxed(
    mut v_e_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_a_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(
        v_e_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_,
        v_a_1410_, v_a_1411_, v_a_1412_,
    );
    crate::leanh::lean_dec(v_a_1412_);
    crate::leanh::lean_dec_ref(v_a_1411_);
    crate::leanh::lean_dec(v_a_1410_);
    crate::leanh::lean_dec_ref(v_a_1409_);
    crate::leanh::lean_dec(v_a_1408_);
    crate::leanh::lean_dec_ref(v_a_1407_);
    crate::leanh::lean_dec(v_a_1406_);
    crate::leanh::lean_dec_ref(v_a_1405_);
    crate::leanh::lean_dec(v_a_1404_);
    crate::leanh::lean_dec(v_a_1403_);
    return v_res_1414_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(
    mut v_msg_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = l_Lean_instInhabitedExpr;
    v___x_1417_ = lean_panic_fn_borrowed(v___x_1416_, v_msg_1415_);
    return v___x_1417_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9;
    v___x_1435_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_1436_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_1437_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8;
    v___x_1438_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7;
    v___x_1439_ = l_mkPanicMessageWithDecl(
        v___x_1438_,
        v___x_1437_,
        v___x_1436_,
        v___x_1435_,
        v___x_1434_,
    );
    return v___x_1439_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(
    mut v_a_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
    mut v_a_1442_: *mut crate::leanh::LeanObject,
    mut v_a_1443_: *mut crate::leanh::LeanObject,
    mut v_a_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
    mut v_a_1448_: *mut crate::leanh::LeanObject,
    mut v_a_1449_: *mut crate::leanh::LeanObject,
    mut v_a_1450_: *mut crate::leanh::LeanObject,
    mut v_a_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1485_: u8 = 0;
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_a_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v___y_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1539_: u8 = 0;
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1453_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_,
                    v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_,
                );
                if crate::leanh::lean_obj_tag(v___x_1453_) == 0 {
                    v_a_1454_ = crate::leanh::lean_ctor_get(v___x_1453_, 0);
                    crate::leanh::lean_inc(v_a_1454_);
                    crate::leanh::lean_dec_ref_known(v___x_1453_, 1);
                    v_type_1455_ = crate::leanh::lean_ctor_get(v_a_1454_, 2);
                    crate::leanh::lean_inc_ref(v_type_1455_);
                    v_u_1456_ = crate::leanh::lean_ctor_get(v_a_1454_, 3);
                    crate::leanh::lean_inc(v_u_1456_);
                    v_leInst_x3f_1457_ = crate::leanh::lean_ctor_get(v_a_1454_, 5);
                    crate::leanh::lean_inc(v_leInst_x3f_1457_);
                    v_ltInst_x3f_1458_ = crate::leanh::lean_ctor_get(v_a_1454_, 6);
                    crate::leanh::lean_inc(v_ltInst_x3f_1458_);
                    v_lawfulOrderLTInst_x3f_1459_ = crate::leanh::lean_ctor_get(v_a_1454_, 7);
                    crate::leanh::lean_inc(v_lawfulOrderLTInst_x3f_1459_);
                    v_isPreorderInst_x3f_1460_ = crate::leanh::lean_ctor_get(v_a_1454_, 8);
                    crate::leanh::lean_inc(v_isPreorderInst_x3f_1460_);
                    v_ringInst_x3f_1461_ = crate::leanh::lean_ctor_get(v_a_1454_, 12);
                    crate::leanh::lean_inc(v_ringInst_x3f_1461_);
                    v_orderedRingInst_x3f_1462_ = crate::leanh::lean_ctor_get(v_a_1454_, 14);
                    crate::leanh::lean_inc(v_orderedRingInst_x3f_1462_);
                    crate::leanh::lean_dec(v_a_1454_);
                    v___x_1463_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4;
                    v___x_1464_ = crate::leanh::lean_box(0);
                    v___x_1465_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1465_, 0, v_u_1456_);
                    crate::leanh::lean_ctor_set(v___x_1465_, 1, v___x_1464_);
                    v___x_1466_ = l_Lean_mkConst(v___x_1463_, v___x_1465_);
                    if crate::leanh::lean_obj_tag(v_ringInst_x3f_1461_) == 0 {
                        v___x_1533_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                        v___x_1534_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1533_);
                        v___y_1529_ = v___x_1534_;
                        state = 10;
                        continue;
                    } else {
                        v_val_1535_ = crate::leanh::lean_ctor_get(v_ringInst_x3f_1461_, 0);
                        crate::leanh::lean_inc(v_val_1535_);
                        crate::leanh::lean_dec_ref_known(v_ringInst_x3f_1461_, 1);
                        v___y_1529_ = v_val_1535_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1440_);
                    v_a_1536_ = crate::leanh::lean_ctor_get(v___x_1453_, 0);
                    v_isSharedCheck_1543_ = (!crate::leanh::lean_is_exclusive(v___x_1453_)) as u8;
                    if v_isSharedCheck_1543_ == 0 {
                        v___x_1538_ = v___x_1453_;
                        v_isShared_1539_ = v_isSharedCheck_1543_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1536_);
                        crate::leanh::lean_dec(v___x_1453_);
                        v___x_1538_ = crate::leanh::lean_box(0);
                        v_isShared_1539_ = v_isSharedCheck_1543_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_a_1440_);
                v___x_1474_ = l_Lean_mkApp8(
                    v___x_1466_,
                    v_type_1455_,
                    v___y_1470_,
                    v___y_1469_,
                    v___y_1468_,
                    v___y_1471_,
                    v___y_1472_,
                    v___y_1473_,
                    v_a_1440_,
                );
                crate::leanh::lean_inc(v_a_1451_);
                crate::leanh::lean_inc_ref(v_a_1450_);
                crate::leanh::lean_inc(v_a_1449_);
                crate::leanh::lean_inc_ref(v_a_1448_);
                crate::leanh::lean_inc_ref(v___x_1474_);
                v___x_1475_ =
                    lean_infer_type(v___x_1474_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
                if crate::leanh::lean_obj_tag(v___x_1475_) == 0 {
                    v_a_1476_ = crate::leanh::lean_ctor_get(v___x_1475_, 0);
                    crate::leanh::lean_inc(v_a_1476_);
                    crate::leanh::lean_dec_ref_known(v___x_1475_, 1);
                    v___x_1477_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1440_, v_a_1442_);
                    crate::leanh::lean_dec_ref(v_a_1440_);
                    if crate::leanh::lean_obj_tag(v___x_1477_) == 0 {
                        v_a_1478_ = crate::leanh::lean_ctor_get(v___x_1477_, 0);
                        crate::leanh::lean_inc(v_a_1478_);
                        crate::leanh::lean_dec_ref_known(v___x_1477_, 1);
                        v___x_1479_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6;
                        v___x_1480_ = crate::leanh::lean_box(1);
                        v___x_1481_ = l_Lean_Meta_Grind_addNewRawFact(
                            v___x_1474_,
                            v_a_1476_,
                            v_a_1478_,
                            v___x_1479_,
                            v___x_1480_,
                            v_a_1442_,
                            v_a_1443_,
                            v_a_1444_,
                            v_a_1445_,
                            v_a_1446_,
                            v_a_1447_,
                            v_a_1448_,
                            v_a_1449_,
                            v_a_1450_,
                            v_a_1451_,
                        );
                        return v___x_1481_;
                    } else {
                        crate::leanh::lean_dec(v_a_1476_);
                        crate::leanh::lean_dec_ref(v___x_1474_);
                        v_a_1482_ = crate::leanh::lean_ctor_get(v___x_1477_, 0);
                        v_isSharedCheck_1489_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1477_)) as u8;
                        if v_isSharedCheck_1489_ == 0 {
                            v___x_1484_ = v___x_1477_;
                            v_isShared_1485_ = v_isSharedCheck_1489_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1482_);
                            crate::leanh::lean_dec(v___x_1477_);
                            v___x_1484_ = crate::leanh::lean_box(0);
                            v_isShared_1485_ = v_isSharedCheck_1489_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1474_);
                    crate::leanh::lean_dec_ref(v_a_1440_);
                    v_a_1490_ = crate::leanh::lean_ctor_get(v___x_1475_, 0);
                    v_isSharedCheck_1497_ = (!crate::leanh::lean_is_exclusive(v___x_1475_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v___x_1492_ = v___x_1475_;
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1490_);
                        crate::leanh::lean_dec(v___x_1475_);
                        v___x_1492_ = crate::leanh::lean_box(0);
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1485_ == 0 {
                    v___x_1487_ = v___x_1484_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
                    v___x_1487_ = v_reuseFailAlloc_1488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1487_;
            }
            4 => {
                if v_isShared_1493_ == 0 {
                    v___x_1495_ = v___x_1492_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
                    v___x_1495_ = v_reuseFailAlloc_1496_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1495_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_orderedRingInst_x3f_1462_) == 0 {
                    v___x_1504_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1505_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1504_);
                    v___y_1468_ = v___y_1499_;
                    v___y_1469_ = v___y_1501_;
                    v___y_1470_ = v___y_1500_;
                    v___y_1471_ = v___y_1502_;
                    v___y_1472_ = v___y_1503_;
                    v___y_1473_ = v___x_1505_;
                    state = 1;
                    continue;
                } else {
                    v_val_1506_ = crate::leanh::lean_ctor_get(v_orderedRingInst_x3f_1462_, 0);
                    crate::leanh::lean_inc(v_val_1506_);
                    crate::leanh::lean_dec_ref_known(v_orderedRingInst_x3f_1462_, 1);
                    v___y_1468_ = v___y_1499_;
                    v___y_1469_ = v___y_1501_;
                    v___y_1470_ = v___y_1500_;
                    v___y_1471_ = v___y_1502_;
                    v___y_1472_ = v___y_1503_;
                    v___y_1473_ = v_val_1506_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_isPreorderInst_x3f_1460_) == 0 {
                    v___x_1512_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1513_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1512_);
                    v___y_1499_ = v___y_1508_;
                    v___y_1500_ = v___y_1510_;
                    v___y_1501_ = v___y_1509_;
                    v___y_1502_ = v___y_1511_;
                    v___y_1503_ = v___x_1513_;
                    state = 6;
                    continue;
                } else {
                    v_val_1514_ = crate::leanh::lean_ctor_get(v_isPreorderInst_x3f_1460_, 0);
                    crate::leanh::lean_inc(v_val_1514_);
                    crate::leanh::lean_dec_ref_known(v_isPreorderInst_x3f_1460_, 1);
                    v___y_1499_ = v___y_1508_;
                    v___y_1500_ = v___y_1510_;
                    v___y_1501_ = v___y_1509_;
                    v___y_1502_ = v___y_1511_;
                    v___y_1503_ = v_val_1514_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_lawfulOrderLTInst_x3f_1459_) == 0 {
                    v___x_1519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1520_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1519_);
                    v___y_1508_ = v___y_1518_;
                    v___y_1509_ = v___y_1517_;
                    v___y_1510_ = v___y_1516_;
                    v___y_1511_ = v___x_1520_;
                    state = 7;
                    continue;
                } else {
                    v_val_1521_ = crate::leanh::lean_ctor_get(v_lawfulOrderLTInst_x3f_1459_, 0);
                    crate::leanh::lean_inc(v_val_1521_);
                    crate::leanh::lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1459_, 1);
                    v___y_1508_ = v___y_1518_;
                    v___y_1509_ = v___y_1517_;
                    v___y_1510_ = v___y_1516_;
                    v___y_1511_ = v_val_1521_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_ltInst_x3f_1458_) == 0 {
                    v___x_1525_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1526_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1525_);
                    v___y_1516_ = v___y_1523_;
                    v___y_1517_ = v___y_1524_;
                    v___y_1518_ = v___x_1526_;
                    state = 8;
                    continue;
                } else {
                    v_val_1527_ = crate::leanh::lean_ctor_get(v_ltInst_x3f_1458_, 0);
                    crate::leanh::lean_inc(v_val_1527_);
                    crate::leanh::lean_dec_ref_known(v_ltInst_x3f_1458_, 1);
                    v___y_1516_ = v___y_1523_;
                    v___y_1517_ = v___y_1524_;
                    v___y_1518_ = v_val_1527_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_leInst_x3f_1457_) == 0 {
                    v___x_1530_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1531_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1530_);
                    v___y_1523_ = v___y_1529_;
                    v___y_1524_ = v___x_1531_;
                    state = 9;
                    continue;
                } else {
                    v_val_1532_ = crate::leanh::lean_ctor_get(v_leInst_x3f_1457_, 0);
                    crate::leanh::lean_inc(v_val_1532_);
                    crate::leanh::lean_dec_ref_known(v_leInst_x3f_1457_, 1);
                    v___y_1523_ = v___y_1529_;
                    v___y_1524_ = v_val_1532_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                if v_isShared_1539_ == 0 {
                    v___x_1541_ = v___x_1538_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
                    v___x_1541_ = v_reuseFailAlloc_1542_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___boxed(
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
    mut v_a_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1557_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
    crate::leanh::lean_dec(v_a_1555_);
    crate::leanh::lean_dec_ref(v_a_1554_);
    crate::leanh::lean_dec(v_a_1553_);
    crate::leanh::lean_dec_ref(v_a_1552_);
    crate::leanh::lean_dec(v_a_1551_);
    crate::leanh::lean_dec_ref(v_a_1550_);
    crate::leanh::lean_dec(v_a_1549_);
    crate::leanh::lean_dec_ref(v_a_1548_);
    crate::leanh::lean_dec(v_a_1547_);
    crate::leanh::lean_dec(v_a_1546_);
    crate::leanh::lean_dec(v_a_1545_);
    return v_res_1557_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(
    mut v_generation_1558_: *mut crate::leanh::LeanObject,
    mut v_e_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
    mut v_a_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
    mut v_a_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_a_1569_: *mut crate::leanh::LeanObject,
    mut v_a_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_a_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_a_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1599_: u8 = 0;
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1613_: u8 = 0;
    let mut v_a_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_a_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1572_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1559_, v_a_1561_);
                if crate::leanh::lean_obj_tag(v___x_1572_) == 0 {
                    v_a_1573_ = crate::leanh::lean_ctor_get(v___x_1572_, 0);
                    crate::leanh::lean_inc(v_a_1573_);
                    crate::leanh::lean_dec_ref_known(v___x_1572_, 1);
                    v___x_1574_ = 1;
                    v___x_1575_ = (crate::leanh::lean_unbox(v_a_1573_) as u8);
                    crate::leanh::lean_dec(v_a_1573_);
                    if v___x_1575_ == 0 {
                        v___x_1576_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_a_1570_);
                        crate::leanh::lean_inc_ref(v_a_1569_);
                        crate::leanh::lean_inc(v_a_1568_);
                        crate::leanh::lean_inc_ref(v_a_1567_);
                        crate::leanh::lean_inc(v_a_1566_);
                        crate::leanh::lean_inc_ref(v_a_1565_);
                        crate::leanh::lean_inc(v_a_1564_);
                        crate::leanh::lean_inc_ref(v_a_1563_);
                        crate::leanh::lean_inc(v_a_1562_);
                        crate::leanh::lean_inc(v_a_1561_);
                        crate::leanh::lean_inc_ref(v_e_1559_);
                        v___x_1577_ = lean_grind_internalize(
                            v_e_1559_,
                            v_generation_1558_,
                            v___x_1576_,
                            v_a_1561_,
                            v_a_1562_,
                            v_a_1563_,
                            v_a_1564_,
                            v_a_1565_,
                            v_a_1566_,
                            v_a_1567_,
                            v_a_1568_,
                            v_a_1569_,
                            v_a_1570_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1577_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1577_, 1);
                            v___x_1578_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(
                                v_e_1559_,
                                v___x_1574_,
                                v_a_1560_,
                                v_a_1561_,
                                v_a_1562_,
                                v_a_1563_,
                                v_a_1564_,
                                v_a_1565_,
                                v_a_1566_,
                                v_a_1567_,
                                v_a_1568_,
                                v_a_1569_,
                                v_a_1570_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1578_) == 0 {
                                v_a_1579_ = crate::leanh::lean_ctor_get(v___x_1578_, 0);
                                v_isSharedCheck_1587_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1578_)) as u8;
                                if v_isSharedCheck_1587_ == 0 {
                                    v___x_1581_ = v___x_1578_;
                                    v_isShared_1582_ = v_isSharedCheck_1587_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1579_);
                                    crate::leanh::lean_dec(v___x_1578_);
                                    v___x_1581_ = crate::leanh::lean_box(0);
                                    v_isShared_1582_ = v_isSharedCheck_1587_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_1588_ = crate::leanh::lean_ctor_get(v___x_1578_, 0);
                                v_isSharedCheck_1595_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1578_)) as u8;
                                if v_isSharedCheck_1595_ == 0 {
                                    v___x_1590_ = v___x_1578_;
                                    v_isShared_1591_ = v_isSharedCheck_1595_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1588_);
                                    crate::leanh::lean_dec(v___x_1578_);
                                    v___x_1590_ = crate::leanh::lean_box(0);
                                    v_isShared_1591_ = v_isSharedCheck_1595_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_1559_);
                            v_a_1596_ = crate::leanh::lean_ctor_get(v___x_1577_, 0);
                            v_isSharedCheck_1603_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1577_)) as u8;
                            if v_isSharedCheck_1603_ == 0 {
                                v___x_1598_ = v___x_1577_;
                                v_isShared_1599_ = v_isSharedCheck_1603_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1596_);
                                crate::leanh::lean_dec(v___x_1577_);
                                v___x_1598_ = crate::leanh::lean_box(0);
                                v_isShared_1599_ = v_isSharedCheck_1603_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_generation_1558_);
                        v___x_1604_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(
                            v_e_1559_,
                            v___x_1574_,
                            v_a_1560_,
                            v_a_1561_,
                            v_a_1562_,
                            v_a_1563_,
                            v_a_1564_,
                            v_a_1565_,
                            v_a_1566_,
                            v_a_1567_,
                            v_a_1568_,
                            v_a_1569_,
                            v_a_1570_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1604_) == 0 {
                            v_a_1605_ = crate::leanh::lean_ctor_get(v___x_1604_, 0);
                            v_isSharedCheck_1613_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1604_)) as u8;
                            if v_isSharedCheck_1613_ == 0 {
                                v___x_1607_ = v___x_1604_;
                                v_isShared_1608_ = v_isSharedCheck_1613_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1605_);
                                crate::leanh::lean_dec(v___x_1604_);
                                v___x_1607_ = crate::leanh::lean_box(0);
                                v_isShared_1608_ = v_isSharedCheck_1613_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_1614_ = crate::leanh::lean_ctor_get(v___x_1604_, 0);
                            v_isSharedCheck_1621_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1604_)) as u8;
                            if v_isSharedCheck_1621_ == 0 {
                                v___x_1616_ = v___x_1604_;
                                v_isShared_1617_ = v_isSharedCheck_1621_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1614_);
                                crate::leanh::lean_dec(v___x_1604_);
                                v___x_1616_ = crate::leanh::lean_box(0);
                                v_isShared_1617_ = v_isSharedCheck_1621_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1559_);
                    crate::leanh::lean_dec(v_generation_1558_);
                    v_a_1622_ = crate::leanh::lean_ctor_get(v___x_1572_, 0);
                    v_isSharedCheck_1629_ = (!crate::leanh::lean_is_exclusive(v___x_1572_)) as u8;
                    if v_isSharedCheck_1629_ == 0 {
                        v___x_1624_ = v___x_1572_;
                        v_isShared_1625_ = v_isSharedCheck_1629_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1622_);
                        crate::leanh::lean_dec(v___x_1572_);
                        v___x_1624_ = crate::leanh::lean_box(0);
                        v_isShared_1625_ = v_isSharedCheck_1629_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1583_, 0, v_a_1579_);
                if v_isShared_1582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1581_, 0, v___x_1583_);
                    v___x_1585_ = v___x_1581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
                    v___x_1585_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1585_;
            }
            3 => {
                if v_isShared_1591_ == 0 {
                    v___x_1593_ = v___x_1590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1593_;
            }
            5 => {
                if v_isShared_1599_ == 0 {
                    v___x_1601_ = v___x_1598_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
                    v___x_1601_ = v_reuseFailAlloc_1602_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1601_;
            }
            7 => {
                v___x_1609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1609_, 0, v_a_1605_);
                if v_isShared_1608_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1607_, 0, v___x_1609_);
                    v___x_1611_ = v___x_1607_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1612_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
                    v___x_1611_ = v_reuseFailAlloc_1612_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1611_;
            }
            9 => {
                if v_isShared_1617_ == 0 {
                    v___x_1619_ = v___x_1616_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1620_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
                    v___x_1619_ = v_reuseFailAlloc_1620_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1619_;
            }
            11 => {
                if v_isShared_1625_ == 0 {
                    v___x_1627_ = v___x_1624_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
                    v___x_1627_ = v_reuseFailAlloc_1628_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar___boxed(
    mut v_generation_1630_: *mut crate::leanh::LeanObject,
    mut v_e_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_a_1633_: *mut crate::leanh::LeanObject,
    mut v_a_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
    mut v_a_1637_: *mut crate::leanh::LeanObject,
    mut v_a_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
    mut v_a_1640_: *mut crate::leanh::LeanObject,
    mut v_a_1641_: *mut crate::leanh::LeanObject,
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1644_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1630_, v_e_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
    crate::leanh::lean_dec(v_a_1642_);
    crate::leanh::lean_dec_ref(v_a_1641_);
    crate::leanh::lean_dec(v_a_1640_);
    crate::leanh::lean_dec_ref(v_a_1639_);
    crate::leanh::lean_dec(v_a_1638_);
    crate::leanh::lean_dec_ref(v_a_1637_);
    crate::leanh::lean_dec(v_a_1636_);
    crate::leanh::lean_dec_ref(v_a_1635_);
    crate::leanh::lean_dec(v_a_1634_);
    crate::leanh::lean_dec(v_a_1633_);
    crate::leanh::lean_dec(v_a_1632_);
    return v_res_1644_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(
    mut v_generation_1645_: *mut crate::leanh::LeanObject,
    mut v_e_1646_: *mut crate::leanh::LeanObject,
    mut v_a_1647_: *mut crate::leanh::LeanObject,
    mut v_a_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
    mut v_a_1655_: *mut crate::leanh::LeanObject,
    mut v_a_1656_: *mut crate::leanh::LeanObject,
    mut v_a_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1664_: u8 = 0;
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1646_);
                v___x_1659_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
                    v_e_1646_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_,
                );
                if crate::leanh::lean_obj_tag(v___x_1659_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1659_, 1);
                    v___x_1660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1645_, v_e_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
                    return v___x_1660_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_1646_);
                    crate::leanh::lean_dec(v_generation_1645_);
                    v_a_1661_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
                    v_isSharedCheck_1668_ = (!crate::leanh::lean_is_exclusive(v___x_1659_)) as u8;
                    if v_isSharedCheck_1668_ == 0 {
                        v___x_1663_ = v___x_1659_;
                        v_isShared_1664_ = v_isSharedCheck_1668_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1661_);
                        crate::leanh::lean_dec(v___x_1659_);
                        v___x_1663_ = crate::leanh::lean_box(0);
                        v_isShared_1664_ = v_isSharedCheck_1668_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1664_ == 0 {
                    v___x_1666_ = v___x_1663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
                    v___x_1666_ = v_reuseFailAlloc_1667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar___boxed(
    mut v_generation_1669_: *mut crate::leanh::LeanObject,
    mut v_e_1670_: *mut crate::leanh::LeanObject,
    mut v_a_1671_: *mut crate::leanh::LeanObject,
    mut v_a_1672_: *mut crate::leanh::LeanObject,
    mut v_a_1673_: *mut crate::leanh::LeanObject,
    mut v_a_1674_: *mut crate::leanh::LeanObject,
    mut v_a_1675_: *mut crate::leanh::LeanObject,
    mut v_a_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
    mut v_a_1680_: *mut crate::leanh::LeanObject,
    mut v_a_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1669_, v_e_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
    crate::leanh::lean_dec(v_a_1681_);
    crate::leanh::lean_dec_ref(v_a_1680_);
    crate::leanh::lean_dec(v_a_1679_);
    crate::leanh::lean_dec_ref(v_a_1678_);
    crate::leanh::lean_dec(v_a_1677_);
    crate::leanh::lean_dec_ref(v_a_1676_);
    crate::leanh::lean_dec(v_a_1675_);
    crate::leanh::lean_dec_ref(v_a_1674_);
    crate::leanh::lean_dec(v_a_1673_);
    crate::leanh::lean_dec(v_a_1672_);
    crate::leanh::lean_dec(v_a_1671_);
    return v_res_1683_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(
    mut v_skipVar_1684_: u8,
    mut v_generation_1685_: *mut crate::leanh::LeanObject,
    mut v_e_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
    mut v_a_1692_: *mut crate::leanh::LeanObject,
    mut v_a_1693_: *mut crate::leanh::LeanObject,
    mut v_a_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
    mut v_a_1696_: *mut crate::leanh::LeanObject,
    mut v_a_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_a_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1716_: u8 = 0;
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_skipVar_1684_ == 0 {
                    v___x_1699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1685_, v_e_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
                    if crate::leanh::lean_obj_tag(v___x_1699_) == 0 {
                        v_a_1700_ = crate::leanh::lean_ctor_get(v___x_1699_, 0);
                        v_isSharedCheck_1708_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1699_)) as u8;
                        if v_isSharedCheck_1708_ == 0 {
                            v___x_1702_ = v___x_1699_;
                            v_isShared_1703_ = v_isSharedCheck_1708_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1700_);
                            crate::leanh::lean_dec(v___x_1699_);
                            v___x_1702_ = crate::leanh::lean_box(0);
                            v_isShared_1703_ = v_isSharedCheck_1708_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1709_ = crate::leanh::lean_ctor_get(v___x_1699_, 0);
                        v_isSharedCheck_1716_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1699_)) as u8;
                        if v_isSharedCheck_1716_ == 0 {
                            v___x_1711_ = v___x_1699_;
                            v_isShared_1712_ = v_isSharedCheck_1716_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1709_);
                            crate::leanh::lean_dec(v___x_1699_);
                            v___x_1711_ = crate::leanh::lean_box(0);
                            v_isShared_1712_ = v_isSharedCheck_1716_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1686_);
                    crate::leanh::lean_dec(v_generation_1685_);
                    v___x_1717_ = crate::leanh::lean_box(0);
                    v___x_1718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1717_);
                    return v___x_1718_;
                }
            }
            1 => {
                v___x_1704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1704_, 0, v_a_1700_);
                if v_isShared_1703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1702_, 0, v___x_1704_);
                    v___x_1706_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1706_;
            }
            3 => {
                if v_isShared_1712_ == 0 {
                    v___x_1714_ = v___x_1711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
                    v___x_1714_ = v_reuseFailAlloc_1715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar___boxed(
    mut v_skipVar_1719_: *mut crate::leanh::LeanObject,
    mut v_generation_1720_: *mut crate::leanh::LeanObject,
    mut v_e_1721_: *mut crate::leanh::LeanObject,
    mut v_a_1722_: *mut crate::leanh::LeanObject,
    mut v_a_1723_: *mut crate::leanh::LeanObject,
    mut v_a_1724_: *mut crate::leanh::LeanObject,
    mut v_a_1725_: *mut crate::leanh::LeanObject,
    mut v_a_1726_: *mut crate::leanh::LeanObject,
    mut v_a_1727_: *mut crate::leanh::LeanObject,
    mut v_a_1728_: *mut crate::leanh::LeanObject,
    mut v_a_1729_: *mut crate::leanh::LeanObject,
    mut v_a_1730_: *mut crate::leanh::LeanObject,
    mut v_a_1731_: *mut crate::leanh::LeanObject,
    mut v_a_1732_: *mut crate::leanh::LeanObject,
    mut v_a_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipVar_boxed_1734_: u8 = 0;
    let mut v_res_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_1734_ = (crate::leanh::lean_unbox(v_skipVar_1719_) as u8);
    v_res_1735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_boxed_1734_, v_generation_1720_, v_e_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
    crate::leanh::lean_dec(v_a_1732_);
    crate::leanh::lean_dec_ref(v_a_1731_);
    crate::leanh::lean_dec(v_a_1730_);
    crate::leanh::lean_dec_ref(v_a_1729_);
    crate::leanh::lean_dec(v_a_1728_);
    crate::leanh::lean_dec_ref(v_a_1727_);
    crate::leanh::lean_dec(v_a_1726_);
    crate::leanh::lean_dec_ref(v_a_1725_);
    crate::leanh::lean_dec(v_a_1724_);
    crate::leanh::lean_dec(v_a_1723_);
    crate::leanh::lean_dec(v_a_1722_);
    return v_res_1735_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(
    mut v_skipVar_1736_: u8,
    mut v_generation_1737_: *mut crate::leanh::LeanObject,
    mut v_e_1738_: *mut crate::leanh::LeanObject,
    mut v_a_1739_: *mut crate::leanh::LeanObject,
    mut v_a_1740_: *mut crate::leanh::LeanObject,
    mut v_a_1741_: *mut crate::leanh::LeanObject,
    mut v_a_1742_: *mut crate::leanh::LeanObject,
    mut v_a_1743_: *mut crate::leanh::LeanObject,
    mut v_a_1744_: *mut crate::leanh::LeanObject,
    mut v_a_1745_: *mut crate::leanh::LeanObject,
    mut v_a_1746_: *mut crate::leanh::LeanObject,
    mut v_a_1747_: *mut crate::leanh::LeanObject,
    mut v_a_1748_: *mut crate::leanh::LeanObject,
    mut v_a_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v_a_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1772_: u8 = 0;
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1777_: u8 = 0;
    let mut v_unused_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1738_);
                v___x_1751_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
                    v_e_1738_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_,
                );
                if crate::leanh::lean_obj_tag(v___x_1751_) == 0 {
                    v_isSharedCheck_1777_ = (!crate::leanh::lean_is_exclusive(v___x_1751_)) as u8;
                    if v_isSharedCheck_1777_ == 0 {
                        v_unused_1778_ = crate::leanh::lean_ctor_get(v___x_1751_, 0);
                        crate::leanh::lean_dec(v_unused_1778_);
                        v___x_1753_ = v___x_1751_;
                        v_isShared_1754_ = v_isSharedCheck_1777_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1751_);
                        v___x_1753_ = crate::leanh::lean_box(0);
                        v_isShared_1754_ = v_isSharedCheck_1777_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1738_);
                    crate::leanh::lean_dec(v_generation_1737_);
                    v_a_1779_ = crate::leanh::lean_ctor_get(v___x_1751_, 0);
                    v_isSharedCheck_1786_ = (!crate::leanh::lean_is_exclusive(v___x_1751_)) as u8;
                    if v_isSharedCheck_1786_ == 0 {
                        v___x_1781_ = v___x_1751_;
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1779_);
                        crate::leanh::lean_dec(v___x_1751_);
                        v___x_1781_ = crate::leanh::lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_skipVar_1736_ == 0 {
                    crate::leanh::lean_del_object(v___x_1753_);
                    v___x_1755_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1737_, v_e_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
                    if crate::leanh::lean_obj_tag(v___x_1755_) == 0 {
                        v_a_1756_ = crate::leanh::lean_ctor_get(v___x_1755_, 0);
                        v_isSharedCheck_1764_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1755_)) as u8;
                        if v_isSharedCheck_1764_ == 0 {
                            v___x_1758_ = v___x_1755_;
                            v_isShared_1759_ = v_isSharedCheck_1764_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1756_);
                            crate::leanh::lean_dec(v___x_1755_);
                            v___x_1758_ = crate::leanh::lean_box(0);
                            v_isShared_1759_ = v_isSharedCheck_1764_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1765_ = crate::leanh::lean_ctor_get(v___x_1755_, 0);
                        v_isSharedCheck_1772_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1755_)) as u8;
                        if v_isSharedCheck_1772_ == 0 {
                            v___x_1767_ = v___x_1755_;
                            v_isShared_1768_ = v_isSharedCheck_1772_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1765_);
                            crate::leanh::lean_dec(v___x_1755_);
                            v___x_1767_ = crate::leanh::lean_box(0);
                            v_isShared_1768_ = v_isSharedCheck_1772_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1738_);
                    crate::leanh::lean_dec(v_generation_1737_);
                    v___x_1773_ = crate::leanh::lean_box(0);
                    if v_isShared_1754_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1773_);
                        v___x_1775_ = v___x_1753_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1776_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
                        v___x_1775_ = v_reuseFailAlloc_1776_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1760_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1760_, 0, v_a_1756_);
                if v_isShared_1759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1760_);
                    v___x_1762_ = v___x_1758_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
                    v___x_1762_ = v_reuseFailAlloc_1763_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1762_;
            }
            4 => {
                if v_isShared_1768_ == 0 {
                    v___x_1770_ = v___x_1767_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
                    v___x_1770_ = v_reuseFailAlloc_1771_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1770_;
            }
            6 => {
                return v___x_1775_;
            }
            7 => {
                if v_isShared_1782_ == 0 {
                    v___x_1784_ = v___x_1781_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
                    v___x_1784_ = v_reuseFailAlloc_1785_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar___boxed(
    mut v_skipVar_1787_: *mut crate::leanh::LeanObject,
    mut v_generation_1788_: *mut crate::leanh::LeanObject,
    mut v_e_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
    mut v_a_1791_: *mut crate::leanh::LeanObject,
    mut v_a_1792_: *mut crate::leanh::LeanObject,
    mut v_a_1793_: *mut crate::leanh::LeanObject,
    mut v_a_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
    mut v_a_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipVar_boxed_1802_: u8 = 0;
    let mut v_res_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_1802_ = (crate::leanh::lean_unbox(v_skipVar_1787_) as u8);
    v_res_1803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_boxed_1802_, v_generation_1788_, v_e_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
    crate::leanh::lean_dec(v_a_1800_);
    crate::leanh::lean_dec_ref(v_a_1799_);
    crate::leanh::lean_dec(v_a_1798_);
    crate::leanh::lean_dec_ref(v_a_1797_);
    crate::leanh::lean_dec(v_a_1796_);
    crate::leanh::lean_dec_ref(v_a_1795_);
    crate::leanh::lean_dec(v_a_1794_);
    crate::leanh::lean_dec_ref(v_a_1793_);
    crate::leanh::lean_dec(v_a_1792_);
    crate::leanh::lean_dec(v_a_1791_);
    crate::leanh::lean_dec(v_a_1790_);
    return v_res_1803_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(
    mut v_e_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
    mut v_a_1809_: *mut crate::leanh::LeanObject,
    mut v_a_1810_: *mut crate::leanh::LeanObject,
    mut v_a_1811_: *mut crate::leanh::LeanObject,
    mut v_a_1812_: *mut crate::leanh::LeanObject,
    mut v_a_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1817_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_,
                    v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_,
                );
                if crate::leanh::lean_obj_tag(v___x_1817_) == 0 {
                    v_a_1818_ = crate::leanh::lean_ctor_get(v___x_1817_, 0);
                    crate::leanh::lean_inc(v_a_1818_);
                    crate::leanh::lean_dec_ref_known(v___x_1817_, 1);
                    v_ofNatZero_1819_ = crate::leanh::lean_ctor_get(v_a_1818_, 18);
                    crate::leanh::lean_inc_ref(v_ofNatZero_1819_);
                    crate::leanh::lean_dec(v_a_1818_);
                    v___x_1820_ = l_Lean_Meta_isDefEqD(
                        v_e_1804_,
                        v_ofNatZero_1819_,
                        v_a_1812_,
                        v_a_1813_,
                        v_a_1814_,
                        v_a_1815_,
                    );
                    return v___x_1820_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_1804_);
                    v_a_1821_ = crate::leanh::lean_ctor_get(v___x_1817_, 0);
                    v_isSharedCheck_1828_ = (!crate::leanh::lean_is_exclusive(v___x_1817_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v___x_1817_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1821_);
                        crate::leanh::lean_dec(v___x_1817_);
                        v___x_1823_ = crate::leanh::lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1824_ == 0 {
                    v___x_1826_ = v___x_1823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
                    v___x_1826_ = v_reuseFailAlloc_1827_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero___boxed(
    mut v_e_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
    mut v_a_1831_: *mut crate::leanh::LeanObject,
    mut v_a_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
    crate::leanh::lean_dec(v_a_1840_);
    crate::leanh::lean_dec_ref(v_a_1839_);
    crate::leanh::lean_dec(v_a_1838_);
    crate::leanh::lean_dec_ref(v_a_1837_);
    crate::leanh::lean_dec(v_a_1836_);
    crate::leanh::lean_dec_ref(v_a_1835_);
    crate::leanh::lean_dec(v_a_1834_);
    crate::leanh::lean_dec_ref(v_a_1833_);
    crate::leanh::lean_dec(v_a_1832_);
    crate::leanh::lean_dec(v_a_1831_);
    crate::leanh::lean_dec(v_a_1830_);
    return v_res_1842_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(
    mut v_generation_1878_: *mut crate::leanh::LeanObject,
    mut v_e_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
    mut v_a_1884_: *mut crate::leanh::LeanObject,
    mut v_a_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: u8 = 0;
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: u8 = 0;
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: u8 = 0;
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: u8 = 0;
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut v_a_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1950_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1954_: u8 = 0;
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1965_: u8 = 0;
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1970_: u8 = 0;
    let mut v_a_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1974_: u8 = 0;
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v_val_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut v_a_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1997_: u8 = 0;
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_a_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v_a_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2043_: u8 = 0;
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut v_orderedRingInst_x3f_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2063_: u8 = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut v_a_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2079_: u8 = 0;
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2083_: u8 = 0;
    let mut v_a_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2087_: u8 = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1879_);
                v___x_1892_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1879_, v_a_1888_);
                if crate::leanh::lean_obj_tag(v___x_1892_) == 0 {
                    v_a_1893_ = crate::leanh::lean_ctor_get(v___x_1892_, 0);
                    crate::leanh::lean_inc(v_a_1893_);
                    crate::leanh::lean_dec_ref_known(v___x_1892_, 1);
                    v___x_1894_ = l_Lean_Expr_cleanupAnnotations(v_a_1893_);
                    v___x_1895_ = l_Lean_Expr_isApp(v___x_1894_);
                    if v___x_1895_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1894_);
                        v___x_1896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                        return v___x_1896_;
                    } else {
                        v_arg_1897_ = crate::leanh::lean_ctor_get(v___x_1894_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1897_);
                        v___x_1898_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1894_);
                        v___x_1899_ = l_Lean_Expr_isApp(v___x_1898_);
                        if v___x_1899_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1898_);
                            crate::leanh::lean_dec_ref(v_arg_1897_);
                            v___x_1900_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                            return v___x_1900_;
                        } else {
                            v_arg_1901_ = crate::leanh::lean_ctor_get(v___x_1898_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1901_);
                            v___x_1902_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1898_);
                            v___x_1903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2;
                            v___x_1904_ = l_Lean_Expr_isConstOf(v___x_1902_, v___x_1903_);
                            if v___x_1904_ == 0 {
                                v___x_1905_ = l_Lean_Expr_isApp(v___x_1902_);
                                if v___x_1905_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_1902_);
                                    crate::leanh::lean_dec_ref(v_arg_1901_);
                                    crate::leanh::lean_dec_ref(v_arg_1897_);
                                    v___x_1906_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                    return v___x_1906_;
                                } else {
                                    v_arg_1907_ = crate::leanh::lean_ctor_get(v___x_1902_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_1907_);
                                    v___x_1908_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1902_);
                                    v___x_1909_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5;
                                    v___x_1910_ = l_Lean_Expr_isConstOf(v___x_1908_, v___x_1909_);
                                    if v___x_1910_ == 0 {
                                        v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8;
                                        v___x_1912_ =
                                            l_Lean_Expr_isConstOf(v___x_1908_, v___x_1911_);
                                        if v___x_1912_ == 0 {
                                            v___x_1913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11;
                                            v___x_1914_ =
                                                l_Lean_Expr_isConstOf(v___x_1908_, v___x_1913_);
                                            if v___x_1914_ == 0 {
                                                v___x_1915_ = l_Lean_Expr_isApp(v___x_1908_);
                                                if v___x_1915_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_1908_);
                                                    crate::leanh::lean_dec_ref(v_arg_1907_);
                                                    crate::leanh::lean_dec_ref(v_arg_1901_);
                                                    crate::leanh::lean_dec_ref(v_arg_1897_);
                                                    v___x_1916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                    return v___x_1916_;
                                                } else {
                                                    v___x_1917_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1908_,
                                                    );
                                                    v___x_1918_ = l_Lean_Expr_isApp(v___x_1917_);
                                                    if v___x_1918_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_1917_);
                                                        crate::leanh::lean_dec_ref(v_arg_1907_);
                                                        crate::leanh::lean_dec_ref(v_arg_1901_);
                                                        crate::leanh::lean_dec_ref(v_arg_1897_);
                                                        v___x_1919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                        return v___x_1919_;
                                                    } else {
                                                        v___x_1920_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_1917_,
                                                            );
                                                        v___x_1921_ =
                                                            l_Lean_Expr_isApp(v___x_1920_);
                                                        if v___x_1921_ == 0 {
                                                            crate::leanh::lean_dec_ref(v___x_1920_);
                                                            crate::leanh::lean_dec_ref(v_arg_1907_);
                                                            crate::leanh::lean_dec_ref(v_arg_1901_);
                                                            crate::leanh::lean_dec_ref(v_arg_1897_);
                                                            v___x_1922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                            return v___x_1922_;
                                                        } else {
                                                            v___x_1923_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_1920_,
                                                                );
                                                            v___x_1924_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14;
                                                            v___x_1925_ = l_Lean_Expr_isConstOf(
                                                                v___x_1923_,
                                                                v___x_1924_,
                                                            );
                                                            if v___x_1925_ == 0 {
                                                                v___x_1926_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17;
                                                                v___x_1927_ = l_Lean_Expr_isConstOf(
                                                                    v___x_1923_,
                                                                    v___x_1926_,
                                                                );
                                                                if v___x_1927_ == 0 {
                                                                    v___x_1928_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20;
                                                                    v___x_1929_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_1923_,
                                                                            v___x_1928_,
                                                                        );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_1923_,
                                                                    );
                                                                    if v___x_1929_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1907_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1901_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1897_,
                                                                        );
                                                                        v___x_1930_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                        return v___x_1930_;
                                                                    } else {
                                                                        v___x_1931_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                        if crate::leanh::lean_obj_tag(v___x_1931_) == 0 {
v_a_1932_ = crate::leanh::lean_ctor_get(v___x_1931_, 0);
crate::leanh::lean_inc(v_a_1932_);
crate::leanh::lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1932_, v_arg_1907_);
crate::leanh::lean_dec_ref(v_arg_1907_);
crate::leanh::lean_dec(v_a_1932_);
if v___x_1933_ == 0 {
crate::leanh::lean_dec_ref(v_arg_1901_);
crate::leanh::lean_dec_ref(v_arg_1897_);
v___x_1934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
return v___x_1934_;
} else {
crate::leanh::lean_dec_ref(v_e_1879_);
crate::leanh::lean_inc(v_generation_1878_);
v___x_1935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1901_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if crate::leanh::lean_obj_tag(v___x_1935_) == 0 {
v_a_1936_ = crate::leanh::lean_ctor_get(v___x_1935_, 0);
crate::leanh::lean_inc(v_a_1936_);
crate::leanh::lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if crate::leanh::lean_obj_tag(v___x_1937_) == 0 {
v_a_1938_ = crate::leanh::lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1946_ = (!crate::leanh::lean_is_exclusive(v___x_1937_)) as u8;
if v_isSharedCheck_1946_ == 0 {
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1946_;
state = 1; continue;
} else {
crate::leanh::lean_inc(v_a_1938_);
crate::leanh::lean_dec(v___x_1937_);
v___x_1940_ = crate::leanh::lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1946_;
state = 1; continue;
}
} else {
crate::leanh::lean_dec(v_a_1936_);
return v___x_1937_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1897_);
crate::leanh::lean_dec(v_generation_1878_);
return v___x_1935_;
}
}
} else {
crate::leanh::lean_dec_ref(v_arg_1907_);
crate::leanh::lean_dec_ref(v_arg_1901_);
crate::leanh::lean_dec_ref(v_arg_1897_);
crate::leanh::lean_dec_ref(v_e_1879_);
crate::leanh::lean_dec(v_generation_1878_);
v_a_1947_ = crate::leanh::lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1954_ = (!crate::leanh::lean_is_exclusive(v___x_1931_)) as u8;
if v_isSharedCheck_1954_ == 0 {
v___x_1949_ = v___x_1931_;
v_isShared_1950_ = v_isSharedCheck_1954_;
state = 3; continue;
} else {
crate::leanh::lean_inc(v_a_1947_);
crate::leanh::lean_dec(v___x_1931_);
v___x_1949_ = crate::leanh::lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
state = 3; continue;
}
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_1923_,
                                                                    );
                                                                    v___x_1955_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_1955_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_1956_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1956_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_1955_, 1);
                                                                        v___x_1957_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_1956_, v_arg_1907_);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1907_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_1956_,
                                                                        );
                                                                        if v___x_1957_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_1901_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1897_);
                                                                            v___x_1958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                            return v___x_1958_;
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v_e_1879_);
                                                                            crate::leanh::lean_inc(
                                                                                v_generation_1878_,
                                                                            );
                                                                            v___x_1959_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1901_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                            if crate::leanh::lean_obj_tag(v___x_1959_) == 0 {
v_a_1960_ = crate::leanh::lean_ctor_get(v___x_1959_, 0);
crate::leanh::lean_inc(v_a_1960_);
crate::leanh::lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if crate::leanh::lean_obj_tag(v___x_1961_) == 0 {
v_a_1962_ = crate::leanh::lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1970_ = (!crate::leanh::lean_is_exclusive(v___x_1961_)) as u8;
if v_isSharedCheck_1970_ == 0 {
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1970_;
state = 5; continue;
} else {
crate::leanh::lean_inc(v_a_1962_);
crate::leanh::lean_dec(v___x_1961_);
v___x_1964_ = crate::leanh::lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
state = 5; continue;
}
} else {
crate::leanh::lean_dec(v_a_1960_);
return v___x_1961_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1897_);
crate::leanh::lean_dec(v_generation_1878_);
return v___x_1959_;
}
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1907_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1901_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1897_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_1879_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_generation_1878_,
                                                                        );
                                                                        v_a_1971_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                                                                        v_isSharedCheck_1978_ = (!crate::leanh::lean_is_exclusive(v___x_1955_)) as u8;
                                                                        if v_isSharedCheck_1978_
                                                                            == 0
                                                                        {
                                                                            v___x_1973_ =
                                                                                v___x_1955_;
                                                                            v_isShared_1974_ = v_isSharedCheck_1978_;
                                                                            state = 7;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_1971_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1955_,
                                                                            );
                                                                            v___x_1973_ = crate::leanh::lean_box(0);
                                                                            v_isShared_1974_ = v_isSharedCheck_1978_;
                                                                            state = 7;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_1923_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_generation_1878_,
                                                                );
                                                                v___x_1979_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_1878_, v_arg_1907_, v_arg_1901_, v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1907_,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_1979_,
                                                                ) == 0
                                                                {
                                                                    v_a_1980_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1979_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1989_ = (!crate::leanh::lean_is_exclusive(v___x_1979_)) as u8;
                                                                    if v_isSharedCheck_1989_ == 0 {
                                                                        v___x_1982_ = v___x_1979_;
                                                                        v_isShared_1983_ =
                                                                            v_isSharedCheck_1989_;
                                                                        state = 9;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1980_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1979_,
                                                                        );
                                                                        v___x_1982_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1983_ =
                                                                            v_isSharedCheck_1989_;
                                                                        state = 9;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_1879_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_generation_1878_,
                                                                    );
                                                                    v_a_1990_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1979_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1997_ = (!crate::leanh::lean_is_exclusive(v___x_1979_)) as u8;
                                                                    if v_isSharedCheck_1997_ == 0 {
                                                                        v___x_1992_ = v___x_1979_;
                                                                        v_isShared_1993_ =
                                                                            v_isSharedCheck_1997_;
                                                                        state = 11;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1990_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1979_,
                                                                        );
                                                                        v___x_1992_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1993_ =
                                                                            v_isSharedCheck_1997_;
                                                                        state = 11;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_1908_);
                                                crate::leanh::lean_dec_ref(v_arg_1907_);
                                                v___x_1998_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                if crate::leanh::lean_obj_tag(v___x_1998_) == 0 {
                                                    v_a_1999_ =
                                                        crate::leanh::lean_ctor_get(v___x_1998_, 0);
                                                    crate::leanh::lean_inc(v_a_1999_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1998_,
                                                        1,
                                                    );
                                                    v___x_2000_ =
                                                        l_Lean_Meta_Grind_Arith_Linear_isNegInst(
                                                            v_a_1999_,
                                                            v_arg_1901_,
                                                        );
                                                    crate::leanh::lean_dec_ref(v_arg_1901_);
                                                    crate::leanh::lean_dec(v_a_1999_);
                                                    if v___x_2000_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_1897_);
                                                        v___x_2001_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                        return v___x_2001_;
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_e_1879_);
                                                        v___x_2002_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                        if crate::leanh::lean_obj_tag(v___x_2002_)
                                                            == 0
                                                        {
                                                            v_a_2003_ = crate::leanh::lean_ctor_get(
                                                                v___x_2002_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2011_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2002_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2011_ == 0 {
                                                                v___x_2005_ = v___x_2002_;
                                                                v_isShared_2006_ =
                                                                    v_isSharedCheck_2011_;
                                                                state = 13;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2003_);
                                                                crate::leanh::lean_dec(v___x_2002_);
                                                                v___x_2005_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2006_ =
                                                                    v_isSharedCheck_2011_;
                                                                state = 13;
                                                                continue;
                                                            }
                                                        } else {
                                                            return v___x_2002_;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_arg_1901_);
                                                    crate::leanh::lean_dec_ref(v_arg_1897_);
                                                    crate::leanh::lean_dec_ref(v_e_1879_);
                                                    crate::leanh::lean_dec(v_generation_1878_);
                                                    v_a_2012_ =
                                                        crate::leanh::lean_ctor_get(v___x_1998_, 0);
                                                    v_isSharedCheck_2019_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_1998_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2019_ == 0 {
                                                        v___x_2014_ = v___x_1998_;
                                                        v_isShared_2015_ = v_isSharedCheck_2019_;
                                                        state = 15;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2012_);
                                                        crate::leanh::lean_dec(v___x_1998_);
                                                        v___x_2014_ = crate::leanh::lean_box(0);
                                                        v_isShared_2015_ = v_isSharedCheck_2019_;
                                                        state = 15;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1908_);
                                            crate::leanh::lean_dec_ref(v_arg_1907_);
                                            crate::leanh::lean_dec_ref(v_arg_1901_);
                                            crate::leanh::lean_dec_ref(v_arg_1897_);
                                            crate::leanh::lean_inc_ref(v_e_1879_);
                                            v___x_2020_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                            if crate::leanh::lean_obj_tag(v___x_2020_) == 0 {
                                                v_a_2021_ =
                                                    crate::leanh::lean_ctor_get(v___x_2020_, 0);
                                                v_isSharedCheck_2031_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2020_))
                                                        as u8;
                                                if v_isSharedCheck_2031_ == 0 {
                                                    v___x_2023_ = v___x_2020_;
                                                    v_isShared_2024_ = v_isSharedCheck_2031_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2021_);
                                                    crate::leanh::lean_dec(v___x_2020_);
                                                    v___x_2023_ = crate::leanh::lean_box(0);
                                                    v_isShared_2024_ = v_isSharedCheck_2031_;
                                                    state = 17;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_e_1879_);
                                                crate::leanh::lean_dec(v_generation_1878_);
                                                v_a_2032_ =
                                                    crate::leanh::lean_ctor_get(v___x_2020_, 0);
                                                v_isSharedCheck_2039_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2020_))
                                                        as u8;
                                                if v_isSharedCheck_2039_ == 0 {
                                                    v___x_2034_ = v___x_2020_;
                                                    v_isShared_2035_ = v_isSharedCheck_2039_;
                                                    state = 19;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2032_);
                                                    crate::leanh::lean_dec(v___x_2020_);
                                                    v___x_2034_ = crate::leanh::lean_box(0);
                                                    v_isShared_2035_ = v_isSharedCheck_2039_;
                                                    state = 19;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_1908_);
                                        crate::leanh::lean_dec_ref(v_arg_1907_);
                                        crate::leanh::lean_dec_ref(v_arg_1901_);
                                        v___x_2040_ =
                                            l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                                v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_,
                                                v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_,
                                                v_a_1888_, v_a_1889_, v_a_1890_,
                                            );
                                        if crate::leanh::lean_obj_tag(v___x_2040_) == 0 {
                                            v_a_2041_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                                            crate::leanh::lean_inc(v_a_2041_);
                                            crate::leanh::lean_dec_ref_known(v___x_2040_, 1);
                                            v_orderedRingInst_x3f_2055_ =
                                                crate::leanh::lean_ctor_get(v_a_2041_, 14);
                                            crate::leanh::lean_inc(v_orderedRingInst_x3f_2055_);
                                            crate::leanh::lean_dec(v_a_2041_);
                                            if crate::leanh::lean_obj_tag(
                                                v_orderedRingInst_x3f_2055_,
                                            ) == 0
                                            {
                                                v___y_2043_ = v___x_1904_;
                                                state = 21;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(
                                                    v_orderedRingInst_x3f_2055_,
                                                    1,
                                                );
                                                v___y_2043_ = v___x_1910_;
                                                state = 21;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_arg_1897_);
                                            crate::leanh::lean_dec_ref(v_e_1879_);
                                            crate::leanh::lean_dec(v_generation_1878_);
                                            v_a_2056_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                                            v_isSharedCheck_2063_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2040_))
                                                    as u8;
                                            if v_isSharedCheck_2063_ == 0 {
                                                v___x_2058_ = v___x_2040_;
                                                v_isShared_2059_ = v_isSharedCheck_2063_;
                                                state = 24;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2056_);
                                                crate::leanh::lean_dec(v___x_2040_);
                                                v___x_2058_ = crate::leanh::lean_box(0);
                                                v_isShared_2059_ = v_isSharedCheck_2063_;
                                                state = 24;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1902_);
                                crate::leanh::lean_dec_ref(v_arg_1901_);
                                v___x_2064_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                    v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_,
                                    v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_,
                                    v_a_1890_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2064_) == 0 {
                                    v_a_2065_ = crate::leanh::lean_ctor_get(v___x_2064_, 0);
                                    v_isSharedCheck_2075_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2064_)) as u8;
                                    if v_isSharedCheck_2075_ == 0 {
                                        v___x_2067_ = v___x_2064_;
                                        v_isShared_2068_ = v_isSharedCheck_2075_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2065_);
                                        crate::leanh::lean_dec(v___x_2064_);
                                        v___x_2067_ = crate::leanh::lean_box(0);
                                        v_isShared_2068_ = v_isSharedCheck_2075_;
                                        state = 26;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_1897_);
                                    crate::leanh::lean_dec_ref(v_e_1879_);
                                    crate::leanh::lean_dec(v_generation_1878_);
                                    v_a_2076_ = crate::leanh::lean_ctor_get(v___x_2064_, 0);
                                    v_isSharedCheck_2083_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2064_)) as u8;
                                    if v_isSharedCheck_2083_ == 0 {
                                        v___x_2078_ = v___x_2064_;
                                        v_isShared_2079_ = v_isSharedCheck_2083_;
                                        state = 28;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2076_);
                                        crate::leanh::lean_dec(v___x_2064_);
                                        v___x_2078_ = crate::leanh::lean_box(0);
                                        v_isShared_2079_ = v_isSharedCheck_2083_;
                                        state = 28;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1879_);
                    crate::leanh::lean_dec(v_generation_1878_);
                    v_a_2084_ = crate::leanh::lean_ctor_get(v___x_1892_, 0);
                    v_isSharedCheck_2091_ = (!crate::leanh::lean_is_exclusive(v___x_1892_)) as u8;
                    if v_isSharedCheck_2091_ == 0 {
                        v___x_2086_ = v___x_1892_;
                        v_isShared_2087_ = v_isSharedCheck_2091_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2084_);
                        crate::leanh::lean_dec(v___x_1892_);
                        v___x_2086_ = crate::leanh::lean_box(0);
                        v_isShared_2087_ = v_isSharedCheck_2091_;
                        state = 30;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1942_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1942_, 0, v_a_1936_);
                crate::leanh::lean_ctor_set(v___x_1942_, 1, v_a_1938_);
                if v_isShared_1941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1940_, 0, v___x_1942_);
                    v___x_1944_ = v___x_1940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
                    v___x_1944_ = v_reuseFailAlloc_1945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1944_;
            }
            3 => {
                if v_isShared_1950_ == 0 {
                    v___x_1952_ = v___x_1949_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
                    v___x_1952_ = v_reuseFailAlloc_1953_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1952_;
            }
            5 => {
                v___x_1966_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1966_, 0, v_a_1960_);
                crate::leanh::lean_ctor_set(v___x_1966_, 1, v_a_1962_);
                if v_isShared_1965_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1964_, 0, v___x_1966_);
                    v___x_1968_ = v___x_1964_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
                    v___x_1968_ = v_reuseFailAlloc_1969_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1968_;
            }
            7 => {
                if v_isShared_1974_ == 0 {
                    v___x_1976_ = v___x_1973_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
                    v___x_1976_ = v_reuseFailAlloc_1977_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1976_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_1980_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_1879_);
                    crate::leanh::lean_dec(v_generation_1878_);
                    v_val_1984_ = crate::leanh::lean_ctor_get(v_a_1980_, 0);
                    crate::leanh::lean_inc(v_val_1984_);
                    crate::leanh::lean_dec_ref_known(v_a_1980_, 1);
                    if v_isShared_1983_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1982_, 0, v_val_1984_);
                        v___x_1986_ = v___x_1982_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_val_1984_);
                        v___x_1986_ = v_reuseFailAlloc_1987_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1982_);
                    crate::leanh::lean_dec(v_a_1980_);
                    v___x_1988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    return v___x_1988_;
                }
            }
            10 => {
                return v___x_1986_;
            }
            11 => {
                if v_isShared_1993_ == 0 {
                    v___x_1995_ = v___x_1992_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1996_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
                    v___x_1995_ = v_reuseFailAlloc_1996_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1995_;
            }
            13 => {
                v___x_2007_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2007_, 0, v_a_2003_);
                if v_isShared_2006_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2005_, 0, v___x_2007_);
                    v___x_2009_ = v___x_2005_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2009_;
            }
            15 => {
                if v_isShared_2015_ == 0 {
                    v___x_2017_ = v___x_2014_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2018_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2017_;
            }
            17 => {
                v___x_2025_ = (crate::leanh::lean_unbox(v_a_2021_) as u8);
                crate::leanh::lean_dec(v_a_2021_);
                if v___x_2025_ == 0 {
                    crate::leanh::lean_del_object(v___x_2023_);
                    v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    return v___x_2026_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_1879_);
                    crate::leanh::lean_dec(v_generation_1878_);
                    v___x_2027_ = crate::leanh::lean_box(0);
                    if v_isShared_2024_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2023_, 0, v___x_2027_);
                        v___x_2029_ = v___x_2023_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_2030_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
                        v___x_2029_ = v_reuseFailAlloc_2030_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                return v___x_2029_;
            }
            19 => {
                if v_isShared_2035_ == 0 {
                    v___x_2037_ = v___x_2034_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
                    v___x_2037_ = v_reuseFailAlloc_2038_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2037_;
            }
            21 => {
                if v___y_2043_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1897_);
                    v___x_2044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    return v___x_2044_;
                } else {
                    v___x_2045_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    if crate::leanh::lean_obj_tag(v___x_2045_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2045_, 1);
                        v___x_2046_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                        return v___x_2046_;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1879_);
                        crate::leanh::lean_dec(v_generation_1878_);
                        v_a_2047_ = crate::leanh::lean_ctor_get(v___x_2045_, 0);
                        v_isSharedCheck_2054_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2045_)) as u8;
                        if v_isSharedCheck_2054_ == 0 {
                            v___x_2049_ = v___x_2045_;
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2047_);
                            crate::leanh::lean_dec(v___x_2045_);
                            v___x_2049_ = crate::leanh::lean_box(0);
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            22 => {
                if v_isShared_2050_ == 0 {
                    v___x_2052_ = v___x_2049_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
                    v___x_2052_ = v_reuseFailAlloc_2053_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2052_;
            }
            24 => {
                if v_isShared_2059_ == 0 {
                    v___x_2061_ = v___x_2058_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
                    v___x_2061_ = v_reuseFailAlloc_2062_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2061_;
            }
            26 => {
                v___x_2069_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_2065_, v_arg_1897_);
                crate::leanh::lean_dec_ref(v_arg_1897_);
                crate::leanh::lean_dec(v_a_2065_);
                if v___x_2069_ == 0 {
                    crate::leanh::lean_del_object(v___x_2067_);
                    v___x_2070_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    return v___x_2070_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_1879_);
                    crate::leanh::lean_dec(v_generation_1878_);
                    v___x_2071_ = crate::leanh::lean_box(0);
                    if v_isShared_2068_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2067_, 0, v___x_2071_);
                        v___x_2073_ = v___x_2067_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
                        v___x_2073_ = v_reuseFailAlloc_2074_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                return v___x_2073_;
            }
            28 => {
                if v_isShared_2079_ == 0 {
                    v___x_2081_ = v___x_2078_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
                    v___x_2081_ = v_reuseFailAlloc_2082_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2081_;
            }
            30 => {
                if v_isShared_2087_ == 0 {
                    v___x_2089_ = v___x_2086_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
                    v___x_2089_ = v_reuseFailAlloc_2090_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(
    mut v_generation_2092_: *mut crate::leanh::LeanObject,
    mut v_i_2093_: *mut crate::leanh::LeanObject,
    mut v_a_2094_: *mut crate::leanh::LeanObject,
    mut v_b_2095_: *mut crate::leanh::LeanObject,
    mut v_a_2096_: *mut crate::leanh::LeanObject,
    mut v_a_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
    mut v_a_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: u8 = 0;
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: u8 = 0;
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2125_: u8 = 0;
    let mut v_val_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2129_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2134_: u8 = 0;
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2142_: u8 = 0;
    let mut v_a_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_isSharedCheck_2151_: u8 = 0;
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut v_a_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2160_: u8 = 0;
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut v_isSharedCheck_2165_: u8 = 0;
    let mut v_a_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2169_: u8 = 0;
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2178_: u8 = 0;
    let mut v_val_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2195_: u8 = 0;
    let mut v_a_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_a_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_a_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2108_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_,
                    v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_,
                );
                if crate::leanh::lean_obj_tag(v___x_2108_) == 0 {
                    v_a_2109_ = crate::leanh::lean_ctor_get(v___x_2108_, 0);
                    crate::leanh::lean_inc(v_a_2109_);
                    crate::leanh::lean_dec_ref_known(v___x_2108_, 1);
                    v___x_2110_ =
                        l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_2109_, v_i_2093_);
                    crate::leanh::lean_dec(v_a_2109_);
                    if v___x_2110_ == 0 {
                        v___x_2111_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                            v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_,
                            v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2111_) == 0 {
                            v_a_2112_ = crate::leanh::lean_ctor_get(v___x_2111_, 0);
                            v_isSharedCheck_2165_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2111_)) as u8;
                            if v_isSharedCheck_2165_ == 0 {
                                v___x_2114_ = v___x_2111_;
                                v_isShared_2115_ = v_isSharedCheck_2165_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2112_);
                                crate::leanh::lean_dec(v___x_2111_);
                                v___x_2114_ = crate::leanh::lean_box(0);
                                v_isShared_2115_ = v_isSharedCheck_2165_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2095_);
                            crate::leanh::lean_dec_ref(v_a_2094_);
                            crate::leanh::lean_dec(v_generation_2092_);
                            v_a_2166_ = crate::leanh::lean_ctor_get(v___x_2111_, 0);
                            v_isSharedCheck_2173_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2111_)) as u8;
                            if v_isSharedCheck_2173_ == 0 {
                                v___x_2168_ = v___x_2111_;
                                v_isShared_2169_ = v_isSharedCheck_2173_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2166_);
                                crate::leanh::lean_dec(v___x_2111_);
                                v___x_2168_ = crate::leanh::lean_box(0);
                                v_isShared_2169_ = v_isSharedCheck_2173_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v___x_2174_ = l_Lean_Meta_getIntValue_x3f(
                            v_a_2094_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2174_) == 0 {
                            v_a_2175_ = crate::leanh::lean_ctor_get(v___x_2174_, 0);
                            v_isSharedCheck_2209_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2174_)) as u8;
                            if v_isSharedCheck_2209_ == 0 {
                                v___x_2177_ = v___x_2174_;
                                v_isShared_2178_ = v_isSharedCheck_2209_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2175_);
                                crate::leanh::lean_dec(v___x_2174_);
                                v___x_2177_ = crate::leanh::lean_box(0);
                                v_isShared_2178_ = v_isSharedCheck_2209_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2095_);
                            crate::leanh::lean_dec(v_generation_2092_);
                            v_a_2210_ = crate::leanh::lean_ctor_get(v___x_2174_, 0);
                            v_isSharedCheck_2217_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2174_)) as u8;
                            if v_isSharedCheck_2217_ == 0 {
                                v___x_2212_ = v___x_2174_;
                                v_isShared_2213_ = v_isSharedCheck_2217_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2210_);
                                crate::leanh::lean_dec(v___x_2174_);
                                v___x_2212_ = crate::leanh::lean_box(0);
                                v_isShared_2213_ = v_isSharedCheck_2217_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2095_);
                    crate::leanh::lean_dec_ref(v_a_2094_);
                    crate::leanh::lean_dec(v_generation_2092_);
                    v_a_2218_ = crate::leanh::lean_ctor_get(v___x_2108_, 0);
                    v_isSharedCheck_2225_ = (!crate::leanh::lean_is_exclusive(v___x_2108_)) as u8;
                    if v_isSharedCheck_2225_ == 0 {
                        v___x_2220_ = v___x_2108_;
                        v_isShared_2221_ = v_isSharedCheck_2225_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2218_);
                        crate::leanh::lean_dec(v___x_2108_);
                        v___x_2220_ = crate::leanh::lean_box(0);
                        v_isShared_2221_ = v_isSharedCheck_2225_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2116_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_a_2112_, v_i_2093_);
                crate::leanh::lean_dec(v_a_2112_);
                if v___x_2116_ == 0 {
                    crate::leanh::lean_dec_ref(v_b_2095_);
                    crate::leanh::lean_dec_ref(v_a_2094_);
                    crate::leanh::lean_dec(v_generation_2092_);
                    v___x_2117_ = crate::leanh::lean_box(0);
                    if v_isShared_2115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2114_, 0, v___x_2117_);
                        v___x_2119_ = v___x_2114_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
                        v___x_2119_ = v_reuseFailAlloc_2120_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2114_);
                    v___x_2121_ = l_Lean_Meta_getNatValue_x3f(
                        v_a_2094_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_,
                    );
                    crate::leanh::lean_dec_ref(v_a_2094_);
                    if crate::leanh::lean_obj_tag(v___x_2121_) == 0 {
                        v_a_2122_ = crate::leanh::lean_ctor_get(v___x_2121_, 0);
                        v_isSharedCheck_2156_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2121_)) as u8;
                        if v_isSharedCheck_2156_ == 0 {
                            v___x_2124_ = v___x_2121_;
                            v_isShared_2125_ = v_isSharedCheck_2156_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2122_);
                            crate::leanh::lean_dec(v___x_2121_);
                            v___x_2124_ = crate::leanh::lean_box(0);
                            v_isShared_2125_ = v_isSharedCheck_2156_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2095_);
                        crate::leanh::lean_dec(v_generation_2092_);
                        v_a_2157_ = crate::leanh::lean_ctor_get(v___x_2121_, 0);
                        v_isSharedCheck_2164_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2121_)) as u8;
                        if v_isSharedCheck_2164_ == 0 {
                            v___x_2159_ = v___x_2121_;
                            v_isShared_2160_ = v_isSharedCheck_2164_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2157_);
                            crate::leanh::lean_dec(v___x_2121_);
                            v___x_2159_ = crate::leanh::lean_box(0);
                            v_isShared_2160_ = v_isSharedCheck_2164_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2119_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_2122_) == 1 {
                    crate::leanh::lean_del_object(v___x_2124_);
                    v_val_2126_ = crate::leanh::lean_ctor_get(v_a_2122_, 0);
                    v_isSharedCheck_2151_ = (!crate::leanh::lean_is_exclusive(v_a_2122_)) as u8;
                    if v_isSharedCheck_2151_ == 0 {
                        v___x_2128_ = v_a_2122_;
                        v_isShared_2129_ = v_isSharedCheck_2151_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2126_);
                        crate::leanh::lean_dec(v_a_2122_);
                        v___x_2128_ = crate::leanh::lean_box(0);
                        v_isShared_2129_ = v_isSharedCheck_2151_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2122_);
                    crate::leanh::lean_dec_ref(v_b_2095_);
                    crate::leanh::lean_dec(v_generation_2092_);
                    v___x_2152_ = crate::leanh::lean_box(0);
                    if v_isShared_2125_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2124_, 0, v___x_2152_);
                        v___x_2154_ = v___x_2124_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
                        v___x_2154_ = v_reuseFailAlloc_2155_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2130_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2092_, v_b_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
                if crate::leanh::lean_obj_tag(v___x_2130_) == 0 {
                    v_a_2131_ = crate::leanh::lean_ctor_get(v___x_2130_, 0);
                    v_isSharedCheck_2142_ = (!crate::leanh::lean_is_exclusive(v___x_2130_)) as u8;
                    if v_isSharedCheck_2142_ == 0 {
                        v___x_2133_ = v___x_2130_;
                        v_isShared_2134_ = v_isSharedCheck_2142_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2131_);
                        crate::leanh::lean_dec(v___x_2130_);
                        v___x_2133_ = crate::leanh::lean_box(0);
                        v_isShared_2134_ = v_isSharedCheck_2142_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2128_);
                    crate::leanh::lean_dec(v_val_2126_);
                    v_a_2143_ = crate::leanh::lean_ctor_get(v___x_2130_, 0);
                    v_isSharedCheck_2150_ = (!crate::leanh::lean_is_exclusive(v___x_2130_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v___x_2145_ = v___x_2130_;
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2143_);
                        crate::leanh::lean_dec(v___x_2130_);
                        v___x_2145_ = crate::leanh::lean_box(0);
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2135_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2135_, 0, v_val_2126_);
                crate::leanh::lean_ctor_set(v___x_2135_, 1, v_a_2131_);
                if v_isShared_2129_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2128_, 0, v___x_2135_);
                    v___x_2137_ = v___x_2128_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2135_);
                    v___x_2137_ = v_reuseFailAlloc_2141_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2134_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2137_);
                    v___x_2139_ = v___x_2133_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
                    v___x_2139_ = v_reuseFailAlloc_2140_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2139_;
            }
            8 => {
                if v_isShared_2146_ == 0 {
                    v___x_2148_ = v___x_2145_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2148_;
            }
            10 => {
                return v___x_2154_;
            }
            11 => {
                if v_isShared_2160_ == 0 {
                    v___x_2162_ = v___x_2159_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
                    v___x_2162_ = v_reuseFailAlloc_2163_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2162_;
            }
            13 => {
                if v_isShared_2169_ == 0 {
                    v___x_2171_ = v___x_2168_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
                    v___x_2171_ = v_reuseFailAlloc_2172_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2171_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v_a_2175_) == 1 {
                    crate::leanh::lean_del_object(v___x_2177_);
                    v_val_2179_ = crate::leanh::lean_ctor_get(v_a_2175_, 0);
                    v_isSharedCheck_2204_ = (!crate::leanh::lean_is_exclusive(v_a_2175_)) as u8;
                    if v_isSharedCheck_2204_ == 0 {
                        v___x_2181_ = v_a_2175_;
                        v_isShared_2182_ = v_isSharedCheck_2204_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2179_);
                        crate::leanh::lean_dec(v_a_2175_);
                        v___x_2181_ = crate::leanh::lean_box(0);
                        v_isShared_2182_ = v_isSharedCheck_2204_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2175_);
                    crate::leanh::lean_dec_ref(v_b_2095_);
                    crate::leanh::lean_dec(v_generation_2092_);
                    v___x_2205_ = crate::leanh::lean_box(0);
                    if v_isShared_2178_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2177_, 0, v___x_2205_);
                        v___x_2207_ = v___x_2177_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_2208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
                        v___x_2207_ = v_reuseFailAlloc_2208_;
                        state = 22;
                        continue;
                    }
                }
            }
            16 => {
                v___x_2183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2092_, v_b_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
                if crate::leanh::lean_obj_tag(v___x_2183_) == 0 {
                    v_a_2184_ = crate::leanh::lean_ctor_get(v___x_2183_, 0);
                    v_isSharedCheck_2195_ = (!crate::leanh::lean_is_exclusive(v___x_2183_)) as u8;
                    if v_isSharedCheck_2195_ == 0 {
                        v___x_2186_ = v___x_2183_;
                        v_isShared_2187_ = v_isSharedCheck_2195_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2184_);
                        crate::leanh::lean_dec(v___x_2183_);
                        v___x_2186_ = crate::leanh::lean_box(0);
                        v_isShared_2187_ = v_isSharedCheck_2195_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2181_);
                    crate::leanh::lean_dec(v_val_2179_);
                    v_a_2196_ = crate::leanh::lean_ctor_get(v___x_2183_, 0);
                    v_isSharedCheck_2203_ = (!crate::leanh::lean_is_exclusive(v___x_2183_)) as u8;
                    if v_isSharedCheck_2203_ == 0 {
                        v___x_2198_ = v___x_2183_;
                        v_isShared_2199_ = v_isSharedCheck_2203_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2196_);
                        crate::leanh::lean_dec(v___x_2183_);
                        v___x_2198_ = crate::leanh::lean_box(0);
                        v_isShared_2199_ = v_isSharedCheck_2203_;
                        state = 20;
                        continue;
                    }
                }
            }
            17 => {
                v___x_2188_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2188_, 0, v_val_2179_);
                crate::leanh::lean_ctor_set(v___x_2188_, 1, v_a_2184_);
                if v_isShared_2182_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2188_);
                    v___x_2190_ = v___x_2181_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2188_);
                    v___x_2190_ = v_reuseFailAlloc_2194_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2186_, 0, v___x_2190_);
                    v___x_2192_ = v___x_2186_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2192_;
            }
            20 => {
                if v_isShared_2199_ == 0 {
                    v___x_2201_ = v___x_2198_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
                    v___x_2201_ = v_reuseFailAlloc_2202_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2201_;
            }
            22 => {
                return v___x_2207_;
            }
            23 => {
                if v_isShared_2213_ == 0 {
                    v___x_2215_ = v___x_2212_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
                    v___x_2215_ = v_reuseFailAlloc_2216_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2215_;
            }
            25 => {
                if v_isShared_2221_ == 0 {
                    v___x_2223_ = v___x_2220_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
                    v___x_2223_ = v_reuseFailAlloc_2224_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul___boxed(
    mut v_generation_2226_: *mut crate::leanh::LeanObject,
    mut v_i_2227_: *mut crate::leanh::LeanObject,
    mut v_a_2228_: *mut crate::leanh::LeanObject,
    mut v_b_2229_: *mut crate::leanh::LeanObject,
    mut v_a_2230_: *mut crate::leanh::LeanObject,
    mut v_a_2231_: *mut crate::leanh::LeanObject,
    mut v_a_2232_: *mut crate::leanh::LeanObject,
    mut v_a_2233_: *mut crate::leanh::LeanObject,
    mut v_a_2234_: *mut crate::leanh::LeanObject,
    mut v_a_2235_: *mut crate::leanh::LeanObject,
    mut v_a_2236_: *mut crate::leanh::LeanObject,
    mut v_a_2237_: *mut crate::leanh::LeanObject,
    mut v_a_2238_: *mut crate::leanh::LeanObject,
    mut v_a_2239_: *mut crate::leanh::LeanObject,
    mut v_a_2240_: *mut crate::leanh::LeanObject,
    mut v_a_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2242_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_2226_, v_i_2227_, v_a_2228_, v_b_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
    crate::leanh::lean_dec(v_a_2240_);
    crate::leanh::lean_dec_ref(v_a_2239_);
    crate::leanh::lean_dec(v_a_2238_);
    crate::leanh::lean_dec_ref(v_a_2237_);
    crate::leanh::lean_dec(v_a_2236_);
    crate::leanh::lean_dec_ref(v_a_2235_);
    crate::leanh::lean_dec(v_a_2234_);
    crate::leanh::lean_dec_ref(v_a_2233_);
    crate::leanh::lean_dec(v_a_2232_);
    crate::leanh::lean_dec(v_a_2231_);
    crate::leanh::lean_dec(v_a_2230_);
    crate::leanh::lean_dec_ref(v_i_2227_);
    return v_res_2242_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___boxed(
    mut v_generation_2243_: *mut crate::leanh::LeanObject,
    mut v_e_2244_: *mut crate::leanh::LeanObject,
    mut v_a_2245_: *mut crate::leanh::LeanObject,
    mut v_a_2246_: *mut crate::leanh::LeanObject,
    mut v_a_2247_: *mut crate::leanh::LeanObject,
    mut v_a_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
    mut v_a_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v_a_2254_: *mut crate::leanh::LeanObject,
    mut v_a_2255_: *mut crate::leanh::LeanObject,
    mut v_a_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2257_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2243_, v_e_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_);
    crate::leanh::lean_dec(v_a_2255_);
    crate::leanh::lean_dec_ref(v_a_2254_);
    crate::leanh::lean_dec(v_a_2253_);
    crate::leanh::lean_dec_ref(v_a_2252_);
    crate::leanh::lean_dec(v_a_2251_);
    crate::leanh::lean_dec_ref(v_a_2250_);
    crate::leanh::lean_dec(v_a_2249_);
    crate::leanh::lean_dec_ref(v_a_2248_);
    crate::leanh::lean_dec(v_a_2247_);
    crate::leanh::lean_dec(v_a_2246_);
    crate::leanh::lean_dec(v_a_2245_);
    return v_res_2257_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
    mut v_e_2260_: *mut crate::leanh::LeanObject,
    mut v_skipVar_2261_: u8,
    mut v_generation_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
    mut v_a_2264_: *mut crate::leanh::LeanObject,
    mut v_a_2265_: *mut crate::leanh::LeanObject,
    mut v_a_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
    mut v_a_2269_: *mut crate::leanh::LeanObject,
    mut v_a_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
    mut v_a_2272_: *mut crate::leanh::LeanObject,
    mut v_a_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: u8 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: u8 = 0;
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: u8 = 0;
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: u8 = 0;
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_a_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_a_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2346_: u8 = 0;
    let mut v_a_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2350_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2354_: u8 = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_a_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut v_a_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_a_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2391_: u8 = 0;
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2413_: u8 = 0;
    let mut v_a_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2417_: u8 = 0;
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut v_a_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2425_: u8 = 0;
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut v_a_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2445_: u8 = 0;
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2453_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2460_: u8 = 0;
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2464_: u8 = 0;
    let mut v_orderedRingInst_x3f_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: u8 = 0;
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2485_: u8 = 0;
    let mut v_a_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v_a_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2260_);
                v___x_2275_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2260_, v_a_2271_);
                if crate::leanh::lean_obj_tag(v___x_2275_) == 0 {
                    v_a_2276_ = crate::leanh::lean_ctor_get(v___x_2275_, 0);
                    crate::leanh::lean_inc(v_a_2276_);
                    crate::leanh::lean_dec_ref_known(v___x_2275_, 1);
                    v___x_2277_ = l_Lean_Expr_cleanupAnnotations(v_a_2276_);
                    v___x_2278_ = l_Lean_Expr_isApp(v___x_2277_);
                    if v___x_2278_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2277_);
                        v___x_2279_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                        return v___x_2279_;
                    } else {
                        v_arg_2280_ = crate::leanh::lean_ctor_get(v___x_2277_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2280_);
                        v___x_2281_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2277_);
                        v___x_2282_ = l_Lean_Expr_isApp(v___x_2281_);
                        if v___x_2282_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2281_);
                            crate::leanh::lean_dec_ref(v_arg_2280_);
                            v___x_2283_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                            return v___x_2283_;
                        } else {
                            v_arg_2284_ = crate::leanh::lean_ctor_get(v___x_2281_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2284_);
                            v___x_2285_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2281_);
                            v___x_2286_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2;
                            v___x_2287_ = l_Lean_Expr_isConstOf(v___x_2285_, v___x_2286_);
                            if v___x_2287_ == 0 {
                                v___x_2288_ = l_Lean_Expr_isApp(v___x_2285_);
                                if v___x_2288_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2285_);
                                    crate::leanh::lean_dec_ref(v_arg_2284_);
                                    crate::leanh::lean_dec_ref(v_arg_2280_);
                                    v___x_2289_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                    return v___x_2289_;
                                } else {
                                    v_arg_2290_ = crate::leanh::lean_ctor_get(v___x_2285_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2290_);
                                    v___x_2291_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2285_);
                                    v___x_2292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5;
                                    v___x_2293_ = l_Lean_Expr_isConstOf(v___x_2291_, v___x_2292_);
                                    if v___x_2293_ == 0 {
                                        v___x_2294_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8;
                                        v___x_2295_ =
                                            l_Lean_Expr_isConstOf(v___x_2291_, v___x_2294_);
                                        if v___x_2295_ == 0 {
                                            v___x_2296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11;
                                            v___x_2297_ =
                                                l_Lean_Expr_isConstOf(v___x_2291_, v___x_2296_);
                                            if v___x_2297_ == 0 {
                                                v___x_2298_ = l_Lean_Expr_isApp(v___x_2291_);
                                                if v___x_2298_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_2291_);
                                                    crate::leanh::lean_dec_ref(v_arg_2290_);
                                                    crate::leanh::lean_dec_ref(v_arg_2284_);
                                                    crate::leanh::lean_dec_ref(v_arg_2280_);
                                                    v___x_2299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                    return v___x_2299_;
                                                } else {
                                                    v___x_2300_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_2291_,
                                                    );
                                                    v___x_2301_ = l_Lean_Expr_isApp(v___x_2300_);
                                                    if v___x_2301_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_2300_);
                                                        crate::leanh::lean_dec_ref(v_arg_2290_);
                                                        crate::leanh::lean_dec_ref(v_arg_2284_);
                                                        crate::leanh::lean_dec_ref(v_arg_2280_);
                                                        v___x_2302_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                        return v___x_2302_;
                                                    } else {
                                                        v___x_2303_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_2300_,
                                                            );
                                                        v___x_2304_ =
                                                            l_Lean_Expr_isApp(v___x_2303_);
                                                        if v___x_2304_ == 0 {
                                                            crate::leanh::lean_dec_ref(v___x_2303_);
                                                            crate::leanh::lean_dec_ref(v_arg_2290_);
                                                            crate::leanh::lean_dec_ref(v_arg_2284_);
                                                            crate::leanh::lean_dec_ref(v_arg_2280_);
                                                            v___x_2305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                            return v___x_2305_;
                                                        } else {
                                                            v___x_2306_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_2303_,
                                                                );
                                                            v___x_2307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14;
                                                            v___x_2308_ = l_Lean_Expr_isConstOf(
                                                                v___x_2306_,
                                                                v___x_2307_,
                                                            );
                                                            if v___x_2308_ == 0 {
                                                                v___x_2309_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17;
                                                                v___x_2310_ = l_Lean_Expr_isConstOf(
                                                                    v___x_2306_,
                                                                    v___x_2309_,
                                                                );
                                                                if v___x_2310_ == 0 {
                                                                    v___x_2311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20;
                                                                    v___x_2312_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_2306_,
                                                                            v___x_2311_,
                                                                        );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_2306_,
                                                                    );
                                                                    if v___x_2312_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2290_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2284_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2280_,
                                                                        );
                                                                        v___x_2313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                        return v___x_2313_;
                                                                    } else {
                                                                        v___x_2314_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                        if crate::leanh::lean_obj_tag(v___x_2314_) == 0 {
v_a_2315_ = crate::leanh::lean_ctor_get(v___x_2314_, 0);
crate::leanh::lean_inc(v_a_2315_);
crate::leanh::lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_2315_, v_arg_2290_);
crate::leanh::lean_dec_ref(v_arg_2290_);
crate::leanh::lean_dec(v_a_2315_);
if v___x_2316_ == 0 {
crate::leanh::lean_dec_ref(v_arg_2284_);
crate::leanh::lean_dec_ref(v_arg_2280_);
v___x_2317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
return v___x_2317_;
} else {
crate::leanh::lean_dec_ref(v_e_2260_);
crate::leanh::lean_inc(v_generation_2262_);
v___x_2318_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2284_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
if crate::leanh::lean_obj_tag(v___x_2318_) == 0 {
v_a_2319_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
crate::leanh::lean_inc(v_a_2319_);
crate::leanh::lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
if crate::leanh::lean_obj_tag(v___x_2320_) == 0 {
v_a_2321_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2330_ = (!crate::leanh::lean_is_exclusive(v___x_2320_)) as u8;
if v_isSharedCheck_2330_ == 0 {
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2330_;
state = 1; continue;
} else {
crate::leanh::lean_inc(v_a_2321_);
crate::leanh::lean_dec(v___x_2320_);
v___x_2323_ = crate::leanh::lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2330_;
state = 1; continue;
}
} else {
crate::leanh::lean_dec(v_a_2319_);
v_a_2331_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2338_ = (!crate::leanh::lean_is_exclusive(v___x_2320_)) as u8;
if v_isSharedCheck_2338_ == 0 {
v___x_2333_ = v___x_2320_;
v_isShared_2334_ = v_isSharedCheck_2338_;
state = 3; continue;
} else {
crate::leanh::lean_inc(v_a_2331_);
crate::leanh::lean_dec(v___x_2320_);
v___x_2333_ = crate::leanh::lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
state = 3; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v_arg_2280_);
crate::leanh::lean_dec(v_generation_2262_);
v_a_2339_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2346_ = (!crate::leanh::lean_is_exclusive(v___x_2318_)) as u8;
if v_isSharedCheck_2346_ == 0 {
v___x_2341_ = v___x_2318_;
v_isShared_2342_ = v_isSharedCheck_2346_;
state = 5; continue;
} else {
crate::leanh::lean_inc(v_a_2339_);
crate::leanh::lean_dec(v___x_2318_);
v___x_2341_ = crate::leanh::lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
state = 5; continue;
}
}
}
} else {
crate::leanh::lean_dec_ref(v_arg_2290_);
crate::leanh::lean_dec_ref(v_arg_2284_);
crate::leanh::lean_dec_ref(v_arg_2280_);
crate::leanh::lean_dec(v_generation_2262_);
crate::leanh::lean_dec_ref(v_e_2260_);
v_a_2347_ = crate::leanh::lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2354_ = (!crate::leanh::lean_is_exclusive(v___x_2314_)) as u8;
if v_isSharedCheck_2354_ == 0 {
v___x_2349_ = v___x_2314_;
v_isShared_2350_ = v_isSharedCheck_2354_;
state = 7; continue;
} else {
crate::leanh::lean_inc(v_a_2347_);
crate::leanh::lean_dec(v___x_2314_);
v___x_2349_ = crate::leanh::lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
state = 7; continue;
}
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_2306_,
                                                                    );
                                                                    v___x_2355_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_2355_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_2356_ = crate::leanh::lean_ctor_get(v___x_2355_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2356_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_2355_, 1);
                                                                        v___x_2357_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_2356_, v_arg_2290_);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2290_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_2356_,
                                                                        );
                                                                        if v___x_2357_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_2284_);
                                                                            crate::leanh::lean_dec_ref(v_arg_2280_);
                                                                            v___x_2358_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                            return v___x_2358_;
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v_e_2260_);
                                                                            crate::leanh::lean_inc(
                                                                                v_generation_2262_,
                                                                            );
                                                                            v___x_2359_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2284_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                            if crate::leanh::lean_obj_tag(v___x_2359_) == 0 {
v_a_2360_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
crate::leanh::lean_inc(v_a_2360_);
crate::leanh::lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
if crate::leanh::lean_obj_tag(v___x_2361_) == 0 {
v_a_2362_ = crate::leanh::lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2371_ = (!crate::leanh::lean_is_exclusive(v___x_2361_)) as u8;
if v_isSharedCheck_2371_ == 0 {
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2371_;
state = 9; continue;
} else {
crate::leanh::lean_inc(v_a_2362_);
crate::leanh::lean_dec(v___x_2361_);
v___x_2364_ = crate::leanh::lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2371_;
state = 9; continue;
}
} else {
crate::leanh::lean_dec(v_a_2360_);
v_a_2372_ = crate::leanh::lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2379_ = (!crate::leanh::lean_is_exclusive(v___x_2361_)) as u8;
if v_isSharedCheck_2379_ == 0 {
v___x_2374_ = v___x_2361_;
v_isShared_2375_ = v_isSharedCheck_2379_;
state = 11; continue;
} else {
crate::leanh::lean_inc(v_a_2372_);
crate::leanh::lean_dec(v___x_2361_);
v___x_2374_ = crate::leanh::lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
state = 11; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v_arg_2280_);
crate::leanh::lean_dec(v_generation_2262_);
v_a_2380_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2387_ = (!crate::leanh::lean_is_exclusive(v___x_2359_)) as u8;
if v_isSharedCheck_2387_ == 0 {
v___x_2382_ = v___x_2359_;
v_isShared_2383_ = v_isSharedCheck_2387_;
state = 13; continue;
} else {
crate::leanh::lean_inc(v_a_2380_);
crate::leanh::lean_dec(v___x_2359_);
v___x_2382_ = crate::leanh::lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
state = 13; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2290_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2284_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2280_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_generation_2262_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_2260_,
                                                                        );
                                                                        v_a_2388_ = crate::leanh::lean_ctor_get(v___x_2355_, 0);
                                                                        v_isSharedCheck_2395_ = (!crate::leanh::lean_is_exclusive(v___x_2355_)) as u8;
                                                                        if v_isSharedCheck_2395_
                                                                            == 0
                                                                        {
                                                                            v___x_2390_ =
                                                                                v___x_2355_;
                                                                            v_isShared_2391_ = v_isSharedCheck_2395_;
                                                                            state = 15;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_2388_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_2355_,
                                                                            );
                                                                            v___x_2390_ = crate::leanh::lean_box(0);
                                                                            v_isShared_2391_ = v_isSharedCheck_2395_;
                                                                            state = 15;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2306_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_generation_2262_,
                                                                );
                                                                v___x_2396_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_2262_, v_arg_2290_, v_arg_2284_, v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2290_,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_2396_,
                                                                ) == 0
                                                                {
                                                                    v_a_2397_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_2396_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_2397_,
                                                                    );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_a_2397_,
                                                                    ) == 1
                                                                    {
                                                                        crate::leanh::lean_dec_ref_known(v_a_2397_, 1);
                                                                        crate::leanh::lean_dec(
                                                                            v_generation_2262_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_2260_,
                                                                        );
                                                                        return v___x_2396_;
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref_known(v___x_2396_, 1);
                                                                        crate::leanh::lean_dec(
                                                                            v_a_2397_,
                                                                        );
                                                                        v___x_2398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                        return v___x_2398_;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_generation_2262_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_2260_,
                                                                    );
                                                                    return v___x_2396_;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_2291_);
                                                crate::leanh::lean_dec_ref(v_arg_2290_);
                                                v___x_2399_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                if crate::leanh::lean_obj_tag(v___x_2399_) == 0 {
                                                    v_a_2400_ =
                                                        crate::leanh::lean_ctor_get(v___x_2399_, 0);
                                                    crate::leanh::lean_inc(v_a_2400_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2399_,
                                                        1,
                                                    );
                                                    v___x_2401_ =
                                                        l_Lean_Meta_Grind_Arith_Linear_isNegInst(
                                                            v_a_2400_,
                                                            v_arg_2284_,
                                                        );
                                                    crate::leanh::lean_dec_ref(v_arg_2284_);
                                                    crate::leanh::lean_dec(v_a_2400_);
                                                    if v___x_2401_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_2280_);
                                                        v___x_2402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                        return v___x_2402_;
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_e_2260_);
                                                        v___x_2403_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                        if crate::leanh::lean_obj_tag(v___x_2403_)
                                                            == 0
                                                        {
                                                            v_a_2404_ = crate::leanh::lean_ctor_get(
                                                                v___x_2403_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2413_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2403_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2413_ == 0 {
                                                                v___x_2406_ = v___x_2403_;
                                                                v_isShared_2407_ =
                                                                    v_isSharedCheck_2413_;
                                                                state = 17;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2404_);
                                                                crate::leanh::lean_dec(v___x_2403_);
                                                                v___x_2406_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2407_ =
                                                                    v_isSharedCheck_2413_;
                                                                state = 17;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_2414_ = crate::leanh::lean_ctor_get(
                                                                v___x_2403_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2421_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2403_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2421_ == 0 {
                                                                v___x_2416_ = v___x_2403_;
                                                                v_isShared_2417_ =
                                                                    v_isSharedCheck_2421_;
                                                                state = 19;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2414_);
                                                                crate::leanh::lean_dec(v___x_2403_);
                                                                v___x_2416_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2417_ =
                                                                    v_isSharedCheck_2421_;
                                                                state = 19;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_arg_2284_);
                                                    crate::leanh::lean_dec_ref(v_arg_2280_);
                                                    crate::leanh::lean_dec(v_generation_2262_);
                                                    crate::leanh::lean_dec_ref(v_e_2260_);
                                                    v_a_2422_ =
                                                        crate::leanh::lean_ctor_get(v___x_2399_, 0);
                                                    v_isSharedCheck_2429_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2399_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2429_ == 0 {
                                                        v___x_2424_ = v___x_2399_;
                                                        v_isShared_2425_ = v_isSharedCheck_2429_;
                                                        state = 21;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2422_);
                                                        crate::leanh::lean_dec(v___x_2399_);
                                                        v___x_2424_ = crate::leanh::lean_box(0);
                                                        v_isShared_2425_ = v_isSharedCheck_2429_;
                                                        state = 21;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2291_);
                                            crate::leanh::lean_dec_ref(v_arg_2290_);
                                            crate::leanh::lean_dec_ref(v_arg_2284_);
                                            crate::leanh::lean_dec_ref(v_arg_2280_);
                                            crate::leanh::lean_inc_ref(v_e_2260_);
                                            v___x_2430_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                            if crate::leanh::lean_obj_tag(v___x_2430_) == 0 {
                                                v_a_2431_ =
                                                    crate::leanh::lean_ctor_get(v___x_2430_, 0);
                                                v_isSharedCheck_2441_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2430_))
                                                        as u8;
                                                if v_isSharedCheck_2441_ == 0 {
                                                    v___x_2433_ = v___x_2430_;
                                                    v_isShared_2434_ = v_isSharedCheck_2441_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2431_);
                                                    crate::leanh::lean_dec(v___x_2430_);
                                                    v___x_2433_ = crate::leanh::lean_box(0);
                                                    v_isShared_2434_ = v_isSharedCheck_2441_;
                                                    state = 23;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_generation_2262_);
                                                crate::leanh::lean_dec_ref(v_e_2260_);
                                                v_a_2442_ =
                                                    crate::leanh::lean_ctor_get(v___x_2430_, 0);
                                                v_isSharedCheck_2449_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2430_))
                                                        as u8;
                                                if v_isSharedCheck_2449_ == 0 {
                                                    v___x_2444_ = v___x_2430_;
                                                    v_isShared_2445_ = v_isSharedCheck_2449_;
                                                    state = 25;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2442_);
                                                    crate::leanh::lean_dec(v___x_2430_);
                                                    v___x_2444_ = crate::leanh::lean_box(0);
                                                    v_isShared_2445_ = v_isSharedCheck_2449_;
                                                    state = 25;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_2291_);
                                        crate::leanh::lean_dec_ref(v_arg_2290_);
                                        crate::leanh::lean_dec_ref(v_arg_2284_);
                                        v___x_2450_ =
                                            l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                                v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_,
                                                v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_,
                                                v_a_2271_, v_a_2272_, v_a_2273_,
                                            );
                                        if crate::leanh::lean_obj_tag(v___x_2450_) == 0 {
                                            v_a_2451_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                                            crate::leanh::lean_inc(v_a_2451_);
                                            crate::leanh::lean_dec_ref_known(v___x_2450_, 1);
                                            v_orderedRingInst_x3f_2465_ =
                                                crate::leanh::lean_ctor_get(v_a_2451_, 14);
                                            crate::leanh::lean_inc(v_orderedRingInst_x3f_2465_);
                                            crate::leanh::lean_dec(v_a_2451_);
                                            if crate::leanh::lean_obj_tag(
                                                v_orderedRingInst_x3f_2465_,
                                            ) == 0
                                            {
                                                v___y_2453_ = v___x_2287_;
                                                state = 27;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(
                                                    v_orderedRingInst_x3f_2465_,
                                                    1,
                                                );
                                                v___y_2453_ = v___x_2293_;
                                                state = 27;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_arg_2280_);
                                            crate::leanh::lean_dec(v_generation_2262_);
                                            crate::leanh::lean_dec_ref(v_e_2260_);
                                            v_a_2466_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                                            v_isSharedCheck_2473_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2450_))
                                                    as u8;
                                            if v_isSharedCheck_2473_ == 0 {
                                                v___x_2468_ = v___x_2450_;
                                                v_isShared_2469_ = v_isSharedCheck_2473_;
                                                state = 30;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2466_);
                                                crate::leanh::lean_dec(v___x_2450_);
                                                v___x_2468_ = crate::leanh::lean_box(0);
                                                v_isShared_2469_ = v_isSharedCheck_2473_;
                                                state = 30;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2285_);
                                crate::leanh::lean_dec_ref(v_arg_2284_);
                                v___x_2474_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                    v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_,
                                    v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_,
                                    v_a_2273_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2474_) == 0 {
                                    v_a_2475_ = crate::leanh::lean_ctor_get(v___x_2474_, 0);
                                    v_isSharedCheck_2485_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2474_)) as u8;
                                    if v_isSharedCheck_2485_ == 0 {
                                        v___x_2477_ = v___x_2474_;
                                        v_isShared_2478_ = v_isSharedCheck_2485_;
                                        state = 32;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2475_);
                                        crate::leanh::lean_dec(v___x_2474_);
                                        v___x_2477_ = crate::leanh::lean_box(0);
                                        v_isShared_2478_ = v_isSharedCheck_2485_;
                                        state = 32;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_2280_);
                                    crate::leanh::lean_dec(v_generation_2262_);
                                    crate::leanh::lean_dec_ref(v_e_2260_);
                                    v_a_2486_ = crate::leanh::lean_ctor_get(v___x_2474_, 0);
                                    v_isSharedCheck_2493_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2474_)) as u8;
                                    if v_isSharedCheck_2493_ == 0 {
                                        v___x_2488_ = v___x_2474_;
                                        v_isShared_2489_ = v_isSharedCheck_2493_;
                                        state = 34;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2486_);
                                        crate::leanh::lean_dec(v___x_2474_);
                                        v___x_2488_ = crate::leanh::lean_box(0);
                                        v_isShared_2489_ = v_isSharedCheck_2493_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_2262_);
                    crate::leanh::lean_dec_ref(v_e_2260_);
                    v_a_2494_ = crate::leanh::lean_ctor_get(v___x_2275_, 0);
                    v_isSharedCheck_2501_ = (!crate::leanh::lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2501_ == 0 {
                        v___x_2496_ = v___x_2275_;
                        v_isShared_2497_ = v_isSharedCheck_2501_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2494_);
                        crate::leanh::lean_dec(v___x_2275_);
                        v___x_2496_ = crate::leanh::lean_box(0);
                        v_isShared_2497_ = v_isSharedCheck_2501_;
                        state = 36;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2325_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2325_, 0, v_a_2319_);
                crate::leanh::lean_ctor_set(v___x_2325_, 1, v_a_2321_);
                v___x_2326_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2326_, 0, v___x_2325_);
                if v_isShared_2324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2328_;
            }
            3 => {
                if v_isShared_2334_ == 0 {
                    v___x_2336_ = v___x_2333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2337_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
                    v___x_2336_ = v_reuseFailAlloc_2337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2336_;
            }
            5 => {
                if v_isShared_2342_ == 0 {
                    v___x_2344_ = v___x_2341_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
                    v___x_2344_ = v_reuseFailAlloc_2345_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2344_;
            }
            7 => {
                if v_isShared_2350_ == 0 {
                    v___x_2352_ = v___x_2349_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
                    v___x_2352_ = v_reuseFailAlloc_2353_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2352_;
            }
            9 => {
                v___x_2366_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2366_, 0, v_a_2360_);
                crate::leanh::lean_ctor_set(v___x_2366_, 1, v_a_2362_);
                v___x_2367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2367_, 0, v___x_2366_);
                if v_isShared_2365_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2364_, 0, v___x_2367_);
                    v___x_2369_ = v___x_2364_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
                    v___x_2369_ = v_reuseFailAlloc_2370_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2369_;
            }
            11 => {
                if v_isShared_2375_ == 0 {
                    v___x_2377_ = v___x_2374_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
                    v___x_2377_ = v_reuseFailAlloc_2378_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2377_;
            }
            13 => {
                if v_isShared_2383_ == 0 {
                    v___x_2385_ = v___x_2382_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2385_;
            }
            15 => {
                if v_isShared_2391_ == 0 {
                    v___x_2393_ = v___x_2390_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2394_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
                    v___x_2393_ = v_reuseFailAlloc_2394_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2393_;
            }
            17 => {
                v___x_2408_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2408_, 0, v_a_2404_);
                v___x_2409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2409_, 0, v___x_2408_);
                if v_isShared_2407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2406_, 0, v___x_2409_);
                    v___x_2411_ = v___x_2406_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
                    v___x_2411_ = v_reuseFailAlloc_2412_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2411_;
            }
            19 => {
                if v_isShared_2417_ == 0 {
                    v___x_2419_ = v___x_2416_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
                    v___x_2419_ = v_reuseFailAlloc_2420_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2419_;
            }
            21 => {
                if v_isShared_2425_ == 0 {
                    v___x_2427_ = v___x_2424_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
                    v___x_2427_ = v_reuseFailAlloc_2428_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2427_;
            }
            23 => {
                v___x_2435_ = (crate::leanh::lean_unbox(v_a_2431_) as u8);
                crate::leanh::lean_dec(v_a_2431_);
                if v___x_2435_ == 0 {
                    crate::leanh::lean_del_object(v___x_2433_);
                    v___x_2436_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                    return v___x_2436_;
                } else {
                    crate::leanh::lean_dec(v_generation_2262_);
                    crate::leanh::lean_dec_ref(v_e_2260_);
                    v___x_2437_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0;
                    if v_isShared_2434_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2433_, 0, v___x_2437_);
                        v___x_2439_ = v___x_2433_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_2440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
                        v___x_2439_ = v_reuseFailAlloc_2440_;
                        state = 24;
                        continue;
                    }
                }
            }
            24 => {
                return v___x_2439_;
            }
            25 => {
                if v_isShared_2445_ == 0 {
                    v___x_2447_ = v___x_2444_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
                    v___x_2447_ = v_reuseFailAlloc_2448_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2447_;
            }
            27 => {
                if v___y_2453_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_2280_);
                    v___x_2454_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                    return v___x_2454_;
                } else {
                    v___x_2455_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                    if crate::leanh::lean_obj_tag(v___x_2455_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2455_, 1);
                        v___x_2456_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                        return v___x_2456_;
                    } else {
                        crate::leanh::lean_dec(v_generation_2262_);
                        crate::leanh::lean_dec_ref(v_e_2260_);
                        v_a_2457_ = crate::leanh::lean_ctor_get(v___x_2455_, 0);
                        v_isSharedCheck_2464_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2455_)) as u8;
                        if v_isSharedCheck_2464_ == 0 {
                            v___x_2459_ = v___x_2455_;
                            v_isShared_2460_ = v_isSharedCheck_2464_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2457_);
                            crate::leanh::lean_dec(v___x_2455_);
                            v___x_2459_ = crate::leanh::lean_box(0);
                            v_isShared_2460_ = v_isSharedCheck_2464_;
                            state = 28;
                            continue;
                        }
                    }
                }
            }
            28 => {
                if v_isShared_2460_ == 0 {
                    v___x_2462_ = v___x_2459_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2463_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
                    v___x_2462_ = v_reuseFailAlloc_2463_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2462_;
            }
            30 => {
                if v_isShared_2469_ == 0 {
                    v___x_2471_ = v___x_2468_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
                    v___x_2471_ = v_reuseFailAlloc_2472_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2471_;
            }
            32 => {
                v___x_2479_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_2475_, v_arg_2280_);
                crate::leanh::lean_dec_ref(v_arg_2280_);
                crate::leanh::lean_dec(v_a_2475_);
                if v___x_2479_ == 0 {
                    crate::leanh::lean_del_object(v___x_2477_);
                    v___x_2480_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                    return v___x_2480_;
                } else {
                    crate::leanh::lean_dec(v_generation_2262_);
                    crate::leanh::lean_dec_ref(v_e_2260_);
                    v___x_2481_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0;
                    if v_isShared_2478_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2477_, 0, v___x_2481_);
                        v___x_2483_ = v___x_2477_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_2484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
                        v___x_2483_ = v_reuseFailAlloc_2484_;
                        state = 33;
                        continue;
                    }
                }
            }
            33 => {
                return v___x_2483_;
            }
            34 => {
                if v_isShared_2489_ == 0 {
                    v___x_2491_ = v___x_2488_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
                    v___x_2491_ = v_reuseFailAlloc_2492_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2491_;
            }
            36 => {
                if v_isShared_2497_ == 0 {
                    v___x_2499_ = v___x_2496_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reify_x3f___boxed(
    mut v_e_2502_: *mut crate::leanh::LeanObject,
    mut v_skipVar_2503_: *mut crate::leanh::LeanObject,
    mut v_generation_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
    mut v_a_2515_: *mut crate::leanh::LeanObject,
    mut v_a_2516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipVar_boxed_2517_: u8 = 0;
    let mut v_res_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_2517_ = (crate::leanh::lean_unbox(v_skipVar_2503_) as u8);
    v_res_2518_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
        v_e_2502_,
        v_skipVar_boxed_2517_,
        v_generation_2504_,
        v_a_2505_,
        v_a_2506_,
        v_a_2507_,
        v_a_2508_,
        v_a_2509_,
        v_a_2510_,
        v_a_2511_,
        v_a_2512_,
        v_a_2513_,
        v_a_2514_,
        v_a_2515_,
    );
    crate::leanh::lean_dec(v_a_2515_);
    crate::leanh::lean_dec_ref(v_a_2514_);
    crate::leanh::lean_dec(v_a_2513_);
    crate::leanh::lean_dec_ref(v_a_2512_);
    crate::leanh::lean_dec(v_a_2511_);
    crate::leanh::lean_dec_ref(v_a_2510_);
    crate::leanh::lean_dec(v_a_2509_);
    crate::leanh::lean_dec_ref(v_a_2508_);
    crate::leanh::lean_dec(v_a_2507_);
    crate::leanh::lean_dec(v_a_2506_);
    crate::leanh::lean_dec(v_a_2505_);
    return v_res_2518_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
}
