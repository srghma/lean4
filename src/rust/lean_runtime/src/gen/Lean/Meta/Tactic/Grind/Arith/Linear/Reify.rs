// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Reify
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.Linear.Var
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
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
use crate::lean_imports_rs::Init::Prelude::lean_panic_fn_borrowed;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_internalize;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0_value:
    LeanStringObject<47> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 114, 100, 101, 114, 101, 100, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 97, 116, 67, 97, 115, 116, 95, 110, 111, 110, 110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__2_value) as *mut LeanObject,17867769263165242357 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__3_value) as *mut LeanObject,16743452394867191478 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [90, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__0_value) as *mut LeanObject,18263865437487147968 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__1_value) as *mut LeanObject,2651253468108498348 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__3_value) as *mut LeanObject,5779414593499529281 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__4_value) as *mut LeanObject,7063772860359172143 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__6_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__7_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__9_value) as *mut LeanObject,9626815015619986526 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__10_value) as *mut LeanObject,17185717442815859305 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [72, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__12_value) as *mut LeanObject,15703084674812832738 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__13_value) as *mut LeanObject,13609749952674037527 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__15_value) as *mut LeanObject,16856108565602861689 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__16_value) as *mut LeanObject,4187025665268973031 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__18_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__19_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__20_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isAddInst(
    mut v_struct_1260_: *mut LeanObject,
    mut v_inst_1261_: *mut LeanObject,
) -> u8 {
    let mut v_addFn_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: u8 = 0;
    v_addFn_1262_ = lean_ctor_get(v_struct_1260_, 22);
    v___x_1263_ = l_Lean_Expr_appArg_x21(v_addFn_1262_);
    v___x_1264_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1263_,
        v_inst_1261_,
    );
    lean_dec_ref(v___x_1263_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(
    mut v_struct_1265_: *mut LeanObject,
    mut v_inst_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1267_: u8 = 0;
    let mut v_r_1268_: *mut LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_struct_1265_, v_inst_1266_);
    lean_dec_ref(v_inst_1266_);
    lean_dec_ref(v_struct_1265_);
    v_r_1268_ = lean_box((v_res_1267_) as usize);
    return v_r_1268_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isZeroInst(
    mut v_struct_1269_: *mut LeanObject,
    mut v_inst_1270_: *mut LeanObject,
) -> u8 {
    let mut v_zero_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    v_zero_1271_ = lean_ctor_get(v_struct_1269_, 17);
    v___x_1272_ = l_Lean_Expr_appArg_x21(v_zero_1271_);
    v___x_1273_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1272_,
        v_inst_1270_,
    );
    lean_dec_ref(v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(
    mut v_struct_1274_: *mut LeanObject,
    mut v_inst_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1276_: u8 = 0;
    let mut v_r_1277_: *mut LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_struct_1274_, v_inst_1275_);
    lean_dec_ref(v_inst_1275_);
    lean_dec_ref(v_struct_1274_);
    v_r_1277_ = lean_box((v_res_1276_) as usize);
    return v_r_1277_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(
    mut v_struct_1278_: *mut LeanObject,
    mut v_inst_1279_: *mut LeanObject,
) -> u8 {
    let mut v_zsmulFn_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: u8 = 0;
    v_zsmulFn_1280_ = lean_ctor_get(v_struct_1278_, 23);
    v___x_1281_ = l_Lean_Expr_appArg_x21(v_zsmulFn_1280_);
    v___x_1282_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1281_,
        v_inst_1279_,
    );
    lean_dec_ref(v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst___boxed(
    mut v_struct_1283_: *mut LeanObject,
    mut v_inst_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1285_: u8 = 0;
    let mut v_r_1286_: *mut LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_struct_1283_, v_inst_1284_);
    lean_dec_ref(v_inst_1284_);
    lean_dec_ref(v_struct_1283_);
    v_r_1286_ = lean_box((v_res_1285_) as usize);
    return v_r_1286_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(
    mut v_struct_1287_: *mut LeanObject,
    mut v_inst_1288_: *mut LeanObject,
) -> u8 {
    let mut v_nsmulFn_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    v_nsmulFn_1289_ = lean_ctor_get(v_struct_1287_, 24);
    v___x_1290_ = l_Lean_Expr_appArg_x21(v_nsmulFn_1289_);
    v___x_1291_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1290_,
        v_inst_1288_,
    );
    lean_dec_ref(v___x_1290_);
    return v___x_1291_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst___boxed(
    mut v_struct_1292_: *mut LeanObject,
    mut v_inst_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1294_: u8 = 0;
    let mut v_r_1295_: *mut LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_struct_1292_, v_inst_1293_);
    lean_dec_ref(v_inst_1293_);
    lean_dec_ref(v_struct_1292_);
    v_r_1295_ = lean_box((v_res_1294_) as usize);
    return v_r_1295_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(
    mut v_struct_1296_: *mut LeanObject,
    mut v_inst_1297_: *mut LeanObject,
) -> u8 {
    let mut v_homomulFn_x3f_1298_: *mut LeanObject = core::ptr::null_mut();
    v_homomulFn_x3f_1298_ = lean_ctor_get(v_struct_1296_, 27);
    if lean_obj_tag(v_homomulFn_x3f_1298_) == 1 {
        let mut v_val_1299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1300_: u8 = 0;
        v_val_1299_ = lean_ctor_get(v_homomulFn_x3f_1298_, 0);
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
    mut v_struct_1302_: *mut LeanObject,
    mut v_inst_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1304_: u8 = 0;
    let mut v_r_1305_: *mut LeanObject = core::ptr::null_mut();
    v_res_1304_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_struct_1302_, v_inst_1303_);
    lean_dec_ref(v_inst_1303_);
    lean_dec_ref(v_struct_1302_);
    v_r_1305_ = lean_box((v_res_1304_) as usize);
    return v_r_1305_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(
    mut v_struct_1306_: *mut LeanObject,
    mut v_inst_1307_: *mut LeanObject,
) -> u8 {
    let mut v_zsmulFn_x3f_1308_: *mut LeanObject = core::ptr::null_mut();
    v_zsmulFn_x3f_1308_ = lean_ctor_get(v_struct_1306_, 25);
    if lean_obj_tag(v_zsmulFn_x3f_1308_) == 1 {
        let mut v_val_1309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1311_: u8 = 0;
        v_val_1309_ = lean_ctor_get(v_zsmulFn_x3f_1308_, 0);
        v___x_1310_ = l_Lean_Expr_appArg_x21(v_val_1309_);
        v___x_1311_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v___x_1310_,
            v_inst_1307_,
        );
        lean_dec_ref(v___x_1310_);
        return v___x_1311_;
    } else {
        let mut v___x_1312_: u8 = 0;
        v___x_1312_ = 0;
        return v___x_1312_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst___boxed(
    mut v_struct_1313_: *mut LeanObject,
    mut v_inst_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1315_: u8 = 0;
    let mut v_r_1316_: *mut LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Lean_Meta_Grind_Arith_Linear_isHSMulIntInst(v_struct_1313_, v_inst_1314_);
    lean_dec_ref(v_inst_1314_);
    lean_dec_ref(v_struct_1313_);
    v_r_1316_ = lean_box((v_res_1315_) as usize);
    return v_r_1316_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(
    mut v_struct_1317_: *mut LeanObject,
    mut v_inst_1318_: *mut LeanObject,
) -> u8 {
    let mut v_nsmulFn_x3f_1319_: *mut LeanObject = core::ptr::null_mut();
    v_nsmulFn_x3f_1319_ = lean_ctor_get(v_struct_1317_, 26);
    if lean_obj_tag(v_nsmulFn_x3f_1319_) == 1 {
        let mut v_val_1320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: u8 = 0;
        v_val_1320_ = lean_ctor_get(v_nsmulFn_x3f_1319_, 0);
        v___x_1321_ = l_Lean_Expr_appArg_x21(v_val_1320_);
        v___x_1322_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v___x_1321_,
            v_inst_1318_,
        );
        lean_dec_ref(v___x_1321_);
        return v___x_1322_;
    } else {
        let mut v___x_1323_: u8 = 0;
        v___x_1323_ = 0;
        return v___x_1323_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst___boxed(
    mut v_struct_1324_: *mut LeanObject,
    mut v_inst_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1326_: u8 = 0;
    let mut v_r_1327_: *mut LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_Lean_Meta_Grind_Arith_Linear_isHSMulNatInst(v_struct_1324_, v_inst_1325_);
    lean_dec_ref(v_inst_1325_);
    lean_dec_ref(v_struct_1324_);
    v_r_1327_ = lean_box((v_res_1326_) as usize);
    return v_r_1327_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSubInst(
    mut v_struct_1328_: *mut LeanObject,
    mut v_inst_1329_: *mut LeanObject,
) -> u8 {
    let mut v_subFn_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    v_subFn_1330_ = lean_ctor_get(v_struct_1328_, 28);
    v___x_1331_ = l_Lean_Expr_appArg_x21(v_subFn_1330_);
    v___x_1332_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1331_,
        v_inst_1329_,
    );
    lean_dec_ref(v___x_1331_);
    return v___x_1332_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isSubInst___boxed(
    mut v_struct_1333_: *mut LeanObject,
    mut v_inst_1334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1335_: u8 = 0;
    let mut v_r_1336_: *mut LeanObject = core::ptr::null_mut();
    v_res_1335_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_struct_1333_, v_inst_1334_);
    lean_dec_ref(v_inst_1334_);
    lean_dec_ref(v_struct_1333_);
    v_r_1336_ = lean_box((v_res_1335_) as usize);
    return v_r_1336_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isNegInst(
    mut v_struct_1337_: *mut LeanObject,
    mut v_inst_1338_: *mut LeanObject,
) -> u8 {
    let mut v_negFn_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    v_negFn_1339_ = lean_ctor_get(v_struct_1337_, 29);
    v___x_1340_ = l_Lean_Expr_appArg_x21(v_negFn_1339_);
    v___x_1341_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_1340_,
        v_inst_1338_,
    );
    lean_dec_ref(v___x_1340_);
    return v___x_1341_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isNegInst___boxed(
    mut v_struct_1342_: *mut LeanObject,
    mut v_inst_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1344_: u8 = 0;
    let mut v_r_1345_: *mut LeanObject = core::ptr::null_mut();
    v_res_1344_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_struct_1342_, v_inst_1343_);
    lean_dec_ref(v_inst_1343_);
    lean_dec_ref(v_struct_1342_);
    v_r_1345_ = lean_box((v_res_1344_) as usize);
    return v_r_1345_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__0;
    v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
    mut v_e_1349_: *mut LeanObject,
    mut v_a_1350_: *mut LeanObject,
    mut v_a_1351_: *mut LeanObject,
    mut v_a_1352_: *mut LeanObject,
    mut v_a_1353_: *mut LeanObject,
    mut v_a_1354_: *mut LeanObject,
    mut v_a_1355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_a_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1357_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1350_);
                if lean_obj_tag(v___x_1357_) == 0 {
                    v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
                    v_isSharedCheck_1371_ = (!lean_is_exclusive(v___x_1357_)) as u8;
                    if v_isSharedCheck_1371_ == 0 {
                        v___x_1360_ = v___x_1357_;
                        v_isShared_1361_ = v_isSharedCheck_1371_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1358_);
                        lean_dec(v___x_1357_);
                        v___x_1360_ = lean_box(0);
                        v_isShared_1361_ = v_isSharedCheck_1371_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1349_);
                    v_a_1372_ = lean_ctor_get(v___x_1357_, 0);
                    v_isSharedCheck_1379_ = (!lean_is_exclusive(v___x_1357_)) as u8;
                    if v_isSharedCheck_1379_ == 0 {
                        v___x_1374_ = v___x_1357_;
                        v_isShared_1375_ = v_isSharedCheck_1379_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1372_);
                        lean_dec(v___x_1357_);
                        v___x_1374_ = lean_box(0);
                        v_isShared_1375_ = v_isSharedCheck_1379_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1362_ = (lean_unbox(v_a_1358_) as u8);
                lean_dec(v_a_1358_);
                if v___x_1362_ == 0 {
                    lean_dec_ref(v_e_1349_);
                    v___x_1363_ = lean_box(0);
                    if v_isShared_1361_ == 0 {
                        lean_ctor_set(v___x_1360_, 0, v___x_1363_);
                        v___x_1365_ = v___x_1360_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
                        v___x_1365_ = v_reuseFailAlloc_1366_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1360_);
                    v___x_1367_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg___closed__1);
                    v___x_1368_ = l_Lean_indentExpr(v_e_1349_);
                    v___x_1369_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1369_, 0, v___x_1367_);
                    lean_ctor_set(v___x_1369_, 1, v___x_1368_);
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
                    v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
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
    mut v_e_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1388_: *mut LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
        v_e_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_,
    );
    lean_dec(v_a_1386_);
    lean_dec_ref(v_a_1385_);
    lean_dec(v_a_1384_);
    lean_dec_ref(v_a_1383_);
    lean_dec(v_a_1382_);
    lean_dec_ref(v_a_1381_);
    return v_res_1388_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(
    mut v_e_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
    mut v_a_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
    mut v_a_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
    mut v_a_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
        v_e_1389_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_,
    );
    return v___x_1401_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___boxed(
    mut v_e_1402_: *mut LeanObject,
    mut v_a_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
    mut v_a_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_a_1407_: *mut LeanObject,
    mut v_a_1408_: *mut LeanObject,
    mut v_a_1409_: *mut LeanObject,
    mut v_a_1410_: *mut LeanObject,
    mut v_a_1411_: *mut LeanObject,
    mut v_a_1412_: *mut LeanObject,
    mut v_a_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue(
        v_e_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_,
        v_a_1410_, v_a_1411_, v_a_1412_,
    );
    lean_dec(v_a_1412_);
    lean_dec_ref(v_a_1411_);
    lean_dec(v_a_1410_);
    lean_dec_ref(v_a_1409_);
    lean_dec(v_a_1408_);
    lean_dec_ref(v_a_1407_);
    lean_dec(v_a_1406_);
    lean_dec_ref(v_a_1405_);
    lean_dec(v_a_1404_);
    lean_dec(v_a_1403_);
    return v_res_1414_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(
    mut v_msg_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1416_ = l_Lean_instInhabitedExpr;
    v___x_1417_ = lean_panic_fn_borrowed(v___x_1416_, v_msg_1415_);
    return v___x_1417_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10()
-> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    v___x_1434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__9;
    v___x_1435_ = lean_unsigned_to_nat(14);
    v___x_1436_ = lean_unsigned_to_nat(22);
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
    mut v_a_1440_: *mut LeanObject,
    mut v_a_1441_: *mut LeanObject,
    mut v_a_1442_: *mut LeanObject,
    mut v_a_1443_: *mut LeanObject,
    mut v_a_1444_: *mut LeanObject,
    mut v_a_1445_: *mut LeanObject,
    mut v_a_1446_: *mut LeanObject,
    mut v_a_1447_: *mut LeanObject,
    mut v_a_1448_: *mut LeanObject,
    mut v_a_1449_: *mut LeanObject,
    mut v_a_1450_: *mut LeanObject,
    mut v_a_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1485_: u8 = 0;
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_a_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v___y_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1539_: u8 = 0;
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1453_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_,
                    v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_,
                );
                if lean_obj_tag(v___x_1453_) == 0 {
                    v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
                    lean_inc(v_a_1454_);
                    lean_dec_ref_known(v___x_1453_, 1);
                    v_type_1455_ = lean_ctor_get(v_a_1454_, 2);
                    lean_inc_ref(v_type_1455_);
                    v_u_1456_ = lean_ctor_get(v_a_1454_, 3);
                    lean_inc(v_u_1456_);
                    v_leInst_x3f_1457_ = lean_ctor_get(v_a_1454_, 5);
                    lean_inc(v_leInst_x3f_1457_);
                    v_ltInst_x3f_1458_ = lean_ctor_get(v_a_1454_, 6);
                    lean_inc(v_ltInst_x3f_1458_);
                    v_lawfulOrderLTInst_x3f_1459_ = lean_ctor_get(v_a_1454_, 7);
                    lean_inc(v_lawfulOrderLTInst_x3f_1459_);
                    v_isPreorderInst_x3f_1460_ = lean_ctor_get(v_a_1454_, 8);
                    lean_inc(v_isPreorderInst_x3f_1460_);
                    v_ringInst_x3f_1461_ = lean_ctor_get(v_a_1454_, 12);
                    lean_inc(v_ringInst_x3f_1461_);
                    v_orderedRingInst_x3f_1462_ = lean_ctor_get(v_a_1454_, 14);
                    lean_inc(v_orderedRingInst_x3f_1462_);
                    lean_dec(v_a_1454_);
                    v___x_1463_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__4;
                    v___x_1464_ = lean_box(0);
                    v___x_1465_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1465_, 0, v_u_1456_);
                    lean_ctor_set(v___x_1465_, 1, v___x_1464_);
                    v___x_1466_ = l_Lean_mkConst(v___x_1463_, v___x_1465_);
                    if lean_obj_tag(v_ringInst_x3f_1461_) == 0 {
                        v___x_1533_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                        v___x_1534_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1533_);
                        v___y_1529_ = v___x_1534_;
                        state = 10;
                        continue;
                    } else {
                        v_val_1535_ = lean_ctor_get(v_ringInst_x3f_1461_, 0);
                        lean_inc(v_val_1535_);
                        lean_dec_ref_known(v_ringInst_x3f_1461_, 1);
                        v___y_1529_ = v_val_1535_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_1440_);
                    v_a_1536_ = lean_ctor_get(v___x_1453_, 0);
                    v_isSharedCheck_1543_ = (!lean_is_exclusive(v___x_1453_)) as u8;
                    if v_isSharedCheck_1543_ == 0 {
                        v___x_1538_ = v___x_1453_;
                        v_isShared_1539_ = v_isSharedCheck_1543_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1536_);
                        lean_dec(v___x_1453_);
                        v___x_1538_ = lean_box(0);
                        v_isShared_1539_ = v_isSharedCheck_1543_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_a_1440_);
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
                lean_inc(v_a_1451_);
                lean_inc_ref(v_a_1450_);
                lean_inc(v_a_1449_);
                lean_inc_ref(v_a_1448_);
                lean_inc_ref(v___x_1474_);
                v___x_1475_ =
                    lean_infer_type(v___x_1474_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
                if lean_obj_tag(v___x_1475_) == 0 {
                    v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
                    lean_inc(v_a_1476_);
                    lean_dec_ref_known(v___x_1475_, 1);
                    v___x_1477_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1440_, v_a_1442_);
                    lean_dec_ref(v_a_1440_);
                    if lean_obj_tag(v___x_1477_) == 0 {
                        v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
                        lean_inc(v_a_1478_);
                        lean_dec_ref_known(v___x_1477_, 1);
                        v___x_1479_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__6;
                        v___x_1480_ = lean_box(1);
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
                        lean_dec(v_a_1476_);
                        lean_dec_ref(v___x_1474_);
                        v_a_1482_ = lean_ctor_get(v___x_1477_, 0);
                        v_isSharedCheck_1489_ = (!lean_is_exclusive(v___x_1477_)) as u8;
                        if v_isSharedCheck_1489_ == 0 {
                            v___x_1484_ = v___x_1477_;
                            v_isShared_1485_ = v_isSharedCheck_1489_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1482_);
                            lean_dec(v___x_1477_);
                            v___x_1484_ = lean_box(0);
                            v_isShared_1485_ = v_isSharedCheck_1489_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1474_);
                    lean_dec_ref(v_a_1440_);
                    v_a_1490_ = lean_ctor_get(v___x_1475_, 0);
                    v_isSharedCheck_1497_ = (!lean_is_exclusive(v___x_1475_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v___x_1492_ = v___x_1475_;
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1490_);
                        lean_dec(v___x_1475_);
                        v___x_1492_ = lean_box(0);
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
                    v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
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
                    v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
                    v___x_1495_ = v_reuseFailAlloc_1496_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1495_;
            }
            6 => {
                if lean_obj_tag(v_orderedRingInst_x3f_1462_) == 0 {
                    v___x_1504_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
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
                    v_val_1506_ = lean_ctor_get(v_orderedRingInst_x3f_1462_, 0);
                    lean_inc(v_val_1506_);
                    lean_dec_ref_known(v_orderedRingInst_x3f_1462_, 1);
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
                if lean_obj_tag(v_isPreorderInst_x3f_1460_) == 0 {
                    v___x_1512_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1513_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1512_);
                    v___y_1499_ = v___y_1508_;
                    v___y_1500_ = v___y_1510_;
                    v___y_1501_ = v___y_1509_;
                    v___y_1502_ = v___y_1511_;
                    v___y_1503_ = v___x_1513_;
                    state = 6;
                    continue;
                } else {
                    v_val_1514_ = lean_ctor_get(v_isPreorderInst_x3f_1460_, 0);
                    lean_inc(v_val_1514_);
                    lean_dec_ref_known(v_isPreorderInst_x3f_1460_, 1);
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
                if lean_obj_tag(v_lawfulOrderLTInst_x3f_1459_) == 0 {
                    v___x_1519_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1520_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1519_);
                    v___y_1508_ = v___y_1518_;
                    v___y_1509_ = v___y_1517_;
                    v___y_1510_ = v___y_1516_;
                    v___y_1511_ = v___x_1520_;
                    state = 7;
                    continue;
                } else {
                    v_val_1521_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_1459_, 0);
                    lean_inc(v_val_1521_);
                    lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1459_, 1);
                    v___y_1508_ = v___y_1518_;
                    v___y_1509_ = v___y_1517_;
                    v___y_1510_ = v___y_1516_;
                    v___y_1511_ = v_val_1521_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if lean_obj_tag(v_ltInst_x3f_1458_) == 0 {
                    v___x_1525_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1526_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1525_);
                    v___y_1516_ = v___y_1523_;
                    v___y_1517_ = v___y_1524_;
                    v___y_1518_ = v___x_1526_;
                    state = 8;
                    continue;
                } else {
                    v_val_1527_ = lean_ctor_get(v_ltInst_x3f_1458_, 0);
                    lean_inc(v_val_1527_);
                    lean_dec_ref_known(v_ltInst_x3f_1458_, 1);
                    v___y_1516_ = v___y_1523_;
                    v___y_1517_ = v___y_1524_;
                    v___y_1518_ = v_val_1527_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if lean_obj_tag(v_leInst_x3f_1457_) == 0 {
                    v___x_1530_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg___closed__10);
                    v___x_1531_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg_spec__0(v___x_1530_);
                    v___y_1523_ = v___y_1529_;
                    v___y_1524_ = v___x_1531_;
                    state = 9;
                    continue;
                } else {
                    v_val_1532_ = lean_ctor_get(v_leInst_x3f_1457_, 0);
                    lean_inc(v_val_1532_);
                    lean_dec_ref_known(v_leInst_x3f_1457_, 1);
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
                    v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
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
    mut v_a_1544_: *mut LeanObject,
    mut v_a_1545_: *mut LeanObject,
    mut v_a_1546_: *mut LeanObject,
    mut v_a_1547_: *mut LeanObject,
    mut v_a_1548_: *mut LeanObject,
    mut v_a_1549_: *mut LeanObject,
    mut v_a_1550_: *mut LeanObject,
    mut v_a_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
    mut v_a_1555_: *mut LeanObject,
    mut v_a_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1557_: *mut LeanObject = core::ptr::null_mut();
    v_res_1557_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
    lean_dec(v_a_1555_);
    lean_dec_ref(v_a_1554_);
    lean_dec(v_a_1553_);
    lean_dec_ref(v_a_1552_);
    lean_dec(v_a_1551_);
    lean_dec_ref(v_a_1550_);
    lean_dec(v_a_1549_);
    lean_dec_ref(v_a_1548_);
    lean_dec(v_a_1547_);
    lean_dec(v_a_1546_);
    lean_dec(v_a_1545_);
    return v_res_1557_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(
    mut v_generation_1558_: *mut LeanObject,
    mut v_e_1559_: *mut LeanObject,
    mut v_a_1560_: *mut LeanObject,
    mut v_a_1561_: *mut LeanObject,
    mut v_a_1562_: *mut LeanObject,
    mut v_a_1563_: *mut LeanObject,
    mut v_a_1564_: *mut LeanObject,
    mut v_a_1565_: *mut LeanObject,
    mut v_a_1566_: *mut LeanObject,
    mut v_a_1567_: *mut LeanObject,
    mut v_a_1568_: *mut LeanObject,
    mut v_a_1569_: *mut LeanObject,
    mut v_a_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_a_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_a_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1599_: u8 = 0;
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1613_: u8 = 0;
    let mut v_a_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_a_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1572_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1559_, v_a_1561_);
                if lean_obj_tag(v___x_1572_) == 0 {
                    v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
                    lean_inc(v_a_1573_);
                    lean_dec_ref_known(v___x_1572_, 1);
                    v___x_1574_ = 1;
                    v___x_1575_ = (lean_unbox(v_a_1573_) as u8);
                    lean_dec(v_a_1573_);
                    if v___x_1575_ == 0 {
                        v___x_1576_ = lean_box(0);
                        lean_inc(v_a_1570_);
                        lean_inc_ref(v_a_1569_);
                        lean_inc(v_a_1568_);
                        lean_inc_ref(v_a_1567_);
                        lean_inc(v_a_1566_);
                        lean_inc_ref(v_a_1565_);
                        lean_inc(v_a_1564_);
                        lean_inc_ref(v_a_1563_);
                        lean_inc(v_a_1562_);
                        lean_inc(v_a_1561_);
                        lean_inc_ref(v_e_1559_);
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
                        if lean_obj_tag(v___x_1577_) == 0 {
                            lean_dec_ref_known(v___x_1577_, 1);
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
                            if lean_obj_tag(v___x_1578_) == 0 {
                                v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
                                v_isSharedCheck_1587_ = (!lean_is_exclusive(v___x_1578_)) as u8;
                                if v_isSharedCheck_1587_ == 0 {
                                    v___x_1581_ = v___x_1578_;
                                    v_isShared_1582_ = v_isSharedCheck_1587_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_1579_);
                                    lean_dec(v___x_1578_);
                                    v___x_1581_ = lean_box(0);
                                    v_isShared_1582_ = v_isSharedCheck_1587_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_1588_ = lean_ctor_get(v___x_1578_, 0);
                                v_isSharedCheck_1595_ = (!lean_is_exclusive(v___x_1578_)) as u8;
                                if v_isSharedCheck_1595_ == 0 {
                                    v___x_1590_ = v___x_1578_;
                                    v_isShared_1591_ = v_isSharedCheck_1595_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1588_);
                                    lean_dec(v___x_1578_);
                                    v___x_1590_ = lean_box(0);
                                    v_isShared_1591_ = v_isSharedCheck_1595_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_e_1559_);
                            v_a_1596_ = lean_ctor_get(v___x_1577_, 0);
                            v_isSharedCheck_1603_ = (!lean_is_exclusive(v___x_1577_)) as u8;
                            if v_isSharedCheck_1603_ == 0 {
                                v___x_1598_ = v___x_1577_;
                                v_isShared_1599_ = v_isSharedCheck_1603_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1596_);
                                lean_dec(v___x_1577_);
                                v___x_1598_ = lean_box(0);
                                v_isShared_1599_ = v_isSharedCheck_1603_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_generation_1558_);
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
                        if lean_obj_tag(v___x_1604_) == 0 {
                            v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
                            v_isSharedCheck_1613_ = (!lean_is_exclusive(v___x_1604_)) as u8;
                            if v_isSharedCheck_1613_ == 0 {
                                v___x_1607_ = v___x_1604_;
                                v_isShared_1608_ = v_isSharedCheck_1613_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_1605_);
                                lean_dec(v___x_1604_);
                                v___x_1607_ = lean_box(0);
                                v_isShared_1608_ = v_isSharedCheck_1613_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_1614_ = lean_ctor_get(v___x_1604_, 0);
                            v_isSharedCheck_1621_ = (!lean_is_exclusive(v___x_1604_)) as u8;
                            if v_isSharedCheck_1621_ == 0 {
                                v___x_1616_ = v___x_1604_;
                                v_isShared_1617_ = v_isSharedCheck_1621_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_1614_);
                                lean_dec(v___x_1604_);
                                v___x_1616_ = lean_box(0);
                                v_isShared_1617_ = v_isSharedCheck_1621_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1559_);
                    lean_dec(v_generation_1558_);
                    v_a_1622_ = lean_ctor_get(v___x_1572_, 0);
                    v_isSharedCheck_1629_ = (!lean_is_exclusive(v___x_1572_)) as u8;
                    if v_isSharedCheck_1629_ == 0 {
                        v___x_1624_ = v___x_1572_;
                        v_isShared_1625_ = v_isSharedCheck_1629_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1622_);
                        lean_dec(v___x_1572_);
                        v___x_1624_ = lean_box(0);
                        v_isShared_1625_ = v_isSharedCheck_1629_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1583_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1583_, 0, v_a_1579_);
                if v_isShared_1582_ == 0 {
                    lean_ctor_set(v___x_1581_, 0, v___x_1583_);
                    v___x_1585_ = v___x_1581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
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
                    v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
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
                    v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
                    v___x_1601_ = v_reuseFailAlloc_1602_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1601_;
            }
            7 => {
                v___x_1609_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1609_, 0, v_a_1605_);
                if v_isShared_1608_ == 0 {
                    lean_ctor_set(v___x_1607_, 0, v___x_1609_);
                    v___x_1611_ = v___x_1607_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
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
                    v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
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
                    v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
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
    mut v_generation_1630_: *mut LeanObject,
    mut v_e_1631_: *mut LeanObject,
    mut v_a_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
    mut v_a_1634_: *mut LeanObject,
    mut v_a_1635_: *mut LeanObject,
    mut v_a_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
    mut v_a_1638_: *mut LeanObject,
    mut v_a_1639_: *mut LeanObject,
    mut v_a_1640_: *mut LeanObject,
    mut v_a_1641_: *mut LeanObject,
    mut v_a_1642_: *mut LeanObject,
    mut v_a_1643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1644_: *mut LeanObject = core::ptr::null_mut();
    v_res_1644_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1630_, v_e_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
    lean_dec(v_a_1642_);
    lean_dec_ref(v_a_1641_);
    lean_dec(v_a_1640_);
    lean_dec_ref(v_a_1639_);
    lean_dec(v_a_1638_);
    lean_dec_ref(v_a_1637_);
    lean_dec(v_a_1636_);
    lean_dec_ref(v_a_1635_);
    lean_dec(v_a_1634_);
    lean_dec(v_a_1633_);
    lean_dec(v_a_1632_);
    return v_res_1644_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(
    mut v_generation_1645_: *mut LeanObject,
    mut v_e_1646_: *mut LeanObject,
    mut v_a_1647_: *mut LeanObject,
    mut v_a_1648_: *mut LeanObject,
    mut v_a_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
    mut v_a_1651_: *mut LeanObject,
    mut v_a_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
    mut v_a_1654_: *mut LeanObject,
    mut v_a_1655_: *mut LeanObject,
    mut v_a_1656_: *mut LeanObject,
    mut v_a_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1664_: u8 = 0;
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1646_);
                v___x_1659_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
                    v_e_1646_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_,
                );
                if lean_obj_tag(v___x_1659_) == 0 {
                    lean_dec_ref_known(v___x_1659_, 1);
                    v___x_1660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1645_, v_e_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
                    return v___x_1660_;
                } else {
                    lean_dec_ref(v_e_1646_);
                    lean_dec(v_generation_1645_);
                    v_a_1661_ = lean_ctor_get(v___x_1659_, 0);
                    v_isSharedCheck_1668_ = (!lean_is_exclusive(v___x_1659_)) as u8;
                    if v_isSharedCheck_1668_ == 0 {
                        v___x_1663_ = v___x_1659_;
                        v_isShared_1664_ = v_isSharedCheck_1668_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1661_);
                        lean_dec(v___x_1659_);
                        v___x_1663_ = lean_box(0);
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
                    v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
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
    mut v_generation_1669_: *mut LeanObject,
    mut v_e_1670_: *mut LeanObject,
    mut v_a_1671_: *mut LeanObject,
    mut v_a_1672_: *mut LeanObject,
    mut v_a_1673_: *mut LeanObject,
    mut v_a_1674_: *mut LeanObject,
    mut v_a_1675_: *mut LeanObject,
    mut v_a_1676_: *mut LeanObject,
    mut v_a_1677_: *mut LeanObject,
    mut v_a_1678_: *mut LeanObject,
    mut v_a_1679_: *mut LeanObject,
    mut v_a_1680_: *mut LeanObject,
    mut v_a_1681_: *mut LeanObject,
    mut v_a_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1683_: *mut LeanObject = core::ptr::null_mut();
    v_res_1683_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1669_, v_e_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
    lean_dec(v_a_1681_);
    lean_dec_ref(v_a_1680_);
    lean_dec(v_a_1679_);
    lean_dec_ref(v_a_1678_);
    lean_dec(v_a_1677_);
    lean_dec_ref(v_a_1676_);
    lean_dec(v_a_1675_);
    lean_dec_ref(v_a_1674_);
    lean_dec(v_a_1673_);
    lean_dec(v_a_1672_);
    lean_dec(v_a_1671_);
    return v_res_1683_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(
    mut v_skipVar_1684_: u8,
    mut v_generation_1685_: *mut LeanObject,
    mut v_e_1686_: *mut LeanObject,
    mut v_a_1687_: *mut LeanObject,
    mut v_a_1688_: *mut LeanObject,
    mut v_a_1689_: *mut LeanObject,
    mut v_a_1690_: *mut LeanObject,
    mut v_a_1691_: *mut LeanObject,
    mut v_a_1692_: *mut LeanObject,
    mut v_a_1693_: *mut LeanObject,
    mut v_a_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
    mut v_a_1696_: *mut LeanObject,
    mut v_a_1697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_a_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_skipVar_1684_ == 0 {
                    v___x_1699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1685_, v_e_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
                    if lean_obj_tag(v___x_1699_) == 0 {
                        v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
                        v_isSharedCheck_1708_ = (!lean_is_exclusive(v___x_1699_)) as u8;
                        if v_isSharedCheck_1708_ == 0 {
                            v___x_1702_ = v___x_1699_;
                            v_isShared_1703_ = v_isSharedCheck_1708_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1700_);
                            lean_dec(v___x_1699_);
                            v___x_1702_ = lean_box(0);
                            v_isShared_1703_ = v_isSharedCheck_1708_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1709_ = lean_ctor_get(v___x_1699_, 0);
                        v_isSharedCheck_1716_ = (!lean_is_exclusive(v___x_1699_)) as u8;
                        if v_isSharedCheck_1716_ == 0 {
                            v___x_1711_ = v___x_1699_;
                            v_isShared_1712_ = v_isSharedCheck_1716_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1709_);
                            lean_dec(v___x_1699_);
                            v___x_1711_ = lean_box(0);
                            v_isShared_1712_ = v_isSharedCheck_1716_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1686_);
                    lean_dec(v_generation_1685_);
                    v___x_1717_ = lean_box(0);
                    v___x_1718_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1718_, 0, v___x_1717_);
                    return v___x_1718_;
                }
            }
            1 => {
                v___x_1704_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1704_, 0, v_a_1700_);
                if v_isShared_1703_ == 0 {
                    lean_ctor_set(v___x_1702_, 0, v___x_1704_);
                    v___x_1706_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
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
                    v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
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
    mut v_skipVar_1719_: *mut LeanObject,
    mut v_generation_1720_: *mut LeanObject,
    mut v_e_1721_: *mut LeanObject,
    mut v_a_1722_: *mut LeanObject,
    mut v_a_1723_: *mut LeanObject,
    mut v_a_1724_: *mut LeanObject,
    mut v_a_1725_: *mut LeanObject,
    mut v_a_1726_: *mut LeanObject,
    mut v_a_1727_: *mut LeanObject,
    mut v_a_1728_: *mut LeanObject,
    mut v_a_1729_: *mut LeanObject,
    mut v_a_1730_: *mut LeanObject,
    mut v_a_1731_: *mut LeanObject,
    mut v_a_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipVar_boxed_1734_: u8 = 0;
    let mut v_res_1735_: *mut LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_1734_ = (lean_unbox(v_skipVar_1719_) as u8);
    v_res_1735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_boxed_1734_, v_generation_1720_, v_e_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
    lean_dec(v_a_1732_);
    lean_dec_ref(v_a_1731_);
    lean_dec(v_a_1730_);
    lean_dec_ref(v_a_1729_);
    lean_dec(v_a_1728_);
    lean_dec_ref(v_a_1727_);
    lean_dec(v_a_1726_);
    lean_dec_ref(v_a_1725_);
    lean_dec(v_a_1724_);
    lean_dec(v_a_1723_);
    lean_dec(v_a_1722_);
    return v_res_1735_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(
    mut v_skipVar_1736_: u8,
    mut v_generation_1737_: *mut LeanObject,
    mut v_e_1738_: *mut LeanObject,
    mut v_a_1739_: *mut LeanObject,
    mut v_a_1740_: *mut LeanObject,
    mut v_a_1741_: *mut LeanObject,
    mut v_a_1742_: *mut LeanObject,
    mut v_a_1743_: *mut LeanObject,
    mut v_a_1744_: *mut LeanObject,
    mut v_a_1745_: *mut LeanObject,
    mut v_a_1746_: *mut LeanObject,
    mut v_a_1747_: *mut LeanObject,
    mut v_a_1748_: *mut LeanObject,
    mut v_a_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v_a_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1772_: u8 = 0;
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1777_: u8 = 0;
    let mut v_unused_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1738_);
                v___x_1751_ = l_Lean_Meta_Grind_Arith_Linear_reportInstIssue___redArg(
                    v_e_1738_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_,
                );
                if lean_obj_tag(v___x_1751_) == 0 {
                    v_isSharedCheck_1777_ = (!lean_is_exclusive(v___x_1751_)) as u8;
                    if v_isSharedCheck_1777_ == 0 {
                        v_unused_1778_ = lean_ctor_get(v___x_1751_, 0);
                        lean_dec(v_unused_1778_);
                        v___x_1753_ = v___x_1751_;
                        v_isShared_1754_ = v_isSharedCheck_1777_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1751_);
                        v___x_1753_ = lean_box(0);
                        v_isShared_1754_ = v_isSharedCheck_1777_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1738_);
                    lean_dec(v_generation_1737_);
                    v_a_1779_ = lean_ctor_get(v___x_1751_, 0);
                    v_isSharedCheck_1786_ = (!lean_is_exclusive(v___x_1751_)) as u8;
                    if v_isSharedCheck_1786_ == 0 {
                        v___x_1781_ = v___x_1751_;
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1779_);
                        lean_dec(v___x_1751_);
                        v___x_1781_ = lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_skipVar_1736_ == 0 {
                    lean_del_object(v___x_1753_);
                    v___x_1755_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1737_, v_e_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
                    if lean_obj_tag(v___x_1755_) == 0 {
                        v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
                        v_isSharedCheck_1764_ = (!lean_is_exclusive(v___x_1755_)) as u8;
                        if v_isSharedCheck_1764_ == 0 {
                            v___x_1758_ = v___x_1755_;
                            v_isShared_1759_ = v_isSharedCheck_1764_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1756_);
                            lean_dec(v___x_1755_);
                            v___x_1758_ = lean_box(0);
                            v_isShared_1759_ = v_isSharedCheck_1764_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1765_ = lean_ctor_get(v___x_1755_, 0);
                        v_isSharedCheck_1772_ = (!lean_is_exclusive(v___x_1755_)) as u8;
                        if v_isSharedCheck_1772_ == 0 {
                            v___x_1767_ = v___x_1755_;
                            v_isShared_1768_ = v_isSharedCheck_1772_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1765_);
                            lean_dec(v___x_1755_);
                            v___x_1767_ = lean_box(0);
                            v_isShared_1768_ = v_isSharedCheck_1772_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1738_);
                    lean_dec(v_generation_1737_);
                    v___x_1773_ = lean_box(0);
                    if v_isShared_1754_ == 0 {
                        lean_ctor_set(v___x_1753_, 0, v___x_1773_);
                        v___x_1775_ = v___x_1753_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
                        v___x_1775_ = v_reuseFailAlloc_1776_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1760_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1760_, 0, v_a_1756_);
                if v_isShared_1759_ == 0 {
                    lean_ctor_set(v___x_1758_, 0, v___x_1760_);
                    v___x_1762_ = v___x_1758_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
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
                    v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
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
                    v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
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
    mut v_skipVar_1787_: *mut LeanObject,
    mut v_generation_1788_: *mut LeanObject,
    mut v_e_1789_: *mut LeanObject,
    mut v_a_1790_: *mut LeanObject,
    mut v_a_1791_: *mut LeanObject,
    mut v_a_1792_: *mut LeanObject,
    mut v_a_1793_: *mut LeanObject,
    mut v_a_1794_: *mut LeanObject,
    mut v_a_1795_: *mut LeanObject,
    mut v_a_1796_: *mut LeanObject,
    mut v_a_1797_: *mut LeanObject,
    mut v_a_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
    mut v_a_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipVar_boxed_1802_: u8 = 0;
    let mut v_res_1803_: *mut LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_1802_ = (lean_unbox(v_skipVar_1787_) as u8);
    v_res_1803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_boxed_1802_, v_generation_1788_, v_e_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
    lean_dec(v_a_1800_);
    lean_dec_ref(v_a_1799_);
    lean_dec(v_a_1798_);
    lean_dec_ref(v_a_1797_);
    lean_dec(v_a_1796_);
    lean_dec_ref(v_a_1795_);
    lean_dec(v_a_1794_);
    lean_dec_ref(v_a_1793_);
    lean_dec(v_a_1792_);
    lean_dec(v_a_1791_);
    lean_dec(v_a_1790_);
    return v_res_1803_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(
    mut v_e_1804_: *mut LeanObject,
    mut v_a_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
    mut v_a_1809_: *mut LeanObject,
    mut v_a_1810_: *mut LeanObject,
    mut v_a_1811_: *mut LeanObject,
    mut v_a_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1817_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_,
                    v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_,
                );
                if lean_obj_tag(v___x_1817_) == 0 {
                    v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
                    lean_inc(v_a_1818_);
                    lean_dec_ref_known(v___x_1817_, 1);
                    v_ofNatZero_1819_ = lean_ctor_get(v_a_1818_, 18);
                    lean_inc_ref(v_ofNatZero_1819_);
                    lean_dec(v_a_1818_);
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
                    lean_dec_ref(v_e_1804_);
                    v_a_1821_ = lean_ctor_get(v___x_1817_, 0);
                    v_isSharedCheck_1828_ = (!lean_is_exclusive(v___x_1817_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v___x_1817_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1821_);
                        lean_dec(v___x_1817_);
                        v___x_1823_ = lean_box(0);
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
                    v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
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
    mut v_e_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1842_: *mut LeanObject = core::ptr::null_mut();
    v_res_1842_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
    lean_dec(v_a_1840_);
    lean_dec_ref(v_a_1839_);
    lean_dec(v_a_1838_);
    lean_dec_ref(v_a_1837_);
    lean_dec(v_a_1836_);
    lean_dec_ref(v_a_1835_);
    lean_dec(v_a_1834_);
    lean_dec_ref(v_a_1833_);
    lean_dec(v_a_1832_);
    lean_dec(v_a_1831_);
    lean_dec(v_a_1830_);
    return v_res_1842_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(
    mut v_generation_1878_: *mut LeanObject,
    mut v_e_1879_: *mut LeanObject,
    mut v_a_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
    mut v_a_1882_: *mut LeanObject,
    mut v_a_1883_: *mut LeanObject,
    mut v_a_1884_: *mut LeanObject,
    mut v_a_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
    mut v_a_1889_: *mut LeanObject,
    mut v_a_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: u8 = 0;
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: u8 = 0;
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: u8 = 0;
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: u8 = 0;
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: u8 = 0;
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut v_a_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1950_: u8 = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1954_: u8 = 0;
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1965_: u8 = 0;
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1970_: u8 = 0;
    let mut v_a_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1974_: u8 = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v_val_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut v_a_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1997_: u8 = 0;
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_a_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v_a_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2043_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut v_orderedRingInst_x3f_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2063_: u8 = 0;
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut v_a_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2079_: u8 = 0;
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2083_: u8 = 0;
    let mut v_a_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2087_: u8 = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1879_);
                v___x_1892_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1879_, v_a_1888_);
                if lean_obj_tag(v___x_1892_) == 0 {
                    v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
                    lean_inc(v_a_1893_);
                    lean_dec_ref_known(v___x_1892_, 1);
                    v___x_1894_ = l_Lean_Expr_cleanupAnnotations(v_a_1893_);
                    v___x_1895_ = l_Lean_Expr_isApp(v___x_1894_);
                    if v___x_1895_ == 0 {
                        lean_dec_ref(v___x_1894_);
                        v___x_1896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                        return v___x_1896_;
                    } else {
                        v_arg_1897_ = lean_ctor_get(v___x_1894_, 1);
                        lean_inc_ref(v_arg_1897_);
                        v___x_1898_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1894_);
                        v___x_1899_ = l_Lean_Expr_isApp(v___x_1898_);
                        if v___x_1899_ == 0 {
                            lean_dec_ref(v___x_1898_);
                            lean_dec_ref(v_arg_1897_);
                            v___x_1900_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                            return v___x_1900_;
                        } else {
                            v_arg_1901_ = lean_ctor_get(v___x_1898_, 1);
                            lean_inc_ref(v_arg_1901_);
                            v___x_1902_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1898_);
                            v___x_1903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2;
                            v___x_1904_ = l_Lean_Expr_isConstOf(v___x_1902_, v___x_1903_);
                            if v___x_1904_ == 0 {
                                v___x_1905_ = l_Lean_Expr_isApp(v___x_1902_);
                                if v___x_1905_ == 0 {
                                    lean_dec_ref(v___x_1902_);
                                    lean_dec_ref(v_arg_1901_);
                                    lean_dec_ref(v_arg_1897_);
                                    v___x_1906_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                    return v___x_1906_;
                                } else {
                                    v_arg_1907_ = lean_ctor_get(v___x_1902_, 1);
                                    lean_inc_ref(v_arg_1907_);
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
                                                    lean_dec_ref(v___x_1908_);
                                                    lean_dec_ref(v_arg_1907_);
                                                    lean_dec_ref(v_arg_1901_);
                                                    lean_dec_ref(v_arg_1897_);
                                                    v___x_1916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                    return v___x_1916_;
                                                } else {
                                                    v___x_1917_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1908_,
                                                    );
                                                    v___x_1918_ = l_Lean_Expr_isApp(v___x_1917_);
                                                    if v___x_1918_ == 0 {
                                                        lean_dec_ref(v___x_1917_);
                                                        lean_dec_ref(v_arg_1907_);
                                                        lean_dec_ref(v_arg_1901_);
                                                        lean_dec_ref(v_arg_1897_);
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
                                                            lean_dec_ref(v___x_1920_);
                                                            lean_dec_ref(v_arg_1907_);
                                                            lean_dec_ref(v_arg_1901_);
                                                            lean_dec_ref(v_arg_1897_);
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
                                                                    lean_dec_ref(v___x_1923_);
                                                                    if v___x_1929_ == 0 {
                                                                        lean_dec_ref(v_arg_1907_);
                                                                        lean_dec_ref(v_arg_1901_);
                                                                        lean_dec_ref(v_arg_1897_);
                                                                        v___x_1930_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                        return v___x_1930_;
                                                                    } else {
                                                                        v___x_1931_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                        if lean_obj_tag(v___x_1931_)
                                                                            == 0
                                                                        {
                                                                            v_a_1932_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1931_,
                                                                                    0,
                                                                                );
                                                                            lean_inc(v_a_1932_);
                                                                            lean_dec_ref_known(
                                                                                v___x_1931_,
                                                                                1,
                                                                            );
                                                                            v___x_1933_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1932_, v_arg_1907_);
                                                                            lean_dec_ref(
                                                                                v_arg_1907_,
                                                                            );
                                                                            lean_dec(v_a_1932_);
                                                                            if v___x_1933_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v_arg_1901_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1897_,
                                                                                );
                                                                                v___x_1934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                                return v___x_1934_;
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_e_1879_,
                                                                                );
                                                                                lean_inc(v_generation_1878_);
                                                                                v___x_1935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1901_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                                if lean_obj_tag(
                                                                                    v___x_1935_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
                                                                                    lean_inc(
                                                                                        v_a_1936_,
                                                                                    );
                                                                                    lean_dec_ref_known(v___x_1935_, 1);
                                                                                    v___x_1937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                                    if lean_obj_tag(
                                                                                        v___x_1937_,
                                                                                    ) == 0
                                                                                    {
                                                                                        v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
                                                                                        v_isSharedCheck_1946_ = (!lean_is_exclusive(v___x_1937_)) as u8;
                                                                                        if v_isSharedCheck_1946_ == 0 {
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1946_;
state = 1; continue;
} else {
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1946_;
state = 1; continue;
}
                                                                                    } else {
                                                                                        lean_dec(v_a_1936_);
                                                                                        return v___x_1937_;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_arg_1897_,
                                                                                    );
                                                                                    lean_dec(v_generation_1878_);
                                                                                    return v___x_1935_;
                                                                                }
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_1907_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1901_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1897_,
                                                                            );
                                                                            lean_dec_ref(v_e_1879_);
                                                                            lean_dec(
                                                                                v_generation_1878_,
                                                                            );
                                                                            v_a_1947_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1931_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_1954_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_1931_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_1954_
                                                                                == 0
                                                                            {
                                                                                v___x_1949_ =
                                                                                    v___x_1931_;
                                                                                v_isShared_1950_ = v_isSharedCheck_1954_;
                                                                                state = 3;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_1947_);
                                                                                lean_dec(
                                                                                    v___x_1931_,
                                                                                );
                                                                                v___x_1949_ =
                                                                                    lean_box(0);
                                                                                v_isShared_1950_ = v_isSharedCheck_1954_;
                                                                                state = 3;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v___x_1923_);
                                                                    v___x_1955_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                    if lean_obj_tag(v___x_1955_)
                                                                        == 0
                                                                    {
                                                                        v_a_1956_ = lean_ctor_get(
                                                                            v___x_1955_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_1956_);
                                                                        lean_dec_ref_known(
                                                                            v___x_1955_,
                                                                            1,
                                                                        );
                                                                        v___x_1957_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_1956_, v_arg_1907_);
                                                                        lean_dec_ref(v_arg_1907_);
                                                                        lean_dec(v_a_1956_);
                                                                        if v___x_1957_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_arg_1901_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1897_,
                                                                            );
                                                                            v___x_1958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                            return v___x_1958_;
                                                                        } else {
                                                                            lean_dec_ref(v_e_1879_);
                                                                            lean_inc(
                                                                                v_generation_1878_,
                                                                            );
                                                                            v___x_1959_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1901_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                            if lean_obj_tag(
                                                                                v___x_1959_,
                                                                            ) == 0
                                                                            {
                                                                                v_a_1960_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_1959_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc(v_a_1960_);
                                                                                lean_dec_ref_known(
                                                                                    v___x_1959_,
                                                                                    1,
                                                                                );
                                                                                v___x_1961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                                if lean_obj_tag(
                                                                                    v___x_1961_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
                                                                                    v_isSharedCheck_1970_ = (!lean_is_exclusive(v___x_1961_)) as u8;
                                                                                    if v_isSharedCheck_1970_ == 0 {
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1970_;
state = 5; continue;
} else {
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
state = 5; continue;
}
                                                                                } else {
                                                                                    lean_dec(
                                                                                        v_a_1960_,
                                                                                    );
                                                                                    return v___x_1961_;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_1897_,
                                                                                );
                                                                                lean_dec(v_generation_1878_);
                                                                                return v___x_1959_;
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_1907_);
                                                                        lean_dec_ref(v_arg_1901_);
                                                                        lean_dec_ref(v_arg_1897_);
                                                                        lean_dec_ref(v_e_1879_);
                                                                        lean_dec(
                                                                            v_generation_1878_,
                                                                        );
                                                                        v_a_1971_ = lean_ctor_get(
                                                                            v___x_1955_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_1978_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_1955_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_1978_
                                                                            == 0
                                                                        {
                                                                            v___x_1973_ =
                                                                                v___x_1955_;
                                                                            v_isShared_1974_ = v_isSharedCheck_1978_;
                                                                            state = 7;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_1971_);
                                                                            lean_dec(v___x_1955_);
                                                                            v___x_1973_ =
                                                                                lean_box(0);
                                                                            v_isShared_1974_ = v_isSharedCheck_1978_;
                                                                            state = 7;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_1923_);
                                                                lean_inc(v_generation_1878_);
                                                                v___x_1979_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_1878_, v_arg_1907_, v_arg_1901_, v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                                lean_dec_ref(v_arg_1907_);
                                                                if lean_obj_tag(v___x_1979_) == 0 {
                                                                    v_a_1980_ = lean_ctor_get(
                                                                        v___x_1979_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_1989_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_1979_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_1989_ == 0 {
                                                                        v___x_1982_ = v___x_1979_;
                                                                        v_isShared_1983_ =
                                                                            v_isSharedCheck_1989_;
                                                                        state = 9;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_1980_);
                                                                        lean_dec(v___x_1979_);
                                                                        v___x_1982_ = lean_box(0);
                                                                        v_isShared_1983_ =
                                                                            v_isSharedCheck_1989_;
                                                                        state = 9;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_e_1879_);
                                                                    lean_dec(v_generation_1878_);
                                                                    v_a_1990_ = lean_ctor_get(
                                                                        v___x_1979_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_1997_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_1979_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_1997_ == 0 {
                                                                        v___x_1992_ = v___x_1979_;
                                                                        v_isShared_1993_ =
                                                                            v_isSharedCheck_1997_;
                                                                        state = 11;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_1990_);
                                                                        lean_dec(v___x_1979_);
                                                                        v___x_1992_ = lean_box(0);
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
                                                lean_dec_ref(v___x_1908_);
                                                lean_dec_ref(v_arg_1907_);
                                                v___x_1998_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                if lean_obj_tag(v___x_1998_) == 0 {
                                                    v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
                                                    lean_inc(v_a_1999_);
                                                    lean_dec_ref_known(v___x_1998_, 1);
                                                    v___x_2000_ =
                                                        l_Lean_Meta_Grind_Arith_Linear_isNegInst(
                                                            v_a_1999_,
                                                            v_arg_1901_,
                                                        );
                                                    lean_dec_ref(v_arg_1901_);
                                                    lean_dec(v_a_1999_);
                                                    if v___x_2000_ == 0 {
                                                        lean_dec_ref(v_arg_1897_);
                                                        v___x_2001_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                        return v___x_2001_;
                                                    } else {
                                                        lean_dec_ref(v_e_1879_);
                                                        v___x_2002_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_1878_, v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                                        if lean_obj_tag(v___x_2002_) == 0 {
                                                            v_a_2003_ =
                                                                lean_ctor_get(v___x_2002_, 0);
                                                            v_isSharedCheck_2011_ =
                                                                (!lean_is_exclusive(v___x_2002_))
                                                                    as u8;
                                                            if v_isSharedCheck_2011_ == 0 {
                                                                v___x_2005_ = v___x_2002_;
                                                                v_isShared_2006_ =
                                                                    v_isSharedCheck_2011_;
                                                                state = 13;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2003_);
                                                                lean_dec(v___x_2002_);
                                                                v___x_2005_ = lean_box(0);
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
                                                    lean_dec_ref(v_arg_1901_);
                                                    lean_dec_ref(v_arg_1897_);
                                                    lean_dec_ref(v_e_1879_);
                                                    lean_dec(v_generation_1878_);
                                                    v_a_2012_ = lean_ctor_get(v___x_1998_, 0);
                                                    v_isSharedCheck_2019_ =
                                                        (!lean_is_exclusive(v___x_1998_)) as u8;
                                                    if v_isSharedCheck_2019_ == 0 {
                                                        v___x_2014_ = v___x_1998_;
                                                        v_isShared_2015_ = v_isSharedCheck_2019_;
                                                        state = 15;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2012_);
                                                        lean_dec(v___x_1998_);
                                                        v___x_2014_ = lean_box(0);
                                                        v_isShared_2015_ = v_isSharedCheck_2019_;
                                                        state = 15;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_1908_);
                                            lean_dec_ref(v_arg_1907_);
                                            lean_dec_ref(v_arg_1901_);
                                            lean_dec_ref(v_arg_1897_);
                                            lean_inc_ref(v_e_1879_);
                                            v___x_2020_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                                            if lean_obj_tag(v___x_2020_) == 0 {
                                                v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
                                                v_isSharedCheck_2031_ =
                                                    (!lean_is_exclusive(v___x_2020_)) as u8;
                                                if v_isSharedCheck_2031_ == 0 {
                                                    v___x_2023_ = v___x_2020_;
                                                    v_isShared_2024_ = v_isSharedCheck_2031_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2021_);
                                                    lean_dec(v___x_2020_);
                                                    v___x_2023_ = lean_box(0);
                                                    v_isShared_2024_ = v_isSharedCheck_2031_;
                                                    state = 17;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_e_1879_);
                                                lean_dec(v_generation_1878_);
                                                v_a_2032_ = lean_ctor_get(v___x_2020_, 0);
                                                v_isSharedCheck_2039_ =
                                                    (!lean_is_exclusive(v___x_2020_)) as u8;
                                                if v_isSharedCheck_2039_ == 0 {
                                                    v___x_2034_ = v___x_2020_;
                                                    v_isShared_2035_ = v_isSharedCheck_2039_;
                                                    state = 19;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2032_);
                                                    lean_dec(v___x_2020_);
                                                    v___x_2034_ = lean_box(0);
                                                    v_isShared_2035_ = v_isSharedCheck_2039_;
                                                    state = 19;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_1908_);
                                        lean_dec_ref(v_arg_1907_);
                                        lean_dec_ref(v_arg_1901_);
                                        v___x_2040_ =
                                            l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                                v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_,
                                                v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_,
                                                v_a_1888_, v_a_1889_, v_a_1890_,
                                            );
                                        if lean_obj_tag(v___x_2040_) == 0 {
                                            v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
                                            lean_inc(v_a_2041_);
                                            lean_dec_ref_known(v___x_2040_, 1);
                                            v_orderedRingInst_x3f_2055_ =
                                                lean_ctor_get(v_a_2041_, 14);
                                            lean_inc(v_orderedRingInst_x3f_2055_);
                                            lean_dec(v_a_2041_);
                                            if lean_obj_tag(v_orderedRingInst_x3f_2055_) == 0 {
                                                v___y_2043_ = v___x_1904_;
                                                state = 21;
                                                continue;
                                            } else {
                                                lean_dec_ref_known(v_orderedRingInst_x3f_2055_, 1);
                                                v___y_2043_ = v___x_1910_;
                                                state = 21;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_1897_);
                                            lean_dec_ref(v_e_1879_);
                                            lean_dec(v_generation_1878_);
                                            v_a_2056_ = lean_ctor_get(v___x_2040_, 0);
                                            v_isSharedCheck_2063_ =
                                                (!lean_is_exclusive(v___x_2040_)) as u8;
                                            if v_isSharedCheck_2063_ == 0 {
                                                v___x_2058_ = v___x_2040_;
                                                v_isShared_2059_ = v_isSharedCheck_2063_;
                                                state = 24;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2056_);
                                                lean_dec(v___x_2040_);
                                                v___x_2058_ = lean_box(0);
                                                v_isShared_2059_ = v_isSharedCheck_2063_;
                                                state = 24;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_1902_);
                                lean_dec_ref(v_arg_1901_);
                                v___x_2064_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                    v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_,
                                    v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_,
                                    v_a_1890_,
                                );
                                if lean_obj_tag(v___x_2064_) == 0 {
                                    v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
                                    v_isSharedCheck_2075_ = (!lean_is_exclusive(v___x_2064_)) as u8;
                                    if v_isSharedCheck_2075_ == 0 {
                                        v___x_2067_ = v___x_2064_;
                                        v_isShared_2068_ = v_isSharedCheck_2075_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2065_);
                                        lean_dec(v___x_2064_);
                                        v___x_2067_ = lean_box(0);
                                        v_isShared_2068_ = v_isSharedCheck_2075_;
                                        state = 26;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_1897_);
                                    lean_dec_ref(v_e_1879_);
                                    lean_dec(v_generation_1878_);
                                    v_a_2076_ = lean_ctor_get(v___x_2064_, 0);
                                    v_isSharedCheck_2083_ = (!lean_is_exclusive(v___x_2064_)) as u8;
                                    if v_isSharedCheck_2083_ == 0 {
                                        v___x_2078_ = v___x_2064_;
                                        v_isShared_2079_ = v_isSharedCheck_2083_;
                                        state = 28;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2076_);
                                        lean_dec(v___x_2064_);
                                        v___x_2078_ = lean_box(0);
                                        v_isShared_2079_ = v_isSharedCheck_2083_;
                                        state = 28;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1879_);
                    lean_dec(v_generation_1878_);
                    v_a_2084_ = lean_ctor_get(v___x_1892_, 0);
                    v_isSharedCheck_2091_ = (!lean_is_exclusive(v___x_1892_)) as u8;
                    if v_isSharedCheck_2091_ == 0 {
                        v___x_2086_ = v___x_1892_;
                        v_isShared_2087_ = v_isSharedCheck_2091_;
                        state = 30;
                        continue;
                    } else {
                        lean_inc(v_a_2084_);
                        lean_dec(v___x_1892_);
                        v___x_2086_ = lean_box(0);
                        v_isShared_2087_ = v_isSharedCheck_2091_;
                        state = 30;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1942_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1942_, 0, v_a_1936_);
                lean_ctor_set(v___x_1942_, 1, v_a_1938_);
                if v_isShared_1941_ == 0 {
                    lean_ctor_set(v___x_1940_, 0, v___x_1942_);
                    v___x_1944_ = v___x_1940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
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
                    v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
                    v___x_1952_ = v_reuseFailAlloc_1953_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1952_;
            }
            5 => {
                v___x_1966_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_1966_, 0, v_a_1960_);
                lean_ctor_set(v___x_1966_, 1, v_a_1962_);
                if v_isShared_1965_ == 0 {
                    lean_ctor_set(v___x_1964_, 0, v___x_1966_);
                    v___x_1968_ = v___x_1964_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
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
                    v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
                    v___x_1976_ = v_reuseFailAlloc_1977_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1976_;
            }
            9 => {
                if lean_obj_tag(v_a_1980_) == 1 {
                    lean_dec_ref(v_e_1879_);
                    lean_dec(v_generation_1878_);
                    v_val_1984_ = lean_ctor_get(v_a_1980_, 0);
                    lean_inc(v_val_1984_);
                    lean_dec_ref_known(v_a_1980_, 1);
                    if v_isShared_1983_ == 0 {
                        lean_ctor_set(v___x_1982_, 0, v_val_1984_);
                        v___x_1986_ = v___x_1982_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_val_1984_);
                        v___x_1986_ = v_reuseFailAlloc_1987_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1982_);
                    lean_dec(v_a_1980_);
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
                    v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
                    v___x_1995_ = v_reuseFailAlloc_1996_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1995_;
            }
            13 => {
                v___x_2007_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_2007_, 0, v_a_2003_);
                if v_isShared_2006_ == 0 {
                    lean_ctor_set(v___x_2005_, 0, v___x_2007_);
                    v___x_2009_ = v___x_2005_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
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
                    v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2018_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2017_;
            }
            17 => {
                v___x_2025_ = (lean_unbox(v_a_2021_) as u8);
                lean_dec(v_a_2021_);
                if v___x_2025_ == 0 {
                    lean_del_object(v___x_2023_);
                    v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    return v___x_2026_;
                } else {
                    lean_dec_ref(v_e_1879_);
                    lean_dec(v_generation_1878_);
                    v___x_2027_ = lean_box(0);
                    if v_isShared_2024_ == 0 {
                        lean_ctor_set(v___x_2023_, 0, v___x_2027_);
                        v___x_2029_ = v___x_2023_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
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
                    v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
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
                    lean_dec_ref(v_arg_1897_);
                    v___x_2044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    return v___x_2044_;
                } else {
                    v___x_2045_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_1897_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    if lean_obj_tag(v___x_2045_) == 0 {
                        lean_dec_ref_known(v___x_2045_, 1);
                        v___x_2046_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                        return v___x_2046_;
                    } else {
                        lean_dec_ref(v_e_1879_);
                        lean_dec(v_generation_1878_);
                        v_a_2047_ = lean_ctor_get(v___x_2045_, 0);
                        v_isSharedCheck_2054_ = (!lean_is_exclusive(v___x_2045_)) as u8;
                        if v_isSharedCheck_2054_ == 0 {
                            v___x_2049_ = v___x_2045_;
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_2047_);
                            lean_dec(v___x_2045_);
                            v___x_2049_ = lean_box(0);
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
                    v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
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
                    v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
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
                lean_dec_ref(v_arg_1897_);
                lean_dec(v_a_2065_);
                if v___x_2069_ == 0 {
                    lean_del_object(v___x_2067_);
                    v___x_2070_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asVar(v_generation_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
                    return v___x_2070_;
                } else {
                    lean_dec_ref(v_e_1879_);
                    lean_dec(v_generation_1878_);
                    v___x_2071_ = lean_box(0);
                    if v_isShared_2068_ == 0 {
                        lean_ctor_set(v___x_2067_, 0, v___x_2071_);
                        v___x_2073_ = v___x_2067_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
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
                    v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
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
                    v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
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
    mut v_generation_2092_: *mut LeanObject,
    mut v_i_2093_: *mut LeanObject,
    mut v_a_2094_: *mut LeanObject,
    mut v_b_2095_: *mut LeanObject,
    mut v_a_2096_: *mut LeanObject,
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
    mut v_a_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
    mut v_a_2103_: *mut LeanObject,
    mut v_a_2104_: *mut LeanObject,
    mut v_a_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: u8 = 0;
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: u8 = 0;
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2125_: u8 = 0;
    let mut v_val_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2129_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2134_: u8 = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2142_: u8 = 0;
    let mut v_a_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_isSharedCheck_2151_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut v_a_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2160_: u8 = 0;
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut v_isSharedCheck_2165_: u8 = 0;
    let mut v_a_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2169_: u8 = 0;
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2178_: u8 = 0;
    let mut v_val_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2195_: u8 = 0;
    let mut v_a_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2108_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_,
                    v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_,
                );
                if lean_obj_tag(v___x_2108_) == 0 {
                    v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
                    lean_inc(v_a_2109_);
                    lean_dec_ref_known(v___x_2108_, 1);
                    v___x_2110_ =
                        l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_2109_, v_i_2093_);
                    lean_dec(v_a_2109_);
                    if v___x_2110_ == 0 {
                        v___x_2111_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                            v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_,
                            v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_,
                        );
                        if lean_obj_tag(v___x_2111_) == 0 {
                            v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
                            v_isSharedCheck_2165_ = (!lean_is_exclusive(v___x_2111_)) as u8;
                            if v_isSharedCheck_2165_ == 0 {
                                v___x_2114_ = v___x_2111_;
                                v_isShared_2115_ = v_isSharedCheck_2165_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2112_);
                                lean_dec(v___x_2111_);
                                v___x_2114_ = lean_box(0);
                                v_isShared_2115_ = v_isSharedCheck_2165_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_2095_);
                            lean_dec_ref(v_a_2094_);
                            lean_dec(v_generation_2092_);
                            v_a_2166_ = lean_ctor_get(v___x_2111_, 0);
                            v_isSharedCheck_2173_ = (!lean_is_exclusive(v___x_2111_)) as u8;
                            if v_isSharedCheck_2173_ == 0 {
                                v___x_2168_ = v___x_2111_;
                                v_isShared_2169_ = v_isSharedCheck_2173_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_2166_);
                                lean_dec(v___x_2111_);
                                v___x_2168_ = lean_box(0);
                                v_isShared_2169_ = v_isSharedCheck_2173_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v___x_2174_ = l_Lean_Meta_getIntValue_x3f(
                            v_a_2094_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_,
                        );
                        if lean_obj_tag(v___x_2174_) == 0 {
                            v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
                            v_isSharedCheck_2209_ = (!lean_is_exclusive(v___x_2174_)) as u8;
                            if v_isSharedCheck_2209_ == 0 {
                                v___x_2177_ = v___x_2174_;
                                v_isShared_2178_ = v_isSharedCheck_2209_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_2175_);
                                lean_dec(v___x_2174_);
                                v___x_2177_ = lean_box(0);
                                v_isShared_2178_ = v_isSharedCheck_2209_;
                                state = 15;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_2095_);
                            lean_dec(v_generation_2092_);
                            v_a_2210_ = lean_ctor_get(v___x_2174_, 0);
                            v_isSharedCheck_2217_ = (!lean_is_exclusive(v___x_2174_)) as u8;
                            if v_isSharedCheck_2217_ == 0 {
                                v___x_2212_ = v___x_2174_;
                                v_isShared_2213_ = v_isSharedCheck_2217_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_2210_);
                                lean_dec(v___x_2174_);
                                v___x_2212_ = lean_box(0);
                                v_isShared_2213_ = v_isSharedCheck_2217_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_b_2095_);
                    lean_dec_ref(v_a_2094_);
                    lean_dec(v_generation_2092_);
                    v_a_2218_ = lean_ctor_get(v___x_2108_, 0);
                    v_isSharedCheck_2225_ = (!lean_is_exclusive(v___x_2108_)) as u8;
                    if v_isSharedCheck_2225_ == 0 {
                        v___x_2220_ = v___x_2108_;
                        v_isShared_2221_ = v_isSharedCheck_2225_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_2218_);
                        lean_dec(v___x_2108_);
                        v___x_2220_ = lean_box(0);
                        v_isShared_2221_ = v_isSharedCheck_2225_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2116_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_a_2112_, v_i_2093_);
                lean_dec(v_a_2112_);
                if v___x_2116_ == 0 {
                    lean_dec_ref(v_b_2095_);
                    lean_dec_ref(v_a_2094_);
                    lean_dec(v_generation_2092_);
                    v___x_2117_ = lean_box(0);
                    if v_isShared_2115_ == 0 {
                        lean_ctor_set(v___x_2114_, 0, v___x_2117_);
                        v___x_2119_ = v___x_2114_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
                        v___x_2119_ = v_reuseFailAlloc_2120_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2114_);
                    v___x_2121_ = l_Lean_Meta_getNatValue_x3f(
                        v_a_2094_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_,
                    );
                    lean_dec_ref(v_a_2094_);
                    if lean_obj_tag(v___x_2121_) == 0 {
                        v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
                        v_isSharedCheck_2156_ = (!lean_is_exclusive(v___x_2121_)) as u8;
                        if v_isSharedCheck_2156_ == 0 {
                            v___x_2124_ = v___x_2121_;
                            v_isShared_2125_ = v_isSharedCheck_2156_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2122_);
                            lean_dec(v___x_2121_);
                            v___x_2124_ = lean_box(0);
                            v_isShared_2125_ = v_isSharedCheck_2156_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_2095_);
                        lean_dec(v_generation_2092_);
                        v_a_2157_ = lean_ctor_get(v___x_2121_, 0);
                        v_isSharedCheck_2164_ = (!lean_is_exclusive(v___x_2121_)) as u8;
                        if v_isSharedCheck_2164_ == 0 {
                            v___x_2159_ = v___x_2121_;
                            v_isShared_2160_ = v_isSharedCheck_2164_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_2157_);
                            lean_dec(v___x_2121_);
                            v___x_2159_ = lean_box(0);
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
                if lean_obj_tag(v_a_2122_) == 1 {
                    lean_del_object(v___x_2124_);
                    v_val_2126_ = lean_ctor_get(v_a_2122_, 0);
                    v_isSharedCheck_2151_ = (!lean_is_exclusive(v_a_2122_)) as u8;
                    if v_isSharedCheck_2151_ == 0 {
                        v___x_2128_ = v_a_2122_;
                        v_isShared_2129_ = v_isSharedCheck_2151_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_2126_);
                        lean_dec(v_a_2122_);
                        v___x_2128_ = lean_box(0);
                        v_isShared_2129_ = v_isSharedCheck_2151_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2122_);
                    lean_dec_ref(v_b_2095_);
                    lean_dec(v_generation_2092_);
                    v___x_2152_ = lean_box(0);
                    if v_isShared_2125_ == 0 {
                        lean_ctor_set(v___x_2124_, 0, v___x_2152_);
                        v___x_2154_ = v___x_2124_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
                        v___x_2154_ = v_reuseFailAlloc_2155_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2130_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2092_, v_b_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
                if lean_obj_tag(v___x_2130_) == 0 {
                    v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
                    v_isSharedCheck_2142_ = (!lean_is_exclusive(v___x_2130_)) as u8;
                    if v_isSharedCheck_2142_ == 0 {
                        v___x_2133_ = v___x_2130_;
                        v_isShared_2134_ = v_isSharedCheck_2142_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2131_);
                        lean_dec(v___x_2130_);
                        v___x_2133_ = lean_box(0);
                        v_isShared_2134_ = v_isSharedCheck_2142_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2128_);
                    lean_dec(v_val_2126_);
                    v_a_2143_ = lean_ctor_get(v___x_2130_, 0);
                    v_isSharedCheck_2150_ = (!lean_is_exclusive(v___x_2130_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v___x_2145_ = v___x_2130_;
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2143_);
                        lean_dec(v___x_2130_);
                        v___x_2145_ = lean_box(0);
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2135_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2135_, 0, v_val_2126_);
                lean_ctor_set(v___x_2135_, 1, v_a_2131_);
                if v_isShared_2129_ == 0 {
                    lean_ctor_set(v___x_2128_, 0, v___x_2135_);
                    v___x_2137_ = v___x_2128_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2135_);
                    v___x_2137_ = v_reuseFailAlloc_2141_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2134_ == 0 {
                    lean_ctor_set(v___x_2133_, 0, v___x_2137_);
                    v___x_2139_ = v___x_2133_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
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
                    v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
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
                    v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
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
                    v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
                    v___x_2171_ = v_reuseFailAlloc_2172_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2171_;
            }
            15 => {
                if lean_obj_tag(v_a_2175_) == 1 {
                    lean_del_object(v___x_2177_);
                    v_val_2179_ = lean_ctor_get(v_a_2175_, 0);
                    v_isSharedCheck_2204_ = (!lean_is_exclusive(v_a_2175_)) as u8;
                    if v_isSharedCheck_2204_ == 0 {
                        v___x_2181_ = v_a_2175_;
                        v_isShared_2182_ = v_isSharedCheck_2204_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_val_2179_);
                        lean_dec(v_a_2175_);
                        v___x_2181_ = lean_box(0);
                        v_isShared_2182_ = v_isSharedCheck_2204_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2175_);
                    lean_dec_ref(v_b_2095_);
                    lean_dec(v_generation_2092_);
                    v___x_2205_ = lean_box(0);
                    if v_isShared_2178_ == 0 {
                        lean_ctor_set(v___x_2177_, 0, v___x_2205_);
                        v___x_2207_ = v___x_2177_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
                        v___x_2207_ = v_reuseFailAlloc_2208_;
                        state = 22;
                        continue;
                    }
                }
            }
            16 => {
                v___x_2183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2092_, v_b_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
                if lean_obj_tag(v___x_2183_) == 0 {
                    v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
                    v_isSharedCheck_2195_ = (!lean_is_exclusive(v___x_2183_)) as u8;
                    if v_isSharedCheck_2195_ == 0 {
                        v___x_2186_ = v___x_2183_;
                        v_isShared_2187_ = v_isSharedCheck_2195_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_2184_);
                        lean_dec(v___x_2183_);
                        v___x_2186_ = lean_box(0);
                        v_isShared_2187_ = v_isSharedCheck_2195_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2181_);
                    lean_dec(v_val_2179_);
                    v_a_2196_ = lean_ctor_get(v___x_2183_, 0);
                    v_isSharedCheck_2203_ = (!lean_is_exclusive(v___x_2183_)) as u8;
                    if v_isSharedCheck_2203_ == 0 {
                        v___x_2198_ = v___x_2183_;
                        v_isShared_2199_ = v_isSharedCheck_2203_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_2196_);
                        lean_dec(v___x_2183_);
                        v___x_2198_ = lean_box(0);
                        v_isShared_2199_ = v_isSharedCheck_2203_;
                        state = 20;
                        continue;
                    }
                }
            }
            17 => {
                v___x_2188_ = lean_alloc_ctor(6, 2, (0) as u32);
                lean_ctor_set(v___x_2188_, 0, v_val_2179_);
                lean_ctor_set(v___x_2188_, 1, v_a_2184_);
                if v_isShared_2182_ == 0 {
                    lean_ctor_set(v___x_2181_, 0, v___x_2188_);
                    v___x_2190_ = v___x_2181_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2188_);
                    v___x_2190_ = v_reuseFailAlloc_2194_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2187_ == 0 {
                    lean_ctor_set(v___x_2186_, 0, v___x_2190_);
                    v___x_2192_ = v___x_2186_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
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
                    v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
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
                    v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
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
                    v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
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
    mut v_generation_2226_: *mut LeanObject,
    mut v_i_2227_: *mut LeanObject,
    mut v_a_2228_: *mut LeanObject,
    mut v_b_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
    mut v_a_2232_: *mut LeanObject,
    mut v_a_2233_: *mut LeanObject,
    mut v_a_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
    mut v_a_2237_: *mut LeanObject,
    mut v_a_2238_: *mut LeanObject,
    mut v_a_2239_: *mut LeanObject,
    mut v_a_2240_: *mut LeanObject,
    mut v_a_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2242_: *mut LeanObject = core::ptr::null_mut();
    v_res_2242_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_2226_, v_i_2227_, v_a_2228_, v_b_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
    lean_dec(v_a_2240_);
    lean_dec_ref(v_a_2239_);
    lean_dec(v_a_2238_);
    lean_dec_ref(v_a_2237_);
    lean_dec(v_a_2236_);
    lean_dec_ref(v_a_2235_);
    lean_dec(v_a_2234_);
    lean_dec_ref(v_a_2233_);
    lean_dec(v_a_2232_);
    lean_dec(v_a_2231_);
    lean_dec(v_a_2230_);
    lean_dec_ref(v_i_2227_);
    return v_res_2242_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___boxed(
    mut v_generation_2243_: *mut LeanObject,
    mut v_e_2244_: *mut LeanObject,
    mut v_a_2245_: *mut LeanObject,
    mut v_a_2246_: *mut LeanObject,
    mut v_a_2247_: *mut LeanObject,
    mut v_a_2248_: *mut LeanObject,
    mut v_a_2249_: *mut LeanObject,
    mut v_a_2250_: *mut LeanObject,
    mut v_a_2251_: *mut LeanObject,
    mut v_a_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
    mut v_a_2254_: *mut LeanObject,
    mut v_a_2255_: *mut LeanObject,
    mut v_a_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2257_: *mut LeanObject = core::ptr::null_mut();
    v_res_2257_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2243_, v_e_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_);
    lean_dec(v_a_2255_);
    lean_dec_ref(v_a_2254_);
    lean_dec(v_a_2253_);
    lean_dec_ref(v_a_2252_);
    lean_dec(v_a_2251_);
    lean_dec_ref(v_a_2250_);
    lean_dec(v_a_2249_);
    lean_dec_ref(v_a_2248_);
    lean_dec(v_a_2247_);
    lean_dec(v_a_2246_);
    lean_dec(v_a_2245_);
    return v_res_2257_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_reify_x3f(
    mut v_e_2260_: *mut LeanObject,
    mut v_skipVar_2261_: u8,
    mut v_generation_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
    mut v_a_2265_: *mut LeanObject,
    mut v_a_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
    mut v_a_2269_: *mut LeanObject,
    mut v_a_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: u8 = 0;
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: u8 = 0;
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: u8 = 0;
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: u8 = 0;
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_a_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_a_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2346_: u8 = 0;
    let mut v_a_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2350_: u8 = 0;
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2354_: u8 = 0;
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_a_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut v_a_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_a_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2391_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: u8 = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2413_: u8 = 0;
    let mut v_a_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2417_: u8 = 0;
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut v_a_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2425_: u8 = 0;
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut v_a_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2445_: u8 = 0;
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2453_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2460_: u8 = 0;
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2464_: u8 = 0;
    let mut v_orderedRingInst_x3f_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: u8 = 0;
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2485_: u8 = 0;
    let mut v_a_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v_a_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2260_);
                v___x_2275_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2260_, v_a_2271_);
                if lean_obj_tag(v___x_2275_) == 0 {
                    v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
                    lean_inc(v_a_2276_);
                    lean_dec_ref_known(v___x_2275_, 1);
                    v___x_2277_ = l_Lean_Expr_cleanupAnnotations(v_a_2276_);
                    v___x_2278_ = l_Lean_Expr_isApp(v___x_2277_);
                    if v___x_2278_ == 0 {
                        lean_dec_ref(v___x_2277_);
                        v___x_2279_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                        return v___x_2279_;
                    } else {
                        v_arg_2280_ = lean_ctor_get(v___x_2277_, 1);
                        lean_inc_ref(v_arg_2280_);
                        v___x_2281_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2277_);
                        v___x_2282_ = l_Lean_Expr_isApp(v___x_2281_);
                        if v___x_2282_ == 0 {
                            lean_dec_ref(v___x_2281_);
                            lean_dec_ref(v_arg_2280_);
                            v___x_2283_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                            return v___x_2283_;
                        } else {
                            v_arg_2284_ = lean_ctor_get(v___x_2281_, 1);
                            lean_inc_ref(v_arg_2284_);
                            v___x_2285_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2281_);
                            v___x_2286_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go___closed__2;
                            v___x_2287_ = l_Lean_Expr_isConstOf(v___x_2285_, v___x_2286_);
                            if v___x_2287_ == 0 {
                                v___x_2288_ = l_Lean_Expr_isApp(v___x_2285_);
                                if v___x_2288_ == 0 {
                                    lean_dec_ref(v___x_2285_);
                                    lean_dec_ref(v_arg_2284_);
                                    lean_dec_ref(v_arg_2280_);
                                    v___x_2289_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                    return v___x_2289_;
                                } else {
                                    v_arg_2290_ = lean_ctor_get(v___x_2285_, 1);
                                    lean_inc_ref(v_arg_2290_);
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
                                                    lean_dec_ref(v___x_2291_);
                                                    lean_dec_ref(v_arg_2290_);
                                                    lean_dec_ref(v_arg_2284_);
                                                    lean_dec_ref(v_arg_2280_);
                                                    v___x_2299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                    return v___x_2299_;
                                                } else {
                                                    v___x_2300_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_2291_,
                                                    );
                                                    v___x_2301_ = l_Lean_Expr_isApp(v___x_2300_);
                                                    if v___x_2301_ == 0 {
                                                        lean_dec_ref(v___x_2300_);
                                                        lean_dec_ref(v_arg_2290_);
                                                        lean_dec_ref(v_arg_2284_);
                                                        lean_dec_ref(v_arg_2280_);
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
                                                            lean_dec_ref(v___x_2303_);
                                                            lean_dec_ref(v_arg_2290_);
                                                            lean_dec_ref(v_arg_2284_);
                                                            lean_dec_ref(v_arg_2280_);
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
                                                                    lean_dec_ref(v___x_2306_);
                                                                    if v___x_2312_ == 0 {
                                                                        lean_dec_ref(v_arg_2290_);
                                                                        lean_dec_ref(v_arg_2284_);
                                                                        lean_dec_ref(v_arg_2280_);
                                                                        v___x_2313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                        return v___x_2313_;
                                                                    } else {
                                                                        v___x_2314_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                        if lean_obj_tag(v___x_2314_)
                                                                            == 0
                                                                        {
                                                                            v_a_2315_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2314_,
                                                                                    0,
                                                                                );
                                                                            lean_inc(v_a_2315_);
                                                                            lean_dec_ref_known(
                                                                                v___x_2314_,
                                                                                1,
                                                                            );
                                                                            v___x_2316_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_2315_, v_arg_2290_);
                                                                            lean_dec_ref(
                                                                                v_arg_2290_,
                                                                            );
                                                                            lean_dec(v_a_2315_);
                                                                            if v___x_2316_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v_arg_2284_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_2280_,
                                                                                );
                                                                                v___x_2317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                                return v___x_2317_;
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_e_2260_,
                                                                                );
                                                                                lean_inc(v_generation_2262_);
                                                                                v___x_2318_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2284_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                                if lean_obj_tag(
                                                                                    v___x_2318_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
                                                                                    lean_inc(
                                                                                        v_a_2319_,
                                                                                    );
                                                                                    lean_dec_ref_known(v___x_2318_, 1);
                                                                                    v___x_2320_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                                    if lean_obj_tag(
                                                                                        v___x_2320_,
                                                                                    ) == 0
                                                                                    {
                                                                                        v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
                                                                                        v_isSharedCheck_2330_ = (!lean_is_exclusive(v___x_2320_)) as u8;
                                                                                        if v_isSharedCheck_2330_ == 0 {
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2330_;
state = 1; continue;
} else {
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2330_;
state = 1; continue;
}
                                                                                    } else {
                                                                                        lean_dec(v_a_2319_);
                                                                                        v_a_2331_ = lean_ctor_get(v___x_2320_, 0);
                                                                                        v_isSharedCheck_2338_ = (!lean_is_exclusive(v___x_2320_)) as u8;
                                                                                        if v_isSharedCheck_2338_ == 0 {
v___x_2333_ = v___x_2320_;
v_isShared_2334_ = v_isSharedCheck_2338_;
state = 3; continue;
} else {
lean_inc(v_a_2331_);
lean_dec(v___x_2320_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
state = 3; continue;
}
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_arg_2280_,
                                                                                    );
                                                                                    lean_dec(v_generation_2262_);
                                                                                    v_a_2339_ = lean_ctor_get(v___x_2318_, 0);
                                                                                    v_isSharedCheck_2346_ = (!lean_is_exclusive(v___x_2318_)) as u8;
                                                                                    if v_isSharedCheck_2346_ == 0 {
v___x_2341_ = v___x_2318_;
v_isShared_2342_ = v_isSharedCheck_2346_;
state = 5; continue;
} else {
lean_inc(v_a_2339_);
lean_dec(v___x_2318_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
state = 5; continue;
}
                                                                                }
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_2290_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2284_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2280_,
                                                                            );
                                                                            lean_dec(
                                                                                v_generation_2262_,
                                                                            );
                                                                            lean_dec_ref(v_e_2260_);
                                                                            v_a_2347_ =
                                                                                lean_ctor_get(
                                                                                    v___x_2314_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_2354_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_2314_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_2354_
                                                                                == 0
                                                                            {
                                                                                v___x_2349_ =
                                                                                    v___x_2314_;
                                                                                v_isShared_2350_ = v_isSharedCheck_2354_;
                                                                                state = 7;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_2347_);
                                                                                lean_dec(
                                                                                    v___x_2314_,
                                                                                );
                                                                                v___x_2349_ =
                                                                                    lean_box(0);
                                                                                v_isShared_2350_ = v_isSharedCheck_2354_;
                                                                                state = 7;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v___x_2306_);
                                                                    v___x_2355_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                    if lean_obj_tag(v___x_2355_)
                                                                        == 0
                                                                    {
                                                                        v_a_2356_ = lean_ctor_get(
                                                                            v___x_2355_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_2356_);
                                                                        lean_dec_ref_known(
                                                                            v___x_2355_,
                                                                            1,
                                                                        );
                                                                        v___x_2357_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_2356_, v_arg_2290_);
                                                                        lean_dec_ref(v_arg_2290_);
                                                                        lean_dec(v_a_2356_);
                                                                        if v___x_2357_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_arg_2284_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_2280_,
                                                                            );
                                                                            v___x_2358_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                            return v___x_2358_;
                                                                        } else {
                                                                            lean_dec_ref(v_e_2260_);
                                                                            lean_inc(
                                                                                v_generation_2262_,
                                                                            );
                                                                            v___x_2359_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2284_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                            if lean_obj_tag(
                                                                                v___x_2359_,
                                                                            ) == 0
                                                                            {
                                                                                v_a_2360_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_2359_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc(v_a_2360_);
                                                                                lean_dec_ref_known(
                                                                                    v___x_2359_,
                                                                                    1,
                                                                                );
                                                                                v___x_2361_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                                if lean_obj_tag(
                                                                                    v___x_2361_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
                                                                                    v_isSharedCheck_2371_ = (!lean_is_exclusive(v___x_2361_)) as u8;
                                                                                    if v_isSharedCheck_2371_ == 0 {
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2371_;
state = 9; continue;
} else {
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2371_;
state = 9; continue;
}
                                                                                } else {
                                                                                    lean_dec(
                                                                                        v_a_2360_,
                                                                                    );
                                                                                    v_a_2372_ = lean_ctor_get(v___x_2361_, 0);
                                                                                    v_isSharedCheck_2379_ = (!lean_is_exclusive(v___x_2361_)) as u8;
                                                                                    if v_isSharedCheck_2379_ == 0 {
v___x_2374_ = v___x_2361_;
v_isShared_2375_ = v_isSharedCheck_2379_;
state = 11; continue;
} else {
lean_inc(v_a_2372_);
lean_dec(v___x_2361_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
state = 11; continue;
}
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_2280_,
                                                                                );
                                                                                lean_dec(v_generation_2262_);
                                                                                v_a_2380_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_2359_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_2387_ = (!lean_is_exclusive(v___x_2359_)) as u8;
                                                                                if v_isSharedCheck_2387_ == 0 {
v___x_2382_ = v___x_2359_;
v_isShared_2383_ = v_isSharedCheck_2387_;
state = 13; continue;
} else {
lean_inc(v_a_2380_);
lean_dec(v___x_2359_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
state = 13; continue;
}
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_2290_);
                                                                        lean_dec_ref(v_arg_2284_);
                                                                        lean_dec_ref(v_arg_2280_);
                                                                        lean_dec(
                                                                            v_generation_2262_,
                                                                        );
                                                                        lean_dec_ref(v_e_2260_);
                                                                        v_a_2388_ = lean_ctor_get(
                                                                            v___x_2355_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_2395_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_2355_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_2395_
                                                                            == 0
                                                                        {
                                                                            v___x_2390_ =
                                                                                v___x_2355_;
                                                                            v_isShared_2391_ = v_isSharedCheck_2395_;
                                                                            state = 15;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_2388_);
                                                                            lean_dec(v___x_2355_);
                                                                            v___x_2390_ =
                                                                                lean_box(0);
                                                                            v_isShared_2391_ = v_isSharedCheck_2395_;
                                                                            state = 15;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_2306_);
                                                                lean_inc(v_generation_2262_);
                                                                v___x_2396_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_processSMul(v_generation_2262_, v_arg_2290_, v_arg_2284_, v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                lean_dec_ref(v_arg_2290_);
                                                                if lean_obj_tag(v___x_2396_) == 0 {
                                                                    v_a_2397_ = lean_ctor_get(
                                                                        v___x_2396_,
                                                                        0,
                                                                    );
                                                                    lean_inc(v_a_2397_);
                                                                    if lean_obj_tag(v_a_2397_) == 1
                                                                    {
                                                                        lean_dec_ref_known(
                                                                            v_a_2397_, 1,
                                                                        );
                                                                        lean_dec(
                                                                            v_generation_2262_,
                                                                        );
                                                                        lean_dec_ref(v_e_2260_);
                                                                        return v___x_2396_;
                                                                    } else {
                                                                        lean_dec_ref_known(
                                                                            v___x_2396_,
                                                                            1,
                                                                        );
                                                                        lean_dec(v_a_2397_);
                                                                        v___x_2398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                                        return v___x_2398_;
                                                                    }
                                                                } else {
                                                                    lean_dec(v_generation_2262_);
                                                                    lean_dec_ref(v_e_2260_);
                                                                    return v___x_2396_;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_2291_);
                                                lean_dec_ref(v_arg_2290_);
                                                v___x_2399_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                if lean_obj_tag(v___x_2399_) == 0 {
                                                    v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
                                                    lean_inc(v_a_2400_);
                                                    lean_dec_ref_known(v___x_2399_, 1);
                                                    v___x_2401_ =
                                                        l_Lean_Meta_Grind_Arith_Linear_isNegInst(
                                                            v_a_2400_,
                                                            v_arg_2284_,
                                                        );
                                                    lean_dec_ref(v_arg_2284_);
                                                    lean_dec(v_a_2400_);
                                                    if v___x_2401_ == 0 {
                                                        lean_dec_ref(v_arg_2280_);
                                                        v___x_2402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                        return v___x_2402_;
                                                    } else {
                                                        lean_dec_ref(v_e_2260_);
                                                        v___x_2403_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_go(v_generation_2262_, v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                                        if lean_obj_tag(v___x_2403_) == 0 {
                                                            v_a_2404_ =
                                                                lean_ctor_get(v___x_2403_, 0);
                                                            v_isSharedCheck_2413_ =
                                                                (!lean_is_exclusive(v___x_2403_))
                                                                    as u8;
                                                            if v_isSharedCheck_2413_ == 0 {
                                                                v___x_2406_ = v___x_2403_;
                                                                v_isShared_2407_ =
                                                                    v_isSharedCheck_2413_;
                                                                state = 17;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2404_);
                                                                lean_dec(v___x_2403_);
                                                                v___x_2406_ = lean_box(0);
                                                                v_isShared_2407_ =
                                                                    v_isSharedCheck_2413_;
                                                                state = 17;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_2414_ =
                                                                lean_ctor_get(v___x_2403_, 0);
                                                            v_isSharedCheck_2421_ =
                                                                (!lean_is_exclusive(v___x_2403_))
                                                                    as u8;
                                                            if v_isSharedCheck_2421_ == 0 {
                                                                v___x_2416_ = v___x_2403_;
                                                                v_isShared_2417_ =
                                                                    v_isSharedCheck_2421_;
                                                                state = 19;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2414_);
                                                                lean_dec(v___x_2403_);
                                                                v___x_2416_ = lean_box(0);
                                                                v_isShared_2417_ =
                                                                    v_isSharedCheck_2421_;
                                                                state = 19;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_2284_);
                                                    lean_dec_ref(v_arg_2280_);
                                                    lean_dec(v_generation_2262_);
                                                    lean_dec_ref(v_e_2260_);
                                                    v_a_2422_ = lean_ctor_get(v___x_2399_, 0);
                                                    v_isSharedCheck_2429_ =
                                                        (!lean_is_exclusive(v___x_2399_)) as u8;
                                                    if v_isSharedCheck_2429_ == 0 {
                                                        v___x_2424_ = v___x_2399_;
                                                        v_isShared_2425_ = v_isSharedCheck_2429_;
                                                        state = 21;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2422_);
                                                        lean_dec(v___x_2399_);
                                                        v___x_2424_ = lean_box(0);
                                                        v_isShared_2425_ = v_isSharedCheck_2429_;
                                                        state = 21;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2291_);
                                            lean_dec_ref(v_arg_2290_);
                                            lean_dec_ref(v_arg_2284_);
                                            lean_dec_ref(v_arg_2280_);
                                            lean_inc_ref(v_e_2260_);
                                            v___x_2430_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_isOfNatZero(v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                                            if lean_obj_tag(v___x_2430_) == 0 {
                                                v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
                                                v_isSharedCheck_2441_ =
                                                    (!lean_is_exclusive(v___x_2430_)) as u8;
                                                if v_isSharedCheck_2441_ == 0 {
                                                    v___x_2433_ = v___x_2430_;
                                                    v_isShared_2434_ = v_isSharedCheck_2441_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2431_);
                                                    lean_dec(v___x_2430_);
                                                    v___x_2433_ = lean_box(0);
                                                    v_isShared_2434_ = v_isSharedCheck_2441_;
                                                    state = 23;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_generation_2262_);
                                                lean_dec_ref(v_e_2260_);
                                                v_a_2442_ = lean_ctor_get(v___x_2430_, 0);
                                                v_isSharedCheck_2449_ =
                                                    (!lean_is_exclusive(v___x_2430_)) as u8;
                                                if v_isSharedCheck_2449_ == 0 {
                                                    v___x_2444_ = v___x_2430_;
                                                    v_isShared_2445_ = v_isSharedCheck_2449_;
                                                    state = 25;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2442_);
                                                    lean_dec(v___x_2430_);
                                                    v___x_2444_ = lean_box(0);
                                                    v_isShared_2445_ = v_isSharedCheck_2449_;
                                                    state = 25;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_2291_);
                                        lean_dec_ref(v_arg_2290_);
                                        lean_dec_ref(v_arg_2284_);
                                        v___x_2450_ =
                                            l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                                v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_,
                                                v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_,
                                                v_a_2271_, v_a_2272_, v_a_2273_,
                                            );
                                        if lean_obj_tag(v___x_2450_) == 0 {
                                            v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
                                            lean_inc(v_a_2451_);
                                            lean_dec_ref_known(v___x_2450_, 1);
                                            v_orderedRingInst_x3f_2465_ =
                                                lean_ctor_get(v_a_2451_, 14);
                                            lean_inc(v_orderedRingInst_x3f_2465_);
                                            lean_dec(v_a_2451_);
                                            if lean_obj_tag(v_orderedRingInst_x3f_2465_) == 0 {
                                                v___y_2453_ = v___x_2287_;
                                                state = 27;
                                                continue;
                                            } else {
                                                lean_dec_ref_known(v_orderedRingInst_x3f_2465_, 1);
                                                v___y_2453_ = v___x_2293_;
                                                state = 27;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_2280_);
                                            lean_dec(v_generation_2262_);
                                            lean_dec_ref(v_e_2260_);
                                            v_a_2466_ = lean_ctor_get(v___x_2450_, 0);
                                            v_isSharedCheck_2473_ =
                                                (!lean_is_exclusive(v___x_2450_)) as u8;
                                            if v_isSharedCheck_2473_ == 0 {
                                                v___x_2468_ = v___x_2450_;
                                                v_isShared_2469_ = v_isSharedCheck_2473_;
                                                state = 30;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2466_);
                                                lean_dec(v___x_2450_);
                                                v___x_2468_ = lean_box(0);
                                                v_isShared_2469_ = v_isSharedCheck_2473_;
                                                state = 30;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_2285_);
                                lean_dec_ref(v_arg_2284_);
                                v___x_2474_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                                    v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_,
                                    v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_,
                                    v_a_2273_,
                                );
                                if lean_obj_tag(v___x_2474_) == 0 {
                                    v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
                                    v_isSharedCheck_2485_ = (!lean_is_exclusive(v___x_2474_)) as u8;
                                    if v_isSharedCheck_2485_ == 0 {
                                        v___x_2477_ = v___x_2474_;
                                        v_isShared_2478_ = v_isSharedCheck_2485_;
                                        state = 32;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2475_);
                                        lean_dec(v___x_2474_);
                                        v___x_2477_ = lean_box(0);
                                        v_isShared_2478_ = v_isSharedCheck_2485_;
                                        state = 32;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_2280_);
                                    lean_dec(v_generation_2262_);
                                    lean_dec_ref(v_e_2260_);
                                    v_a_2486_ = lean_ctor_get(v___x_2474_, 0);
                                    v_isSharedCheck_2493_ = (!lean_is_exclusive(v___x_2474_)) as u8;
                                    if v_isSharedCheck_2493_ == 0 {
                                        v___x_2488_ = v___x_2474_;
                                        v_isShared_2489_ = v_isSharedCheck_2493_;
                                        state = 34;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2486_);
                                        lean_dec(v___x_2474_);
                                        v___x_2488_ = lean_box(0);
                                        v_isShared_2489_ = v_isSharedCheck_2493_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_generation_2262_);
                    lean_dec_ref(v_e_2260_);
                    v_a_2494_ = lean_ctor_get(v___x_2275_, 0);
                    v_isSharedCheck_2501_ = (!lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2501_ == 0 {
                        v___x_2496_ = v___x_2275_;
                        v_isShared_2497_ = v_isSharedCheck_2501_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_2494_);
                        lean_dec(v___x_2275_);
                        v___x_2496_ = lean_box(0);
                        v_isShared_2497_ = v_isSharedCheck_2501_;
                        state = 36;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2325_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2325_, 0, v_a_2319_);
                lean_ctor_set(v___x_2325_, 1, v_a_2321_);
                v___x_2326_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2326_, 0, v___x_2325_);
                if v_isShared_2324_ == 0 {
                    lean_ctor_set(v___x_2323_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
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
                    v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
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
                    v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
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
                    v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
                    v___x_2352_ = v_reuseFailAlloc_2353_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2352_;
            }
            9 => {
                v___x_2366_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_2366_, 0, v_a_2360_);
                lean_ctor_set(v___x_2366_, 1, v_a_2362_);
                v___x_2367_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2367_, 0, v___x_2366_);
                if v_isShared_2365_ == 0 {
                    lean_ctor_set(v___x_2364_, 0, v___x_2367_);
                    v___x_2369_ = v___x_2364_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
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
                    v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
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
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
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
                    v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
                    v___x_2393_ = v_reuseFailAlloc_2394_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2393_;
            }
            17 => {
                v___x_2408_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_2408_, 0, v_a_2404_);
                v___x_2409_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2409_, 0, v___x_2408_);
                if v_isShared_2407_ == 0 {
                    lean_ctor_set(v___x_2406_, 0, v___x_2409_);
                    v___x_2411_ = v___x_2406_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
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
                    v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
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
                    v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
                    v___x_2427_ = v_reuseFailAlloc_2428_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2427_;
            }
            23 => {
                v___x_2435_ = (lean_unbox(v_a_2431_) as u8);
                lean_dec(v_a_2431_);
                if v___x_2435_ == 0 {
                    lean_del_object(v___x_2433_);
                    v___x_2436_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                    return v___x_2436_;
                } else {
                    lean_dec(v_generation_2262_);
                    lean_dec_ref(v_e_2260_);
                    v___x_2437_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0;
                    if v_isShared_2434_ == 0 {
                        lean_ctor_set(v___x_2433_, 0, v___x_2437_);
                        v___x_2439_ = v___x_2433_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
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
                    v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
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
                    lean_dec_ref(v_arg_2280_);
                    v___x_2454_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                    return v___x_2454_;
                } else {
                    v___x_2455_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_assertNatCastNonneg(v_arg_2280_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                    if lean_obj_tag(v___x_2455_) == 0 {
                        lean_dec_ref_known(v___x_2455_, 1);
                        v___x_2456_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_toTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                        return v___x_2456_;
                    } else {
                        lean_dec(v_generation_2262_);
                        lean_dec_ref(v_e_2260_);
                        v_a_2457_ = lean_ctor_get(v___x_2455_, 0);
                        v_isSharedCheck_2464_ = (!lean_is_exclusive(v___x_2455_)) as u8;
                        if v_isSharedCheck_2464_ == 0 {
                            v___x_2459_ = v___x_2455_;
                            v_isShared_2460_ = v_isSharedCheck_2464_;
                            state = 28;
                            continue;
                        } else {
                            lean_inc(v_a_2457_);
                            lean_dec(v___x_2455_);
                            v___x_2459_ = lean_box(0);
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
                    v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
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
                    v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
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
                lean_dec_ref(v_arg_2280_);
                lean_dec(v_a_2475_);
                if v___x_2479_ == 0 {
                    lean_del_object(v___x_2477_);
                    v___x_2480_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Reify_0__Lean_Meta_Grind_Arith_Linear_reify_x3f_asTopVar(v_skipVar_2261_, v_generation_2262_, v_e_2260_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
                    return v___x_2480_;
                } else {
                    lean_dec(v_generation_2262_);
                    lean_dec_ref(v_e_2260_);
                    v___x_2481_ = l_Lean_Meta_Grind_Arith_Linear_reify_x3f___closed__0;
                    if v_isShared_2478_ == 0 {
                        lean_ctor_set(v___x_2477_, 0, v___x_2481_);
                        v___x_2483_ = v___x_2477_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
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
                    v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
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
                    v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
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
    mut v_e_2502_: *mut LeanObject,
    mut v_skipVar_2503_: *mut LeanObject,
    mut v_generation_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
    mut v_a_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
    mut v_a_2515_: *mut LeanObject,
    mut v_a_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipVar_boxed_2517_: u8 = 0;
    let mut v_res_2518_: *mut LeanObject = core::ptr::null_mut();
    v_skipVar_boxed_2517_ = (lean_unbox(v_skipVar_2503_) as u8);
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
    lean_dec(v_a_2515_);
    lean_dec_ref(v_a_2514_);
    lean_dec(v_a_2513_);
    lean_dec_ref(v_a_2512_);
    lean_dec(v_a_2511_);
    lean_dec_ref(v_a_2510_);
    lean_dec(v_a_2509_);
    lean_dec_ref(v_a_2508_);
    lean_dec(v_a_2507_);
    lean_dec(v_a_2506_);
    lean_dec(v_a_2505_);
    return v_res_2518_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
}
