// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.EvalNum
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.IntInstTesters Lean.Meta.NatInstTesters
use crate::ffi::{
    lean_int_add, lean_int_ediv, lean_int_emod, lean_int_mul, lean_int_neg, lean_int_sub,
    lean_nat_abs, lean_nat_add, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_mul,
    lean_nat_pow, lean_nat_sub, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Int::Basic::{l_Int_pow, l_Int_toNat};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::IntInstTesters::{
    initialize_Lean_Meta_IntInstTesters, l_Lean_Meta_Structural_isInstHAddInt___redArg,
    l_Lean_Meta_Structural_isInstHDivInt___redArg, l_Lean_Meta_Structural_isInstHModInt___redArg,
    l_Lean_Meta_Structural_isInstHMulInt___redArg, l_Lean_Meta_Structural_isInstHPowInt___redArg,
    l_Lean_Meta_Structural_isInstHSubInt___redArg, l_Lean_Meta_Structural_isInstNegInt___redArg,
    runtime_initialize_Lean_Meta_IntInstTesters,
};
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_Structural_isInstHAddNat___redArg,
    l_Lean_Meta_Structural_isInstHDivNat___redArg, l_Lean_Meta_Structural_isInstHModNat___redArg,
    l_Lean_Meta_Structural_isInstHMulNat___redArg, l_Lean_Meta_Structural_isInstHPowNat___redArg,
    l_Lean_Meta_Structural_isInstHSubNat___redArg, runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_getConfig___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
pub static l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [101, 120, 112, 111, 110, 101, 110, 116, 32, 0],
};
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3_value:
    leanh::LeanStringObject<48> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        32, 101, 120, 99, 101, 101, 100, 115, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 32,
        102, 111, 114, 32, 101, 120, 112, 111, 110, 101, 110, 116, 105, 97, 116, 105, 111, 110, 32,
        96, 40, 101, 120, 112, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [41, 96, 0],
};
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value) as *mut leanh::LeanObject,13428217069302927667 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 65, 98, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value) as *mut leanh::LeanObject,7009148538150066493 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value) as *mut leanh::LeanObject,12132318982517471999 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value) as *mut leanh::LeanObject,7009148538150066493 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value) as *mut leanh::LeanObject,13897037934312376979 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 117, 99, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value) as *mut leanh::LeanObject,16112798088292836701 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value) as *mut leanh::LeanObject,12847922472053947547 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value) as *mut leanh::LeanObject,10422657989269798688 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value) as *mut leanh::LeanObject,13744984671752750173 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value) as *mut leanh::LeanObject,9682224670061807480 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value) as *mut leanh::LeanObject,11858238400308895562 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value) as *mut leanh::LeanObject,6100819061652633370 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value) as *mut leanh::LeanObject,16856108565602861689 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value) as *mut leanh::LeanObject,4187025665268973031 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value) as *mut leanh::LeanObject,2929883540436775422 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value) as *mut leanh::LeanObject,1611444129324655608 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value) as *mut leanh::LeanObject,10680564408669940870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 115, 116, 78, 97, 116, 67, 97, 115, 116, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value) as *mut leanh::LeanObject,14240220390202531956 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value) as *mut leanh::LeanObject,8075995802451307795 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value) as *mut leanh::LeanObject,5779414593499529281 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value) as *mut leanh::LeanObject,7063772860359172143 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value) as *mut leanh::LeanObject,17185717442815859305 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1;
    v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
    return v___x_1151_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3;
    v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
    return v___x_1154_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5;
    v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
    return v___x_1157_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_checkExp___redArg(
    mut v_k_1158_: *mut leanh::LeanObject,
    mut v_a_1159_: *mut leanh::LeanObject,
    mut v_a_1160_: *mut leanh::LeanObject,
    mut v_a_1161_: *mut leanh::LeanObject,
    mut v_a_1162_: *mut leanh::LeanObject,
    mut v_a_1163_: *mut leanh::LeanObject,
    mut v_a_1164_: *mut leanh::LeanObject,
    mut v_a_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v_exp_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v_exp_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1204_: u8 = 0;
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1208_: u8 = 0;
    let mut v_a_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1216_: u8 = 0;
    let mut v_a_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1224_: u8 = 0;
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_a_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1170_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1159_);
                if leanh::lean_obj_tag(v___x_1170_) == 0 {
                    v_a_1171_ = leanh::lean_ctor_get(v___x_1170_, 0);
                    v_isSharedCheck_1225_ = (!leanh::lean_is_exclusive(v___x_1170_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1173_ = v___x_1170_;
                        v_isShared_1174_ = v_isSharedCheck_1225_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1171_);
                        leanh::lean_dec(v___x_1170_);
                        v___x_1173_ = leanh::lean_box(0);
                        v_isShared_1174_ = v_isSharedCheck_1225_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_1158_);
                    v_a_1226_ = leanh::lean_ctor_get(v___x_1170_, 0);
                    v_isSharedCheck_1233_ = (!leanh::lean_is_exclusive(v___x_1170_)) as u8;
                    if v_isSharedCheck_1233_ == 0 {
                        v___x_1228_ = v___x_1170_;
                        v_isShared_1229_ = v_isSharedCheck_1233_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1226_);
                        leanh::lean_dec(v___x_1170_);
                        v___x_1228_ = leanh::lean_box(0);
                        v_isShared_1229_ = v_isSharedCheck_1233_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1168_ = leanh::lean_box(0);
                v___x_1169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1169_, 0, v___x_1168_);
                return v___x_1169_;
            }
            2 => {
                v_exp_1175_ = leanh::lean_ctor_get(v_a_1171_, 9);
                leanh::lean_inc(v_exp_1175_);
                leanh::lean_dec(v_a_1171_);
                v___x_1176_ = lean_nat_dec_lt(v_exp_1175_, v_k_1158_);
                leanh::lean_dec(v_exp_1175_);
                if v___x_1176_ == 0 {
                    leanh::lean_dec(v_k_1158_);
                    v___x_1177_ = l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0;
                    if v_isShared_1174_ == 0 {
                        leanh::lean_ctor_set(v___x_1173_, 0, v___x_1177_);
                        v___x_1179_ = v___x_1173_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
                        v___x_1179_ = v_reuseFailAlloc_1180_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1173_);
                    v___x_1181_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1159_);
                    if leanh::lean_obj_tag(v___x_1181_) == 0 {
                        v_a_1182_ = leanh::lean_ctor_get(v___x_1181_, 0);
                        leanh::lean_inc(v_a_1182_);
                        leanh::lean_dec_ref_known(v___x_1181_, 1);
                        v___x_1183_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1160_);
                        if leanh::lean_obj_tag(v___x_1183_) == 0 {
                            v_a_1184_ = leanh::lean_ctor_get(v___x_1183_, 0);
                            leanh::lean_inc(v_a_1184_);
                            leanh::lean_dec_ref_known(v___x_1183_, 1);
                            v___x_1185_ = (leanh::lean_unbox(v_a_1184_) as u8);
                            leanh::lean_dec(v_a_1184_);
                            if v___x_1185_ == 0 {
                                leanh::lean_dec(v_a_1182_);
                                leanh::lean_dec(v_k_1158_);
                                state = 1;
                                continue;
                            } else {
                                v_exp_1186_ = leanh::lean_ctor_get(v_a_1182_, 9);
                                leanh::lean_inc(v_exp_1186_);
                                leanh::lean_dec(v_a_1182_);
                                v___x_1187_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2_once
                                    ),
                                    _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2,
                                );
                                v___x_1188_ = l_Nat_reprFast(v_k_1158_);
                                v___x_1189_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1189_, 0, v___x_1188_);
                                v___x_1190_ = l_Lean_MessageData_ofFormat(v___x_1189_);
                                v___x_1191_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1191_, 0, v___x_1187_);
                                leanh::lean_ctor_set(v___x_1191_, 1, v___x_1190_);
                                v___x_1192_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4_once
                                    ),
                                    _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4,
                                );
                                v___x_1193_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1193_, 0, v___x_1191_);
                                leanh::lean_ctor_set(v___x_1193_, 1, v___x_1192_);
                                v___x_1194_ = l_Nat_reprFast(v_exp_1186_);
                                v___x_1195_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1195_, 0, v___x_1194_);
                                v___x_1196_ = l_Lean_MessageData_ofFormat(v___x_1195_);
                                v___x_1197_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1197_, 0, v___x_1193_);
                                leanh::lean_ctor_set(v___x_1197_, 1, v___x_1196_);
                                v___x_1198_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6_once
                                    ),
                                    _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6,
                                );
                                v___x_1199_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1199_, 0, v___x_1197_);
                                leanh::lean_ctor_set(v___x_1199_, 1, v___x_1198_);
                                v___x_1200_ = l_Lean_Meta_Sym_reportIssue(
                                    v___x_1199_,
                                    v_a_1160_,
                                    v_a_1161_,
                                    v_a_1162_,
                                    v_a_1163_,
                                    v_a_1164_,
                                    v_a_1165_,
                                );
                                if leanh::lean_obj_tag(v___x_1200_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1200_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_1201_ = leanh::lean_ctor_get(v___x_1200_, 0);
                                    v_isSharedCheck_1208_ =
                                        (!leanh::lean_is_exclusive(v___x_1200_)) as u8;
                                    if v_isSharedCheck_1208_ == 0 {
                                        v___x_1203_ = v___x_1200_;
                                        v_isShared_1204_ = v_isSharedCheck_1208_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1201_);
                                        leanh::lean_dec(v___x_1200_);
                                        v___x_1203_ = leanh::lean_box(0);
                                        v_isShared_1204_ = v_isSharedCheck_1208_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1182_);
                            leanh::lean_dec(v_k_1158_);
                            v_a_1209_ = leanh::lean_ctor_get(v___x_1183_, 0);
                            v_isSharedCheck_1216_ =
                                (!leanh::lean_is_exclusive(v___x_1183_)) as u8;
                            if v_isSharedCheck_1216_ == 0 {
                                v___x_1211_ = v___x_1183_;
                                v_isShared_1212_ = v_isSharedCheck_1216_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1209_);
                                leanh::lean_dec(v___x_1183_);
                                v___x_1211_ = leanh::lean_box(0);
                                v_isShared_1212_ = v_isSharedCheck_1216_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_k_1158_);
                        v_a_1217_ = leanh::lean_ctor_get(v___x_1181_, 0);
                        v_isSharedCheck_1224_ =
                            (!leanh::lean_is_exclusive(v___x_1181_)) as u8;
                        if v_isSharedCheck_1224_ == 0 {
                            v___x_1219_ = v___x_1181_;
                            v_isShared_1220_ = v_isSharedCheck_1224_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1217_);
                            leanh::lean_dec(v___x_1181_);
                            v___x_1219_ = leanh::lean_box(0);
                            v_isShared_1220_ = v_isSharedCheck_1224_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_1179_;
            }
            4 => {
                if v_isShared_1204_ == 0 {
                    v___x_1206_ = v___x_1203_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
                    v___x_1206_ = v_reuseFailAlloc_1207_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1206_;
            }
            6 => {
                if v_isShared_1212_ == 0 {
                    v___x_1214_ = v___x_1211_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1215_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
                    v___x_1214_ = v_reuseFailAlloc_1215_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1214_;
            }
            8 => {
                if v_isShared_1220_ == 0 {
                    v___x_1222_ = v___x_1219_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1223_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
                    v___x_1222_ = v_reuseFailAlloc_1223_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1222_;
            }
            10 => {
                if v_isShared_1229_ == 0 {
                    v___x_1231_ = v___x_1228_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
                    v___x_1231_ = v_reuseFailAlloc_1232_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_checkExp___redArg___boxed(
    mut v_k_1234_: *mut leanh::LeanObject,
    mut v_a_1235_: *mut leanh::LeanObject,
    mut v_a_1236_: *mut leanh::LeanObject,
    mut v_a_1237_: *mut leanh::LeanObject,
    mut v_a_1238_: *mut leanh::LeanObject,
    mut v_a_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
    mut v_a_1241_: *mut leanh::LeanObject,
    mut v_a_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(
        v_k_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_,
    );
    leanh::lean_dec(v_a_1241_);
    leanh::lean_dec_ref(v_a_1240_);
    leanh::lean_dec(v_a_1239_);
    leanh::lean_dec_ref(v_a_1238_);
    leanh::lean_dec(v_a_1237_);
    leanh::lean_dec_ref(v_a_1236_);
    leanh::lean_dec_ref(v_a_1235_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_checkExp(
    mut v_k_1244_: *mut leanh::LeanObject,
    mut v_a_1245_: *mut leanh::LeanObject,
    mut v_a_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
    mut v_a_1248_: *mut leanh::LeanObject,
    mut v_a_1249_: *mut leanh::LeanObject,
    mut v_a_1250_: *mut leanh::LeanObject,
    mut v_a_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
    mut v_a_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(
        v_k_1244_, v_a_1246_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_,
    );
    return v___x_1255_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_checkExp___boxed(
    mut v_k_1256_: *mut leanh::LeanObject,
    mut v_a_1257_: *mut leanh::LeanObject,
    mut v_a_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v_a_1260_: *mut leanh::LeanObject,
    mut v_a_1261_: *mut leanh::LeanObject,
    mut v_a_1262_: *mut leanh::LeanObject,
    mut v_a_1263_: *mut leanh::LeanObject,
    mut v_a_1264_: *mut leanh::LeanObject,
    mut v_a_1265_: *mut leanh::LeanObject,
    mut v_a_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_Meta_Grind_Arith_checkExp(
        v_k_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_,
        v_a_1264_, v_a_1265_,
    );
    leanh::lean_dec(v_a_1265_);
    leanh::lean_dec_ref(v_a_1264_);
    leanh::lean_dec(v_a_1263_);
    leanh::lean_dec_ref(v_a_1262_);
    leanh::lean_dec(v_a_1261_);
    leanh::lean_dec_ref(v_a_1260_);
    leanh::lean_dec(v_a_1259_);
    leanh::lean_dec_ref(v_a_1258_);
    leanh::lean_dec(v_a_1257_);
    return v_res_1267_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(
    mut v_e_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
    mut v_a_1344_: *mut leanh::LeanObject,
    mut v_a_1345_: *mut leanh::LeanObject,
    mut v_a_1346_: *mut leanh::LeanObject,
    mut v_a_1347_: *mut leanh::LeanObject,
    mut v_a_1348_: *mut leanh::LeanObject,
    mut v_a_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1379_: u8 = 0;
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut v_a_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1404_: u8 = 0;
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut v_a_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    let mut v_arg_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v_arg_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: u8 = 0;
    let mut v_arg_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v_val_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_unused_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_a_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1500_: u8 = 0;
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1518_: u8 = 0;
    let mut v_val_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1530_: u8 = 0;
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_unused_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_a_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1537_: u8 = 0;
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1547_: u8 = 0;
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v_val_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_unused_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v_a_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v_val_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1604_: u8 = 0;
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_isSharedCheck_1613_: u8 = 0;
    let mut v_unused_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v_a_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v_val_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v_isSharedCheck_1654_: u8 = 0;
    let mut v_unused_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1656_: u8 = 0;
    let mut v_a_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1660_: u8 = 0;
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1664_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1669_: u8 = 0;
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut v_unused_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1709_: u8 = 0;
    let mut v_a_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_a_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1722_: u8 = 0;
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1726_: u8 = 0;
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_a_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1741_: u8 = 0;
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v_val_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1762_: u8 = 0;
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v_unused_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut v_a_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v_unused_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut v_a_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1340_);
                v___x_1414_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1340_, v_a_1347_);
                if leanh::lean_obj_tag(v___x_1414_) == 0 {
                    v_a_1415_ = leanh::lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1785_ = (!leanh::lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1785_ == 0 {
                        v___x_1417_ = v___x_1414_;
                        v_isShared_1418_ = v_isSharedCheck_1785_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1415_);
                        leanh::lean_dec(v___x_1414_);
                        v___x_1417_ = leanh::lean_box(0);
                        v_isShared_1418_ = v_isSharedCheck_1785_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1340_);
                    v_a_1786_ = leanh::lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1793_ = (!leanh::lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1793_ == 0 {
                        v___x_1788_ = v___x_1414_;
                        v_isShared_1789_ = v_isSharedCheck_1793_;
                        state = 81;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1786_);
                        leanh::lean_dec(v___x_1414_);
                        v___x_1788_ = leanh::lean_box(0);
                        v_isShared_1789_ = v_isSharedCheck_1793_;
                        state = 81;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1363_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_i_1352_, v___y_1360_);
                if leanh::lean_obj_tag(v___x_1363_) == 0 {
                    v_a_1364_ = leanh::lean_ctor_get(v___x_1363_, 0);
                    v_isSharedCheck_1405_ = (!leanh::lean_is_exclusive(v___x_1363_)) as u8;
                    if v_isSharedCheck_1405_ == 0 {
                        v___x_1366_ = v___x_1363_;
                        v_isShared_1367_ = v_isSharedCheck_1405_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1364_);
                        leanh::lean_dec(v___x_1363_);
                        v___x_1366_ = leanh::lean_box(0);
                        v_isShared_1367_ = v_isSharedCheck_1405_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1353_);
                    v_a_1406_ = leanh::lean_ctor_get(v___x_1363_, 0);
                    v_isSharedCheck_1413_ = (!leanh::lean_is_exclusive(v___x_1363_)) as u8;
                    if v_isSharedCheck_1413_ == 0 {
                        v___x_1408_ = v___x_1363_;
                        v_isShared_1409_ = v_isSharedCheck_1413_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1406_);
                        leanh::lean_dec(v___x_1363_);
                        v___x_1408_ = leanh::lean_box(0);
                        v_isShared_1409_ = v_isSharedCheck_1413_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1368_ = l_Lean_Expr_cleanupAnnotations(v_a_1364_);
                v___x_1369_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1;
                v___x_1370_ = l_Lean_Expr_isConstOf(v___x_1368_, v___x_1369_);
                leanh::lean_dec_ref(v___x_1368_);
                if v___x_1370_ == 0 {
                    leanh::lean_dec_ref(v_a_1353_);
                    v___x_1371_ = leanh::lean_box(0);
                    if v_isShared_1367_ == 0 {
                        leanh::lean_ctor_set(v___x_1366_, 0, v___x_1371_);
                        v___x_1373_ = v___x_1366_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1374_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
                        v___x_1373_ = v_reuseFailAlloc_1374_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1366_);
                    v___x_1375_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_a_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
                    if leanh::lean_obj_tag(v___x_1375_) == 0 {
                        v_a_1376_ = leanh::lean_ctor_get(v___x_1375_, 0);
                        v_isSharedCheck_1396_ =
                            (!leanh::lean_is_exclusive(v___x_1375_)) as u8;
                        if v_isSharedCheck_1396_ == 0 {
                            v___x_1378_ = v___x_1375_;
                            v_isShared_1379_ = v_isSharedCheck_1396_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1376_);
                            leanh::lean_dec(v___x_1375_);
                            v___x_1378_ = leanh::lean_box(0);
                            v_isShared_1379_ = v_isSharedCheck_1396_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_1397_ = leanh::lean_ctor_get(v___x_1375_, 0);
                        v_isSharedCheck_1404_ =
                            (!leanh::lean_is_exclusive(v___x_1375_)) as u8;
                        if v_isSharedCheck_1404_ == 0 {
                            v___x_1399_ = v___x_1375_;
                            v_isShared_1400_ = v_isSharedCheck_1404_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1397_);
                            leanh::lean_dec(v___x_1375_);
                            v___x_1399_ = leanh::lean_box(0);
                            v_isShared_1400_ = v_isSharedCheck_1404_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_1373_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_1376_) == 0 {
                    v___x_1380_ = leanh::lean_box(0);
                    if v_isShared_1379_ == 0 {
                        leanh::lean_ctor_set(v___x_1378_, 0, v___x_1380_);
                        v___x_1382_ = v___x_1378_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1383_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
                        v___x_1382_ = v_reuseFailAlloc_1383_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_1384_ = leanh::lean_ctor_get(v_a_1376_, 0);
                    v_isSharedCheck_1395_ = (!leanh::lean_is_exclusive(v_a_1376_)) as u8;
                    if v_isSharedCheck_1395_ == 0 {
                        v___x_1386_ = v_a_1376_;
                        v_isShared_1387_ = v_isSharedCheck_1395_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1384_);
                        leanh::lean_dec(v_a_1376_);
                        v___x_1386_ = leanh::lean_box(0);
                        v_isShared_1387_ = v_isSharedCheck_1395_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1382_;
            }
            6 => {
                v___x_1388_ = lean_nat_to_int(v_val_1384_);
                if v_isShared_1387_ == 0 {
                    leanh::lean_ctor_set(v___x_1386_, 0, v___x_1388_);
                    v___x_1390_ = v___x_1386_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1388_);
                    v___x_1390_ = v_reuseFailAlloc_1394_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1379_ == 0 {
                    leanh::lean_ctor_set(v___x_1378_, 0, v___x_1390_);
                    v___x_1392_ = v___x_1378_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
                    v___x_1392_ = v_reuseFailAlloc_1393_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1392_;
            }
            9 => {
                if v_isShared_1400_ == 0 {
                    v___x_1402_ = v___x_1399_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
                    v___x_1402_ = v_reuseFailAlloc_1403_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1402_;
            }
            11 => {
                if v_isShared_1409_ == 0 {
                    v___x_1411_ = v___x_1408_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
                    v___x_1411_ = v_reuseFailAlloc_1412_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1411_;
            }
            13 => {
                v___x_1424_ = l_Lean_Expr_cleanupAnnotations(v_a_1415_);
                v___x_1425_ = l_Lean_Expr_isApp(v___x_1424_);
                if v___x_1425_ == 0 {
                    leanh::lean_dec_ref(v___x_1424_);
                    leanh::lean_dec_ref(v_e_1340_);
                    state = 14;
                    continue;
                } else {
                    v_arg_1426_ = leanh::lean_ctor_get(v___x_1424_, 1);
                    leanh::lean_inc_ref(v_arg_1426_);
                    v___x_1427_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1424_);
                    v___x_1428_ = l_Lean_Expr_isApp(v___x_1427_);
                    if v___x_1428_ == 0 {
                        leanh::lean_dec_ref(v___x_1427_);
                        leanh::lean_dec_ref(v_arg_1426_);
                        leanh::lean_dec_ref(v_e_1340_);
                        state = 14;
                        continue;
                    } else {
                        v_arg_1429_ = leanh::lean_ctor_get(v___x_1427_, 1);
                        leanh::lean_inc_ref(v_arg_1429_);
                        v___x_1430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1427_);
                        v___x_1431_ = l_Lean_Expr_isApp(v___x_1430_);
                        if v___x_1431_ == 0 {
                            leanh::lean_dec_ref(v___x_1430_);
                            leanh::lean_dec_ref(v_arg_1429_);
                            leanh::lean_dec_ref(v_arg_1426_);
                            leanh::lean_dec_ref(v_e_1340_);
                            state = 14;
                            continue;
                        } else {
                            v_arg_1432_ = leanh::lean_ctor_get(v___x_1430_, 1);
                            leanh::lean_inc_ref(v_arg_1432_);
                            v___x_1433_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1430_);
                            v___x_1434_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3;
                            v___x_1435_ = l_Lean_Expr_isConstOf(v___x_1433_, v___x_1434_);
                            if v___x_1435_ == 0 {
                                v___x_1436_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6;
                                v___x_1437_ = l_Lean_Expr_isConstOf(v___x_1433_, v___x_1436_);
                                if v___x_1437_ == 0 {
                                    v___x_1438_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12;
                                    v___x_1439_ = l_Lean_Expr_isConstOf(v___x_1433_, v___x_1438_);
                                    if v___x_1439_ == 0 {
                                        leanh::lean_dec_ref(v_e_1340_);
                                        v___x_1440_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9;
                                        v___x_1441_ =
                                            l_Lean_Expr_isConstOf(v___x_1433_, v___x_1440_);
                                        if v___x_1441_ == 0 {
                                            v___x_1442_ = l_Lean_Expr_isApp(v___x_1433_);
                                            if v___x_1442_ == 0 {
                                                leanh::lean_dec_ref(v___x_1433_);
                                                leanh::lean_dec_ref(v_arg_1432_);
                                                leanh::lean_dec_ref(v_arg_1429_);
                                                leanh::lean_dec_ref(v_arg_1426_);
                                                state = 14;
                                                continue;
                                            } else {
                                                v___x_1443_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_1433_);
                                                v___x_1444_ = l_Lean_Expr_isApp(v___x_1443_);
                                                if v___x_1444_ == 0 {
                                                    leanh::lean_dec_ref(v___x_1443_);
                                                    leanh::lean_dec_ref(v_arg_1432_);
                                                    leanh::lean_dec_ref(v_arg_1429_);
                                                    leanh::lean_dec_ref(v_arg_1426_);
                                                    state = 14;
                                                    continue;
                                                } else {
                                                    v___x_1445_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1443_,
                                                    );
                                                    v___x_1446_ = l_Lean_Expr_isApp(v___x_1445_);
                                                    if v___x_1446_ == 0 {
                                                        leanh::lean_dec_ref(v___x_1445_);
                                                        leanh::lean_dec_ref(v_arg_1432_);
                                                        leanh::lean_dec_ref(v_arg_1429_);
                                                        leanh::lean_dec_ref(v_arg_1426_);
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        v___x_1447_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_1445_,
                                                            );
                                                        v___x_1448_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15;
                                                        v___x_1449_ = l_Lean_Expr_isConstOf(
                                                            v___x_1447_,
                                                            v___x_1448_,
                                                        );
                                                        if v___x_1449_ == 0 {
                                                            v___x_1450_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18;
                                                            v___x_1451_ = l_Lean_Expr_isConstOf(
                                                                v___x_1447_,
                                                                v___x_1450_,
                                                            );
                                                            if v___x_1451_ == 0 {
                                                                v___x_1452_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21;
                                                                v___x_1453_ = l_Lean_Expr_isConstOf(
                                                                    v___x_1447_,
                                                                    v___x_1452_,
                                                                );
                                                                if v___x_1453_ == 0 {
                                                                    v___x_1454_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27;
                                                                    v___x_1455_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_1447_,
                                                                            v___x_1454_,
                                                                        );
                                                                    if v___x_1455_ == 0 {
                                                                        v___x_1456_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24;
                                                                        v___x_1457_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_1447_,
                                                                                v___x_1456_,
                                                                            );
                                                                        if v___x_1457_ == 0 {
                                                                            v___x_1458_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30;
                                                                            v___x_1459_ = l_Lean_Expr_isConstOf(v___x_1447_, v___x_1458_);
                                                                            leanh::lean_dec_ref(v___x_1447_);
                                                                            if v___x_1459_ == 0 {
                                                                                leanh::lean_dec_ref(v_arg_1432_);
                                                                                leanh::lean_dec_ref(v_arg_1429_);
                                                                                leanh::lean_dec_ref(v_arg_1426_);
                                                                                state = 14;
                                                                                continue;
                                                                            } else {
                                                                                leanh::lean_del_object(v___x_1417_);
                                                                                v___x_1460_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1432_, v_a_1347_);
                                                                                if leanh::lean_obj_tag(v___x_1460_) == 0 {
v_a_1461_ = leanh::lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1492_ = (!leanh::lean_is_exclusive(v___x_1460_)) as u8;
if v_isSharedCheck_1492_ == 0 {
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1492_;
state = 16; continue;
} else {
leanh::lean_inc(v_a_1461_);
leanh::lean_dec(v___x_1460_);
v___x_1463_ = leanh::lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1492_;
state = 16; continue;
}
} else {
leanh::lean_dec_ref(v_arg_1429_);
leanh::lean_dec_ref(v_arg_1426_);
v_a_1493_ = leanh::lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1500_ = (!leanh::lean_is_exclusive(v___x_1460_)) as u8;
if v_isSharedCheck_1500_ == 0 {
v___x_1495_ = v___x_1460_;
v_isShared_1496_ = v_isSharedCheck_1500_;
state = 22; continue;
} else {
leanh::lean_inc(v_a_1493_);
leanh::lean_dec(v___x_1460_);
v___x_1495_ = leanh::lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
state = 22; continue;
}
}
                                                                            }
                                                                        } else {
                                                                            leanh::lean_dec_ref(v___x_1447_);
                                                                            leanh::lean_del_object(v___x_1417_);
                                                                            v___x_1501_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_1432_, v_a_1347_);
                                                                            if leanh::lean_obj_tag(v___x_1501_) == 0 {
v_a_1502_ = leanh::lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1533_ = (!leanh::lean_is_exclusive(v___x_1501_)) as u8;
if v_isSharedCheck_1533_ == 0 {
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1533_;
state = 24; continue;
} else {
leanh::lean_inc(v_a_1502_);
leanh::lean_dec(v___x_1501_);
v___x_1504_ = leanh::lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1533_;
state = 24; continue;
}
} else {
leanh::lean_dec_ref(v_arg_1429_);
leanh::lean_dec_ref(v_arg_1426_);
v_a_1534_ = leanh::lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1541_ = (!leanh::lean_is_exclusive(v___x_1501_)) as u8;
if v_isSharedCheck_1541_ == 0 {
v___x_1536_ = v___x_1501_;
v_isShared_1537_ = v_isSharedCheck_1541_;
state = 30; continue;
} else {
leanh::lean_inc(v_a_1534_);
leanh::lean_dec(v___x_1501_);
v___x_1536_ = leanh::lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
state = 30; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v___x_1447_,
                                                                        );
                                                                        leanh::lean_del_object(v___x_1417_);
                                                                        v___x_1542_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1432_, v_a_1347_);
                                                                        if leanh::lean_obj_tag(v___x_1542_) == 0 {
v_a_1543_ = leanh::lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1574_ = (!leanh::lean_is_exclusive(v___x_1542_)) as u8;
if v_isSharedCheck_1574_ == 0 {
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1574_;
state = 32; continue;
} else {
leanh::lean_inc(v_a_1543_);
leanh::lean_dec(v___x_1542_);
v___x_1545_ = leanh::lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1574_;
state = 32; continue;
}
} else {
leanh::lean_dec_ref(v_arg_1429_);
leanh::lean_dec_ref(v_arg_1426_);
v_a_1575_ = leanh::lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1582_ = (!leanh::lean_is_exclusive(v___x_1542_)) as u8;
if v_isSharedCheck_1582_ == 0 {
v___x_1577_ = v___x_1542_;
v_isShared_1578_ = v_isSharedCheck_1582_;
state = 38; continue;
} else {
leanh::lean_inc(v_a_1575_);
leanh::lean_dec(v___x_1542_);
v___x_1577_ = leanh::lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
state = 38; continue;
}
}
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v___x_1447_,
                                                                    );
                                                                    leanh::lean_del_object(
                                                                        v___x_1417_,
                                                                    );
                                                                    v___x_1583_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_1432_, v_a_1347_);
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_1583_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_1584_ = leanh::lean_ctor_get(v___x_1583_, 0);
                                                                        v_isSharedCheck_1615_ = (!leanh::lean_is_exclusive(v___x_1583_)) as u8;
                                                                        if v_isSharedCheck_1615_
                                                                            == 0
                                                                        {
                                                                            v___x_1586_ =
                                                                                v___x_1583_;
                                                                            v_isShared_1587_ = v_isSharedCheck_1615_;
                                                                            state = 40;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_1584_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_1583_,
                                                                            );
                                                                            v___x_1586_ = leanh::lean_box(0);
                                                                            v_isShared_1587_ = v_isSharedCheck_1615_;
                                                                            state = 40;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_1429_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_1426_,
                                                                        );
                                                                        v_a_1616_ = leanh::lean_ctor_get(v___x_1583_, 0);
                                                                        v_isSharedCheck_1623_ = (!leanh::lean_is_exclusive(v___x_1583_)) as u8;
                                                                        if v_isSharedCheck_1623_
                                                                            == 0
                                                                        {
                                                                            v___x_1618_ =
                                                                                v___x_1583_;
                                                                            v_isShared_1619_ = v_isSharedCheck_1623_;
                                                                            state = 46;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_1616_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_1583_,
                                                                            );
                                                                            v___x_1618_ = leanh::lean_box(0);
                                                                            v_isShared_1619_ = v_isSharedCheck_1623_;
                                                                            state = 46;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_1447_,
                                                                );
                                                                leanh::lean_del_object(
                                                                    v___x_1417_,
                                                                );
                                                                v___x_1624_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_1432_, v_a_1347_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_1624_,
                                                                ) == 0
                                                                {
                                                                    v_a_1625_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_1624_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1656_ = (!leanh::lean_is_exclusive(v___x_1624_)) as u8;
                                                                    if v_isSharedCheck_1656_ == 0 {
                                                                        v___x_1627_ = v___x_1624_;
                                                                        v_isShared_1628_ =
                                                                            v_isSharedCheck_1656_;
                                                                        state = 48;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_1625_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_1624_,
                                                                        );
                                                                        v___x_1627_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1628_ =
                                                                            v_isSharedCheck_1656_;
                                                                        state = 48;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_1429_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_1426_,
                                                                    );
                                                                    v_a_1657_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_1624_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1664_ = (!leanh::lean_is_exclusive(v___x_1624_)) as u8;
                                                                    if v_isSharedCheck_1664_ == 0 {
                                                                        v___x_1659_ = v___x_1624_;
                                                                        v_isShared_1660_ =
                                                                            v_isSharedCheck_1664_;
                                                                        state = 54;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_1657_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_1624_,
                                                                        );
                                                                        v___x_1659_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1660_ =
                                                                            v_isSharedCheck_1664_;
                                                                        state = 54;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v___x_1447_);
                                                            leanh::lean_del_object(
                                                                v___x_1417_,
                                                            );
                                                            v___x_1665_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_1432_, v_a_1347_);
                                                            if leanh::lean_obj_tag(
                                                                v___x_1665_,
                                                            ) == 0
                                                            {
                                                                v_a_1666_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_1665_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_1727_ = (!leanh::lean_is_exclusive(v___x_1665_)) as u8;
                                                                if v_isSharedCheck_1727_ == 0 {
                                                                    v___x_1668_ = v___x_1665_;
                                                                    v_isShared_1669_ =
                                                                        v_isSharedCheck_1727_;
                                                                    state = 56;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_1666_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_1665_,
                                                                    );
                                                                    v___x_1668_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_1669_ =
                                                                        v_isSharedCheck_1727_;
                                                                    state = 56;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v_arg_1429_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_1426_,
                                                                );
                                                                v_a_1728_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_1665_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_1735_ = (!leanh::lean_is_exclusive(v___x_1665_)) as u8;
                                                                if v_isSharedCheck_1735_ == 0 {
                                                                    v___x_1730_ = v___x_1665_;
                                                                    v_isShared_1731_ =
                                                                        v_isSharedCheck_1735_;
                                                                    state = 69;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_1728_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_1665_,
                                                                    );
                                                                    v___x_1730_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_1731_ =
                                                                        v_isSharedCheck_1735_;
                                                                    state = 69;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_1433_);
                                            leanh::lean_dec_ref(v_arg_1432_);
                                            leanh::lean_del_object(v___x_1417_);
                                            v___x_1736_ =
                                                l_Lean_Meta_Structural_isInstNegInt___redArg(
                                                    v_arg_1429_,
                                                    v_a_1347_,
                                                );
                                            if leanh::lean_obj_tag(v___x_1736_) == 0 {
                                                v_a_1737_ =
                                                    leanh::lean_ctor_get(v___x_1736_, 0);
                                                v_isSharedCheck_1765_ =
                                                    (!leanh::lean_is_exclusive(v___x_1736_))
                                                        as u8;
                                                if v_isSharedCheck_1765_ == 0 {
                                                    v___x_1739_ = v___x_1736_;
                                                    v_isShared_1740_ = v_isSharedCheck_1765_;
                                                    state = 71;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_1737_);
                                                    leanh::lean_dec(v___x_1736_);
                                                    v___x_1739_ = leanh::lean_box(0);
                                                    v_isShared_1740_ = v_isSharedCheck_1765_;
                                                    state = 71;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v_arg_1426_);
                                                v_a_1766_ =
                                                    leanh::lean_ctor_get(v___x_1736_, 0);
                                                v_isSharedCheck_1773_ =
                                                    (!leanh::lean_is_exclusive(v___x_1736_))
                                                        as u8;
                                                if v_isSharedCheck_1773_ == 0 {
                                                    v___x_1768_ = v___x_1736_;
                                                    v_isShared_1769_ = v_isSharedCheck_1773_;
                                                    state = 77;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_1766_);
                                                    leanh::lean_dec(v___x_1736_);
                                                    v___x_1768_ = leanh::lean_box(0);
                                                    v_isShared_1769_ = v_isSharedCheck_1773_;
                                                    state = 77;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_1433_);
                                        leanh::lean_dec_ref(v_arg_1432_);
                                        leanh::lean_dec_ref(v_arg_1429_);
                                        leanh::lean_dec_ref(v_arg_1426_);
                                        leanh::lean_del_object(v___x_1417_);
                                        v___x_1774_ = l_Lean_Meta_getIntValue_x3f(
                                            v_e_1340_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_,
                                        );
                                        if leanh::lean_obj_tag(v___x_1774_) == 0 {
                                            v_a_1775_ = leanh::lean_ctor_get(v___x_1774_, 0);
                                            leanh::lean_inc(v_a_1775_);
                                            if leanh::lean_obj_tag(v_a_1775_) == 1 {
                                                leanh::lean_dec_ref_known(v_a_1775_, 1);
                                                return v___x_1774_;
                                            } else {
                                                leanh::lean_dec(v_a_1775_);
                                                v_isSharedCheck_1783_ =
                                                    (!leanh::lean_is_exclusive(v___x_1774_))
                                                        as u8;
                                                if v_isSharedCheck_1783_ == 0 {
                                                    v_unused_1784_ =
                                                        leanh::lean_ctor_get(v___x_1774_, 0);
                                                    leanh::lean_dec(v_unused_1784_);
                                                    v___x_1777_ = v___x_1774_;
                                                    v_isShared_1778_ = v_isSharedCheck_1783_;
                                                    state = 79;
                                                    continue;
                                                } else {
                                                    leanh::lean_dec(v___x_1774_);
                                                    v___x_1777_ = leanh::lean_box(0);
                                                    v_isShared_1778_ = v_isSharedCheck_1783_;
                                                    state = 79;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            return v___x_1774_;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_1433_);
                                    leanh::lean_dec_ref(v_arg_1432_);
                                    leanh::lean_del_object(v___x_1417_);
                                    leanh::lean_dec_ref(v_e_1340_);
                                    v_i_1352_ = v_arg_1429_;
                                    v_a_1353_ = v_arg_1426_;
                                    v___y_1354_ = v_a_1341_;
                                    v___y_1355_ = v_a_1342_;
                                    v___y_1356_ = v_a_1343_;
                                    v___y_1357_ = v_a_1344_;
                                    v___y_1358_ = v_a_1345_;
                                    v___y_1359_ = v_a_1346_;
                                    v___y_1360_ = v_a_1347_;
                                    v___y_1361_ = v_a_1348_;
                                    v___y_1362_ = v_a_1349_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1433_);
                                leanh::lean_dec_ref(v_arg_1432_);
                                leanh::lean_del_object(v___x_1417_);
                                leanh::lean_dec_ref(v_e_1340_);
                                v_i_1352_ = v_arg_1429_;
                                v_a_1353_ = v_arg_1426_;
                                v___y_1354_ = v_a_1341_;
                                v___y_1355_ = v_a_1342_;
                                v___y_1356_ = v_a_1343_;
                                v___y_1357_ = v_a_1344_;
                                v___y_1358_ = v_a_1345_;
                                v___y_1359_ = v_a_1346_;
                                v___y_1360_ = v_a_1347_;
                                v___y_1361_ = v_a_1348_;
                                v___y_1362_ = v_a_1349_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            14 => {
                v___x_1420_ = leanh::lean_box(0);
                if v_isShared_1418_ == 0 {
                    leanh::lean_ctor_set(v___x_1417_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1417_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
                    v___x_1422_ = v_reuseFailAlloc_1423_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1422_;
            }
            16 => {
                v___x_1465_ = (leanh::lean_unbox(v_a_1461_) as u8);
                leanh::lean_dec(v_a_1461_);
                if v___x_1465_ == 0 {
                    leanh::lean_dec_ref(v_arg_1429_);
                    leanh::lean_dec_ref(v_arg_1426_);
                    v___x_1466_ = leanh::lean_box(0);
                    if v_isShared_1464_ == 0 {
                        leanh::lean_ctor_set(v___x_1463_, 0, v___x_1466_);
                        v___x_1468_ = v___x_1463_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
                        v___x_1468_ = v_reuseFailAlloc_1469_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1463_);
                    v___x_1470_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if leanh::lean_obj_tag(v___x_1470_) == 0 {
                        v_a_1471_ = leanh::lean_ctor_get(v___x_1470_, 0);
                        leanh::lean_inc(v_a_1471_);
                        if leanh::lean_obj_tag(v_a_1471_) == 0 {
                            leanh::lean_dec_ref(v_arg_1426_);
                            return v___x_1470_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1470_, 1);
                            v_val_1472_ = leanh::lean_ctor_get(v_a_1471_, 0);
                            leanh::lean_inc(v_val_1472_);
                            leanh::lean_dec_ref_known(v_a_1471_, 1);
                            v___x_1473_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if leanh::lean_obj_tag(v___x_1473_) == 0 {
                                v_a_1474_ = leanh::lean_ctor_get(v___x_1473_, 0);
                                leanh::lean_inc(v_a_1474_);
                                if leanh::lean_obj_tag(v_a_1474_) == 0 {
                                    leanh::lean_dec(v_val_1472_);
                                    return v___x_1473_;
                                } else {
                                    v_isSharedCheck_1490_ =
                                        (!leanh::lean_is_exclusive(v___x_1473_)) as u8;
                                    if v_isSharedCheck_1490_ == 0 {
                                        v_unused_1491_ =
                                            leanh::lean_ctor_get(v___x_1473_, 0);
                                        leanh::lean_dec(v_unused_1491_);
                                        v___x_1476_ = v___x_1473_;
                                        v_isShared_1477_ = v_isSharedCheck_1490_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1473_);
                                        v___x_1476_ = leanh::lean_box(0);
                                        v_isShared_1477_ = v_isSharedCheck_1490_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1472_);
                                return v___x_1473_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1426_);
                        return v___x_1470_;
                    }
                }
            }
            17 => {
                return v___x_1468_;
            }
            18 => {
                v_val_1478_ = leanh::lean_ctor_get(v_a_1474_, 0);
                v_isSharedCheck_1489_ = (!leanh::lean_is_exclusive(v_a_1474_)) as u8;
                if v_isSharedCheck_1489_ == 0 {
                    v___x_1480_ = v_a_1474_;
                    v_isShared_1481_ = v_isSharedCheck_1489_;
                    state = 19;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1478_);
                    leanh::lean_dec(v_a_1474_);
                    v___x_1480_ = leanh::lean_box(0);
                    v_isShared_1481_ = v_isSharedCheck_1489_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1482_ = lean_int_add(v_val_1472_, v_val_1478_);
                leanh::lean_dec(v_val_1478_);
                leanh::lean_dec(v_val_1472_);
                if v_isShared_1481_ == 0 {
                    leanh::lean_ctor_set(v___x_1480_, 0, v___x_1482_);
                    v___x_1484_ = v___x_1480_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1482_);
                    v___x_1484_ = v_reuseFailAlloc_1488_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1477_ == 0 {
                    leanh::lean_ctor_set(v___x_1476_, 0, v___x_1484_);
                    v___x_1486_ = v___x_1476_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
                    v___x_1486_ = v_reuseFailAlloc_1487_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1486_;
            }
            22 => {
                if v_isShared_1496_ == 0 {
                    v___x_1498_ = v___x_1495_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1499_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
                    v___x_1498_ = v_reuseFailAlloc_1499_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1498_;
            }
            24 => {
                v___x_1506_ = (leanh::lean_unbox(v_a_1502_) as u8);
                leanh::lean_dec(v_a_1502_);
                if v___x_1506_ == 0 {
                    leanh::lean_dec_ref(v_arg_1429_);
                    leanh::lean_dec_ref(v_arg_1426_);
                    v___x_1507_ = leanh::lean_box(0);
                    if v_isShared_1505_ == 0 {
                        leanh::lean_ctor_set(v___x_1504_, 0, v___x_1507_);
                        v___x_1509_ = v___x_1504_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_1510_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
                        v___x_1509_ = v_reuseFailAlloc_1510_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1504_);
                    v___x_1511_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if leanh::lean_obj_tag(v___x_1511_) == 0 {
                        v_a_1512_ = leanh::lean_ctor_get(v___x_1511_, 0);
                        leanh::lean_inc(v_a_1512_);
                        if leanh::lean_obj_tag(v_a_1512_) == 0 {
                            leanh::lean_dec_ref(v_arg_1426_);
                            return v___x_1511_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1511_, 1);
                            v_val_1513_ = leanh::lean_ctor_get(v_a_1512_, 0);
                            leanh::lean_inc(v_val_1513_);
                            leanh::lean_dec_ref_known(v_a_1512_, 1);
                            v___x_1514_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if leanh::lean_obj_tag(v___x_1514_) == 0 {
                                v_a_1515_ = leanh::lean_ctor_get(v___x_1514_, 0);
                                leanh::lean_inc(v_a_1515_);
                                if leanh::lean_obj_tag(v_a_1515_) == 0 {
                                    leanh::lean_dec(v_val_1513_);
                                    return v___x_1514_;
                                } else {
                                    v_isSharedCheck_1531_ =
                                        (!leanh::lean_is_exclusive(v___x_1514_)) as u8;
                                    if v_isSharedCheck_1531_ == 0 {
                                        v_unused_1532_ =
                                            leanh::lean_ctor_get(v___x_1514_, 0);
                                        leanh::lean_dec(v_unused_1532_);
                                        v___x_1517_ = v___x_1514_;
                                        v_isShared_1518_ = v_isSharedCheck_1531_;
                                        state = 26;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1514_);
                                        v___x_1517_ = leanh::lean_box(0);
                                        v_isShared_1518_ = v_isSharedCheck_1531_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1513_);
                                return v___x_1514_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1426_);
                        return v___x_1511_;
                    }
                }
            }
            25 => {
                return v___x_1509_;
            }
            26 => {
                v_val_1519_ = leanh::lean_ctor_get(v_a_1515_, 0);
                v_isSharedCheck_1530_ = (!leanh::lean_is_exclusive(v_a_1515_)) as u8;
                if v_isSharedCheck_1530_ == 0 {
                    v___x_1521_ = v_a_1515_;
                    v_isShared_1522_ = v_isSharedCheck_1530_;
                    state = 27;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1519_);
                    leanh::lean_dec(v_a_1515_);
                    v___x_1521_ = leanh::lean_box(0);
                    v_isShared_1522_ = v_isSharedCheck_1530_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_1523_ = lean_int_sub(v_val_1513_, v_val_1519_);
                leanh::lean_dec(v_val_1519_);
                leanh::lean_dec(v_val_1513_);
                if v_isShared_1522_ == 0 {
                    leanh::lean_ctor_set(v___x_1521_, 0, v___x_1523_);
                    v___x_1525_ = v___x_1521_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1529_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1523_);
                    v___x_1525_ = v_reuseFailAlloc_1529_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_1518_ == 0 {
                    leanh::lean_ctor_set(v___x_1517_, 0, v___x_1525_);
                    v___x_1527_ = v___x_1517_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1528_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
                    v___x_1527_ = v_reuseFailAlloc_1528_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1527_;
            }
            30 => {
                if v_isShared_1537_ == 0 {
                    v___x_1539_ = v___x_1536_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1540_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
                    v___x_1539_ = v_reuseFailAlloc_1540_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1539_;
            }
            32 => {
                v___x_1547_ = (leanh::lean_unbox(v_a_1543_) as u8);
                leanh::lean_dec(v_a_1543_);
                if v___x_1547_ == 0 {
                    leanh::lean_dec_ref(v_arg_1429_);
                    leanh::lean_dec_ref(v_arg_1426_);
                    v___x_1548_ = leanh::lean_box(0);
                    if v_isShared_1546_ == 0 {
                        leanh::lean_ctor_set(v___x_1545_, 0, v___x_1548_);
                        v___x_1550_ = v___x_1545_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_1551_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
                        v___x_1550_ = v_reuseFailAlloc_1551_;
                        state = 33;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1545_);
                    v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if leanh::lean_obj_tag(v___x_1552_) == 0 {
                        v_a_1553_ = leanh::lean_ctor_get(v___x_1552_, 0);
                        leanh::lean_inc(v_a_1553_);
                        if leanh::lean_obj_tag(v_a_1553_) == 0 {
                            leanh::lean_dec_ref(v_arg_1426_);
                            return v___x_1552_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1552_, 1);
                            v_val_1554_ = leanh::lean_ctor_get(v_a_1553_, 0);
                            leanh::lean_inc(v_val_1554_);
                            leanh::lean_dec_ref_known(v_a_1553_, 1);
                            v___x_1555_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if leanh::lean_obj_tag(v___x_1555_) == 0 {
                                v_a_1556_ = leanh::lean_ctor_get(v___x_1555_, 0);
                                leanh::lean_inc(v_a_1556_);
                                if leanh::lean_obj_tag(v_a_1556_) == 0 {
                                    leanh::lean_dec(v_val_1554_);
                                    return v___x_1555_;
                                } else {
                                    v_isSharedCheck_1572_ =
                                        (!leanh::lean_is_exclusive(v___x_1555_)) as u8;
                                    if v_isSharedCheck_1572_ == 0 {
                                        v_unused_1573_ =
                                            leanh::lean_ctor_get(v___x_1555_, 0);
                                        leanh::lean_dec(v_unused_1573_);
                                        v___x_1558_ = v___x_1555_;
                                        v_isShared_1559_ = v_isSharedCheck_1572_;
                                        state = 34;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1555_);
                                        v___x_1558_ = leanh::lean_box(0);
                                        v_isShared_1559_ = v_isSharedCheck_1572_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1554_);
                                return v___x_1555_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1426_);
                        return v___x_1552_;
                    }
                }
            }
            33 => {
                return v___x_1550_;
            }
            34 => {
                v_val_1560_ = leanh::lean_ctor_get(v_a_1556_, 0);
                v_isSharedCheck_1571_ = (!leanh::lean_is_exclusive(v_a_1556_)) as u8;
                if v_isSharedCheck_1571_ == 0 {
                    v___x_1562_ = v_a_1556_;
                    v_isShared_1563_ = v_isSharedCheck_1571_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1560_);
                    leanh::lean_dec(v_a_1556_);
                    v___x_1562_ = leanh::lean_box(0);
                    v_isShared_1563_ = v_isSharedCheck_1571_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1564_ = lean_int_mul(v_val_1554_, v_val_1560_);
                leanh::lean_dec(v_val_1560_);
                leanh::lean_dec(v_val_1554_);
                if v_isShared_1563_ == 0 {
                    leanh::lean_ctor_set(v___x_1562_, 0, v___x_1564_);
                    v___x_1566_ = v___x_1562_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
                    v___x_1566_ = v_reuseFailAlloc_1570_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1559_ == 0 {
                    leanh::lean_ctor_set(v___x_1558_, 0, v___x_1566_);
                    v___x_1568_ = v___x_1558_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
                    v___x_1568_ = v_reuseFailAlloc_1569_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1568_;
            }
            38 => {
                if v_isShared_1578_ == 0 {
                    v___x_1580_ = v___x_1577_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1580_;
            }
            40 => {
                v___x_1588_ = (leanh::lean_unbox(v_a_1584_) as u8);
                leanh::lean_dec(v_a_1584_);
                if v___x_1588_ == 0 {
                    leanh::lean_dec_ref(v_arg_1429_);
                    leanh::lean_dec_ref(v_arg_1426_);
                    v___x_1589_ = leanh::lean_box(0);
                    if v_isShared_1587_ == 0 {
                        leanh::lean_ctor_set(v___x_1586_, 0, v___x_1589_);
                        v___x_1591_ = v___x_1586_;
                        state = 41;
                        continue;
                    } else {
                        v_reuseFailAlloc_1592_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
                        v___x_1591_ = v_reuseFailAlloc_1592_;
                        state = 41;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1586_);
                    v___x_1593_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if leanh::lean_obj_tag(v___x_1593_) == 0 {
                        v_a_1594_ = leanh::lean_ctor_get(v___x_1593_, 0);
                        leanh::lean_inc(v_a_1594_);
                        if leanh::lean_obj_tag(v_a_1594_) == 0 {
                            leanh::lean_dec_ref(v_arg_1426_);
                            return v___x_1593_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1593_, 1);
                            v_val_1595_ = leanh::lean_ctor_get(v_a_1594_, 0);
                            leanh::lean_inc(v_val_1595_);
                            leanh::lean_dec_ref_known(v_a_1594_, 1);
                            v___x_1596_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if leanh::lean_obj_tag(v___x_1596_) == 0 {
                                v_a_1597_ = leanh::lean_ctor_get(v___x_1596_, 0);
                                leanh::lean_inc(v_a_1597_);
                                if leanh::lean_obj_tag(v_a_1597_) == 0 {
                                    leanh::lean_dec(v_val_1595_);
                                    return v___x_1596_;
                                } else {
                                    v_isSharedCheck_1613_ =
                                        (!leanh::lean_is_exclusive(v___x_1596_)) as u8;
                                    if v_isSharedCheck_1613_ == 0 {
                                        v_unused_1614_ =
                                            leanh::lean_ctor_get(v___x_1596_, 0);
                                        leanh::lean_dec(v_unused_1614_);
                                        v___x_1599_ = v___x_1596_;
                                        v_isShared_1600_ = v_isSharedCheck_1613_;
                                        state = 42;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1596_);
                                        v___x_1599_ = leanh::lean_box(0);
                                        v_isShared_1600_ = v_isSharedCheck_1613_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1595_);
                                return v___x_1596_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1426_);
                        return v___x_1593_;
                    }
                }
            }
            41 => {
                return v___x_1591_;
            }
            42 => {
                v_val_1601_ = leanh::lean_ctor_get(v_a_1597_, 0);
                v_isSharedCheck_1612_ = (!leanh::lean_is_exclusive(v_a_1597_)) as u8;
                if v_isSharedCheck_1612_ == 0 {
                    v___x_1603_ = v_a_1597_;
                    v_isShared_1604_ = v_isSharedCheck_1612_;
                    state = 43;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1601_);
                    leanh::lean_dec(v_a_1597_);
                    v___x_1603_ = leanh::lean_box(0);
                    v_isShared_1604_ = v_isSharedCheck_1612_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_1605_ = lean_int_ediv(v_val_1595_, v_val_1601_);
                leanh::lean_dec(v_val_1601_);
                leanh::lean_dec(v_val_1595_);
                if v_isShared_1604_ == 0 {
                    leanh::lean_ctor_set(v___x_1603_, 0, v___x_1605_);
                    v___x_1607_ = v___x_1603_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1605_);
                    v___x_1607_ = v_reuseFailAlloc_1611_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_1600_ == 0 {
                    leanh::lean_ctor_set(v___x_1599_, 0, v___x_1607_);
                    v___x_1609_ = v___x_1599_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1610_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
                    v___x_1609_ = v_reuseFailAlloc_1610_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_1609_;
            }
            46 => {
                if v_isShared_1619_ == 0 {
                    v___x_1621_ = v___x_1618_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
                    v___x_1621_ = v_reuseFailAlloc_1622_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1621_;
            }
            48 => {
                v___x_1629_ = (leanh::lean_unbox(v_a_1625_) as u8);
                leanh::lean_dec(v_a_1625_);
                if v___x_1629_ == 0 {
                    leanh::lean_dec_ref(v_arg_1429_);
                    leanh::lean_dec_ref(v_arg_1426_);
                    v___x_1630_ = leanh::lean_box(0);
                    if v_isShared_1628_ == 0 {
                        leanh::lean_ctor_set(v___x_1627_, 0, v___x_1630_);
                        v___x_1632_ = v___x_1627_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_1633_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
                        v___x_1632_ = v_reuseFailAlloc_1633_;
                        state = 49;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1627_);
                    v___x_1634_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if leanh::lean_obj_tag(v___x_1634_) == 0 {
                        v_a_1635_ = leanh::lean_ctor_get(v___x_1634_, 0);
                        leanh::lean_inc(v_a_1635_);
                        if leanh::lean_obj_tag(v_a_1635_) == 0 {
                            leanh::lean_dec_ref(v_arg_1426_);
                            return v___x_1634_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1634_, 1);
                            v_val_1636_ = leanh::lean_ctor_get(v_a_1635_, 0);
                            leanh::lean_inc(v_val_1636_);
                            leanh::lean_dec_ref_known(v_a_1635_, 1);
                            v___x_1637_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if leanh::lean_obj_tag(v___x_1637_) == 0 {
                                v_a_1638_ = leanh::lean_ctor_get(v___x_1637_, 0);
                                leanh::lean_inc(v_a_1638_);
                                if leanh::lean_obj_tag(v_a_1638_) == 0 {
                                    leanh::lean_dec(v_val_1636_);
                                    return v___x_1637_;
                                } else {
                                    v_isSharedCheck_1654_ =
                                        (!leanh::lean_is_exclusive(v___x_1637_)) as u8;
                                    if v_isSharedCheck_1654_ == 0 {
                                        v_unused_1655_ =
                                            leanh::lean_ctor_get(v___x_1637_, 0);
                                        leanh::lean_dec(v_unused_1655_);
                                        v___x_1640_ = v___x_1637_;
                                        v_isShared_1641_ = v_isSharedCheck_1654_;
                                        state = 50;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1637_);
                                        v___x_1640_ = leanh::lean_box(0);
                                        v_isShared_1641_ = v_isSharedCheck_1654_;
                                        state = 50;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1636_);
                                return v___x_1637_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1426_);
                        return v___x_1634_;
                    }
                }
            }
            49 => {
                return v___x_1632_;
            }
            50 => {
                v_val_1642_ = leanh::lean_ctor_get(v_a_1638_, 0);
                v_isSharedCheck_1653_ = (!leanh::lean_is_exclusive(v_a_1638_)) as u8;
                if v_isSharedCheck_1653_ == 0 {
                    v___x_1644_ = v_a_1638_;
                    v_isShared_1645_ = v_isSharedCheck_1653_;
                    state = 51;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1642_);
                    leanh::lean_dec(v_a_1638_);
                    v___x_1644_ = leanh::lean_box(0);
                    v_isShared_1645_ = v_isSharedCheck_1653_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                v___x_1646_ = lean_int_emod(v_val_1636_, v_val_1642_);
                leanh::lean_dec(v_val_1642_);
                leanh::lean_dec(v_val_1636_);
                if v_isShared_1645_ == 0 {
                    leanh::lean_ctor_set(v___x_1644_, 0, v___x_1646_);
                    v___x_1648_ = v___x_1644_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1646_);
                    v___x_1648_ = v_reuseFailAlloc_1652_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                if v_isShared_1641_ == 0 {
                    leanh::lean_ctor_set(v___x_1640_, 0, v___x_1648_);
                    v___x_1650_ = v___x_1640_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_1651_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
                    v___x_1650_ = v_reuseFailAlloc_1651_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_1650_;
            }
            54 => {
                if v_isShared_1660_ == 0 {
                    v___x_1662_ = v___x_1659_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_1663_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
                    v___x_1662_ = v_reuseFailAlloc_1663_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_1662_;
            }
            56 => {
                v___x_1670_ = (leanh::lean_unbox(v_a_1666_) as u8);
                leanh::lean_dec(v_a_1666_);
                if v___x_1670_ == 0 {
                    leanh::lean_dec_ref(v_arg_1429_);
                    leanh::lean_dec_ref(v_arg_1426_);
                    v___x_1671_ = leanh::lean_box(0);
                    if v_isShared_1669_ == 0 {
                        leanh::lean_ctor_set(v___x_1668_, 0, v___x_1671_);
                        v___x_1673_ = v___x_1668_;
                        state = 57;
                        continue;
                    } else {
                        v_reuseFailAlloc_1674_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
                        v___x_1673_ = v_reuseFailAlloc_1674_;
                        state = 57;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1668_);
                    v___x_1675_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if leanh::lean_obj_tag(v___x_1675_) == 0 {
                        v_a_1676_ = leanh::lean_ctor_get(v___x_1675_, 0);
                        leanh::lean_inc(v_a_1676_);
                        if leanh::lean_obj_tag(v_a_1676_) == 0 {
                            leanh::lean_dec_ref(v_arg_1426_);
                            return v___x_1675_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1675_, 1);
                            v_val_1677_ = leanh::lean_ctor_get(v_a_1676_, 0);
                            leanh::lean_inc(v_val_1677_);
                            leanh::lean_dec_ref_known(v_a_1676_, 1);
                            v___x_1678_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if leanh::lean_obj_tag(v___x_1678_) == 0 {
                                v_a_1679_ = leanh::lean_ctor_get(v___x_1678_, 0);
                                v_isSharedCheck_1718_ =
                                    (!leanh::lean_is_exclusive(v___x_1678_)) as u8;
                                if v_isSharedCheck_1718_ == 0 {
                                    v___x_1681_ = v___x_1678_;
                                    v_isShared_1682_ = v_isSharedCheck_1718_;
                                    state = 58;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1679_);
                                    leanh::lean_dec(v___x_1678_);
                                    v___x_1681_ = leanh::lean_box(0);
                                    v_isShared_1682_ = v_isSharedCheck_1718_;
                                    state = 58;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_1677_);
                                v_a_1719_ = leanh::lean_ctor_get(v___x_1678_, 0);
                                v_isSharedCheck_1726_ =
                                    (!leanh::lean_is_exclusive(v___x_1678_)) as u8;
                                if v_isSharedCheck_1726_ == 0 {
                                    v___x_1721_ = v___x_1678_;
                                    v_isShared_1722_ = v_isSharedCheck_1726_;
                                    state = 67;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1719_);
                                    leanh::lean_dec(v___x_1678_);
                                    v___x_1721_ = leanh::lean_box(0);
                                    v_isShared_1722_ = v_isSharedCheck_1726_;
                                    state = 67;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1426_);
                        return v___x_1675_;
                    }
                }
            }
            57 => {
                return v___x_1673_;
            }
            58 => {
                if leanh::lean_obj_tag(v_a_1679_) == 0 {
                    leanh::lean_dec(v_val_1677_);
                    v___x_1683_ = leanh::lean_box(0);
                    if v_isShared_1682_ == 0 {
                        leanh::lean_ctor_set(v___x_1681_, 0, v___x_1683_);
                        v___x_1685_ = v___x_1681_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_1686_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
                        v___x_1685_ = v_reuseFailAlloc_1686_;
                        state = 59;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1681_);
                    v_val_1687_ = leanh::lean_ctor_get(v_a_1679_, 0);
                    leanh::lean_inc_n(v_val_1687_, 2);
                    leanh::lean_dec_ref_known(v_a_1679_, 1);
                    v___x_1688_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(
                        v_val_1687_,
                        v_a_1342_,
                        v_a_1344_,
                        v_a_1345_,
                        v_a_1346_,
                        v_a_1347_,
                        v_a_1348_,
                        v_a_1349_,
                    );
                    if leanh::lean_obj_tag(v___x_1688_) == 0 {
                        v_a_1689_ = leanh::lean_ctor_get(v___x_1688_, 0);
                        v_isSharedCheck_1709_ =
                            (!leanh::lean_is_exclusive(v___x_1688_)) as u8;
                        if v_isSharedCheck_1709_ == 0 {
                            v___x_1691_ = v___x_1688_;
                            v_isShared_1692_ = v_isSharedCheck_1709_;
                            state = 60;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1689_);
                            leanh::lean_dec(v___x_1688_);
                            v___x_1691_ = leanh::lean_box(0);
                            v_isShared_1692_ = v_isSharedCheck_1709_;
                            state = 60;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_1687_);
                        leanh::lean_dec(v_val_1677_);
                        v_a_1710_ = leanh::lean_ctor_get(v___x_1688_, 0);
                        v_isSharedCheck_1717_ =
                            (!leanh::lean_is_exclusive(v___x_1688_)) as u8;
                        if v_isSharedCheck_1717_ == 0 {
                            v___x_1712_ = v___x_1688_;
                            v_isShared_1713_ = v_isSharedCheck_1717_;
                            state = 65;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1710_);
                            leanh::lean_dec(v___x_1688_);
                            v___x_1712_ = leanh::lean_box(0);
                            v_isShared_1713_ = v_isSharedCheck_1717_;
                            state = 65;
                            continue;
                        }
                    }
                }
            }
            59 => {
                return v___x_1685_;
            }
            60 => {
                if leanh::lean_obj_tag(v_a_1689_) == 0 {
                    leanh::lean_dec(v_val_1687_);
                    leanh::lean_dec(v_val_1677_);
                    v___x_1693_ = leanh::lean_box(0);
                    if v_isShared_1692_ == 0 {
                        leanh::lean_ctor_set(v___x_1691_, 0, v___x_1693_);
                        v___x_1695_ = v___x_1691_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_1696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
                        v___x_1695_ = v_reuseFailAlloc_1696_;
                        state = 61;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1707_ = (!leanh::lean_is_exclusive(v_a_1689_)) as u8;
                    if v_isSharedCheck_1707_ == 0 {
                        v_unused_1708_ = leanh::lean_ctor_get(v_a_1689_, 0);
                        leanh::lean_dec(v_unused_1708_);
                        v___x_1698_ = v_a_1689_;
                        v_isShared_1699_ = v_isSharedCheck_1707_;
                        state = 62;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_1689_);
                        v___x_1698_ = leanh::lean_box(0);
                        v_isShared_1699_ = v_isSharedCheck_1707_;
                        state = 62;
                        continue;
                    }
                }
            }
            61 => {
                return v___x_1695_;
            }
            62 => {
                v___x_1700_ = l_Int_pow(v_val_1677_, v_val_1687_);
                leanh::lean_dec(v_val_1687_);
                leanh::lean_dec(v_val_1677_);
                if v_isShared_1699_ == 0 {
                    leanh::lean_ctor_set(v___x_1698_, 0, v___x_1700_);
                    v___x_1702_ = v___x_1698_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_1706_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1700_);
                    v___x_1702_ = v_reuseFailAlloc_1706_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v_isShared_1692_ == 0 {
                    leanh::lean_ctor_set(v___x_1691_, 0, v___x_1702_);
                    v___x_1704_ = v___x_1691_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
                    v___x_1704_ = v_reuseFailAlloc_1705_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_1704_;
            }
            65 => {
                if v_isShared_1713_ == 0 {
                    v___x_1715_ = v___x_1712_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
                    v___x_1715_ = v_reuseFailAlloc_1716_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_1715_;
            }
            67 => {
                if v_isShared_1722_ == 0 {
                    v___x_1724_ = v___x_1721_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_1725_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
                    v___x_1724_ = v_reuseFailAlloc_1725_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_1724_;
            }
            69 => {
                if v_isShared_1731_ == 0 {
                    v___x_1733_ = v___x_1730_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_1733_;
            }
            71 => {
                v___x_1741_ = (leanh::lean_unbox(v_a_1737_) as u8);
                leanh::lean_dec(v_a_1737_);
                if v___x_1741_ == 0 {
                    leanh::lean_dec_ref(v_arg_1426_);
                    v___x_1742_ = leanh::lean_box(0);
                    if v_isShared_1740_ == 0 {
                        leanh::lean_ctor_set(v___x_1739_, 0, v___x_1742_);
                        v___x_1744_ = v___x_1739_;
                        state = 72;
                        continue;
                    } else {
                        v_reuseFailAlloc_1745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
                        v___x_1744_ = v_reuseFailAlloc_1745_;
                        state = 72;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1739_);
                    v___x_1746_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if leanh::lean_obj_tag(v___x_1746_) == 0 {
                        v_a_1747_ = leanh::lean_ctor_get(v___x_1746_, 0);
                        leanh::lean_inc(v_a_1747_);
                        if leanh::lean_obj_tag(v_a_1747_) == 0 {
                            return v___x_1746_;
                        } else {
                            v_isSharedCheck_1763_ =
                                (!leanh::lean_is_exclusive(v___x_1746_)) as u8;
                            if v_isSharedCheck_1763_ == 0 {
                                v_unused_1764_ = leanh::lean_ctor_get(v___x_1746_, 0);
                                leanh::lean_dec(v_unused_1764_);
                                v___x_1749_ = v___x_1746_;
                                v_isShared_1750_ = v_isSharedCheck_1763_;
                                state = 73;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1746_);
                                v___x_1749_ = leanh::lean_box(0);
                                v_isShared_1750_ = v_isSharedCheck_1763_;
                                state = 73;
                                continue;
                            }
                        }
                    } else {
                        return v___x_1746_;
                    }
                }
            }
            72 => {
                return v___x_1744_;
            }
            73 => {
                v_val_1751_ = leanh::lean_ctor_get(v_a_1747_, 0);
                v_isSharedCheck_1762_ = (!leanh::lean_is_exclusive(v_a_1747_)) as u8;
                if v_isSharedCheck_1762_ == 0 {
                    v___x_1753_ = v_a_1747_;
                    v_isShared_1754_ = v_isSharedCheck_1762_;
                    state = 74;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1751_);
                    leanh::lean_dec(v_a_1747_);
                    v___x_1753_ = leanh::lean_box(0);
                    v_isShared_1754_ = v_isSharedCheck_1762_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                v___x_1755_ = lean_int_neg(v_val_1751_);
                leanh::lean_dec(v_val_1751_);
                if v_isShared_1754_ == 0 {
                    leanh::lean_ctor_set(v___x_1753_, 0, v___x_1755_);
                    v___x_1757_ = v___x_1753_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_1761_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1755_);
                    v___x_1757_ = v_reuseFailAlloc_1761_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_1750_ == 0 {
                    leanh::lean_ctor_set(v___x_1749_, 0, v___x_1757_);
                    v___x_1759_ = v___x_1749_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
                    v___x_1759_ = v_reuseFailAlloc_1760_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                return v___x_1759_;
            }
            77 => {
                if v_isShared_1769_ == 0 {
                    v___x_1771_ = v___x_1768_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
                    v___x_1771_ = v_reuseFailAlloc_1772_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                return v___x_1771_;
            }
            79 => {
                v___x_1779_ = leanh::lean_box(0);
                if v_isShared_1778_ == 0 {
                    leanh::lean_ctor_set(v___x_1777_, 0, v___x_1779_);
                    v___x_1781_ = v___x_1777_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
                    v___x_1781_ = v_reuseFailAlloc_1782_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                return v___x_1781_;
            }
            81 => {
                if v_isShared_1789_ == 0 {
                    v___x_1791_ = v___x_1788_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
                    v___x_1791_ = v_reuseFailAlloc_1792_;
                    state = 82;
                    continue;
                }
            }
            82 => {
                return v___x_1791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(
    mut v_e_1794_: *mut leanh::LeanObject,
    mut v_a_1795_: *mut leanh::LeanObject,
    mut v_a_1796_: *mut leanh::LeanObject,
    mut v_a_1797_: *mut leanh::LeanObject,
    mut v_a_1798_: *mut leanh::LeanObject,
    mut v_a_1799_: *mut leanh::LeanObject,
    mut v_a_1800_: *mut leanh::LeanObject,
    mut v_a_1801_: *mut leanh::LeanObject,
    mut v_a_1802_: *mut leanh::LeanObject,
    mut v_a_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1812_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: u8 = 0;
    let mut v_arg_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: u8 = 0;
    let mut v_arg_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v_arg_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: u8 = 0;
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: u8 = 0;
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1855_: u8 = 0;
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1868_: u8 = 0;
    let mut v_val_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1872_: u8 = 0;
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v_unused_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1883_: u8 = 0;
    let mut v_a_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v_val_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v_unused_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1924_: u8 = 0;
    let mut v_a_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1928_: u8 = 0;
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1950_: u8 = 0;
    let mut v_val_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1954_: u8 = 0;
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_isSharedCheck_1963_: u8 = 0;
    let mut v_unused_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_a_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v_val_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v_unused_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_a_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v_val_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut v_unused_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut v_a_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v___x_2061_: u8 = 0;
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2073_: u8 = 0;
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v_val_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v_unused_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2097_: u8 = 0;
    let mut v_a_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut v_isSharedCheck_2106_: u8 = 0;
    let mut v_a_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2114_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_unused_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v_val_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2134_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2143_: u8 = 0;
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut v_unused_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_a_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2205_: u8 = 0;
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut v_a_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1794_);
                v___x_1808_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1794_, v_a_1801_);
                if leanh::lean_obj_tag(v___x_1808_) == 0 {
                    v_a_1809_ = leanh::lean_ctor_get(v___x_1808_, 0);
                    v_isSharedCheck_2210_ = (!leanh::lean_is_exclusive(v___x_1808_)) as u8;
                    if v_isSharedCheck_2210_ == 0 {
                        v___x_1811_ = v___x_1808_;
                        v_isShared_1812_ = v_isSharedCheck_2210_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1809_);
                        leanh::lean_dec(v___x_1808_);
                        v___x_1811_ = leanh::lean_box(0);
                        v_isShared_1812_ = v_isSharedCheck_2210_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1794_);
                    v_a_2211_ = leanh::lean_ctor_get(v___x_1808_, 0);
                    v_isSharedCheck_2218_ = (!leanh::lean_is_exclusive(v___x_1808_)) as u8;
                    if v_isSharedCheck_2218_ == 0 {
                        v___x_2213_ = v___x_1808_;
                        v_isShared_2214_ = v_isSharedCheck_2218_;
                        state = 76;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2211_);
                        leanh::lean_dec(v___x_1808_);
                        v___x_2213_ = leanh::lean_box(0);
                        v_isShared_2214_ = v_isSharedCheck_2218_;
                        state = 76;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1806_ = leanh::lean_box(0);
                v___x_1807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1807_, 0, v___x_1806_);
                return v___x_1807_;
            }
            2 => {
                v___x_1813_ = l_Lean_Expr_cleanupAnnotations(v_a_1809_);
                v___x_1814_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2;
                v___x_1815_ = l_Lean_Expr_isConstOf(v___x_1813_, v___x_1814_);
                if v___x_1815_ == 0 {
                    leanh::lean_del_object(v___x_1811_);
                    v___x_1816_ = l_Lean_Expr_isApp(v___x_1813_);
                    if v___x_1816_ == 0 {
                        leanh::lean_dec_ref(v___x_1813_);
                        leanh::lean_dec_ref(v_e_1794_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_1817_ = leanh::lean_ctor_get(v___x_1813_, 1);
                        leanh::lean_inc_ref(v_arg_1817_);
                        v___x_1818_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1813_);
                        v___x_1819_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5;
                        v___x_1820_ = l_Lean_Expr_isConstOf(v___x_1818_, v___x_1819_);
                        if v___x_1820_ == 0 {
                            v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7;
                            v___x_1822_ = l_Lean_Expr_isConstOf(v___x_1818_, v___x_1821_);
                            if v___x_1822_ == 0 {
                                v___x_1823_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9;
                                v___x_1824_ = l_Lean_Expr_isConstOf(v___x_1818_, v___x_1823_);
                                if v___x_1824_ == 0 {
                                    v___x_1825_ = l_Lean_Expr_isApp(v___x_1818_);
                                    if v___x_1825_ == 0 {
                                        leanh::lean_dec_ref(v___x_1818_);
                                        leanh::lean_dec_ref(v_arg_1817_);
                                        leanh::lean_dec_ref(v_e_1794_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_1826_ = leanh::lean_ctor_get(v___x_1818_, 1);
                                        leanh::lean_inc_ref(v_arg_1826_);
                                        v___x_1827_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_1818_);
                                        v___x_1828_ = l_Lean_Expr_isApp(v___x_1827_);
                                        if v___x_1828_ == 0 {
                                            leanh::lean_dec_ref(v___x_1827_);
                                            leanh::lean_dec_ref(v_arg_1826_);
                                            leanh::lean_dec_ref(v_arg_1817_);
                                            leanh::lean_dec_ref(v_e_1794_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_1829_ =
                                                leanh::lean_ctor_get(v___x_1827_, 1);
                                            leanh::lean_inc_ref(v_arg_1829_);
                                            v___x_1830_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_1827_);
                                            v___x_1831_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12;
                                            v___x_1832_ =
                                                l_Lean_Expr_isConstOf(v___x_1830_, v___x_1831_);
                                            if v___x_1832_ == 0 {
                                                leanh::lean_dec_ref(v_e_1794_);
                                                v___x_1833_ = l_Lean_Expr_isApp(v___x_1830_);
                                                if v___x_1833_ == 0 {
                                                    leanh::lean_dec_ref(v___x_1830_);
                                                    leanh::lean_dec_ref(v_arg_1829_);
                                                    leanh::lean_dec_ref(v_arg_1826_);
                                                    leanh::lean_dec_ref(v_arg_1817_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_1834_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1830_,
                                                    );
                                                    v___x_1835_ = l_Lean_Expr_isApp(v___x_1834_);
                                                    if v___x_1835_ == 0 {
                                                        leanh::lean_dec_ref(v___x_1834_);
                                                        leanh::lean_dec_ref(v_arg_1829_);
                                                        leanh::lean_dec_ref(v_arg_1826_);
                                                        leanh::lean_dec_ref(v_arg_1817_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1836_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_1834_,
                                                            );
                                                        v___x_1837_ =
                                                            l_Lean_Expr_isApp(v___x_1836_);
                                                        if v___x_1837_ == 0 {
                                                            leanh::lean_dec_ref(v___x_1836_);
                                                            leanh::lean_dec_ref(v_arg_1829_);
                                                            leanh::lean_dec_ref(v_arg_1826_);
                                                            leanh::lean_dec_ref(v_arg_1817_);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_1838_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_1836_,
                                                                );
                                                            v___x_1839_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15;
                                                            v___x_1840_ = l_Lean_Expr_isConstOf(
                                                                v___x_1838_,
                                                                v___x_1839_,
                                                            );
                                                            if v___x_1840_ == 0 {
                                                                v___x_1841_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18;
                                                                v___x_1842_ = l_Lean_Expr_isConstOf(
                                                                    v___x_1838_,
                                                                    v___x_1841_,
                                                                );
                                                                if v___x_1842_ == 0 {
                                                                    v___x_1843_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21;
                                                                    v___x_1844_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_1838_,
                                                                            v___x_1843_,
                                                                        );
                                                                    if v___x_1844_ == 0 {
                                                                        v___x_1845_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24;
                                                                        v___x_1846_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_1838_,
                                                                                v___x_1845_,
                                                                            );
                                                                        if v___x_1846_ == 0 {
                                                                            v___x_1847_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27;
                                                                            v___x_1848_ = l_Lean_Expr_isConstOf(v___x_1838_, v___x_1847_);
                                                                            if v___x_1848_ == 0 {
                                                                                v___x_1849_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30;
                                                                                v___x_1850_ = l_Lean_Expr_isConstOf(v___x_1838_, v___x_1849_);
                                                                                leanh::lean_dec_ref(v___x_1838_);
                                                                                if v___x_1850_ == 0
                                                                                {
                                                                                    leanh::lean_dec_ref(v_arg_1829_);
                                                                                    leanh::lean_dec_ref(v_arg_1826_);
                                                                                    leanh::lean_dec_ref(v_arg_1817_);
                                                                                    state = 1;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_1851_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_1829_, v_a_1801_);
                                                                                    if leanh::lean_obj_tag(v___x_1851_) == 0 {
v_a_1852_ = leanh::lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1883_ = (!leanh::lean_is_exclusive(v___x_1851_)) as u8;
if v_isSharedCheck_1883_ == 0 {
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1883_;
state = 3; continue;
} else {
leanh::lean_inc(v_a_1852_);
leanh::lean_dec(v___x_1851_);
v___x_1854_ = leanh::lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1883_;
state = 3; continue;
}
} else {
leanh::lean_dec_ref(v_arg_1826_);
leanh::lean_dec_ref(v_arg_1817_);
v_a_1884_ = leanh::lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1891_ = (!leanh::lean_is_exclusive(v___x_1851_)) as u8;
if v_isSharedCheck_1891_ == 0 {
v___x_1886_ = v___x_1851_;
v_isShared_1887_ = v_isSharedCheck_1891_;
state = 9; continue;
} else {
leanh::lean_inc(v_a_1884_);
leanh::lean_dec(v___x_1851_);
v___x_1886_ = leanh::lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
state = 9; continue;
}
}
                                                                                }
                                                                            } else {
                                                                                leanh::lean_dec_ref(v___x_1838_);
                                                                                v___x_1892_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_1829_, v_a_1801_);
                                                                                if leanh::lean_obj_tag(v___x_1892_) == 0 {
v_a_1893_ = leanh::lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1924_ = (!leanh::lean_is_exclusive(v___x_1892_)) as u8;
if v_isSharedCheck_1924_ == 0 {
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1924_;
state = 11; continue;
} else {
leanh::lean_inc(v_a_1893_);
leanh::lean_dec(v___x_1892_);
v___x_1895_ = leanh::lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1924_;
state = 11; continue;
}
} else {
leanh::lean_dec_ref(v_arg_1826_);
leanh::lean_dec_ref(v_arg_1817_);
v_a_1925_ = leanh::lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1932_ = (!leanh::lean_is_exclusive(v___x_1892_)) as u8;
if v_isSharedCheck_1932_ == 0 {
v___x_1927_ = v___x_1892_;
v_isShared_1928_ = v_isSharedCheck_1932_;
state = 17; continue;
} else {
leanh::lean_inc(v_a_1925_);
leanh::lean_dec(v___x_1892_);
v___x_1927_ = leanh::lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
state = 17; continue;
}
}
                                                                            }
                                                                        } else {
                                                                            leanh::lean_dec_ref(v___x_1838_);
                                                                            v___x_1933_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_1829_, v_a_1801_);
                                                                            if leanh::lean_obj_tag(v___x_1933_) == 0 {
v_a_1934_ = leanh::lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1965_ = (!leanh::lean_is_exclusive(v___x_1933_)) as u8;
if v_isSharedCheck_1965_ == 0 {
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1965_;
state = 19; continue;
} else {
leanh::lean_inc(v_a_1934_);
leanh::lean_dec(v___x_1933_);
v___x_1936_ = leanh::lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1965_;
state = 19; continue;
}
} else {
leanh::lean_dec_ref(v_arg_1826_);
leanh::lean_dec_ref(v_arg_1817_);
v_a_1966_ = leanh::lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1973_ = (!leanh::lean_is_exclusive(v___x_1933_)) as u8;
if v_isSharedCheck_1973_ == 0 {
v___x_1968_ = v___x_1933_;
v_isShared_1969_ = v_isSharedCheck_1973_;
state = 25; continue;
} else {
leanh::lean_inc(v_a_1966_);
leanh::lean_dec(v___x_1933_);
v___x_1968_ = leanh::lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
state = 25; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v___x_1838_,
                                                                        );
                                                                        v___x_1974_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_1829_, v_a_1801_);
                                                                        if leanh::lean_obj_tag(v___x_1974_) == 0 {
v_a_1975_ = leanh::lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2006_ = (!leanh::lean_is_exclusive(v___x_1974_)) as u8;
if v_isSharedCheck_2006_ == 0 {
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2006_;
state = 27; continue;
} else {
leanh::lean_inc(v_a_1975_);
leanh::lean_dec(v___x_1974_);
v___x_1977_ = leanh::lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2006_;
state = 27; continue;
}
} else {
leanh::lean_dec_ref(v_arg_1826_);
leanh::lean_dec_ref(v_arg_1817_);
v_a_2007_ = leanh::lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2014_ = (!leanh::lean_is_exclusive(v___x_1974_)) as u8;
if v_isSharedCheck_2014_ == 0 {
v___x_2009_ = v___x_1974_;
v_isShared_2010_ = v_isSharedCheck_2014_;
state = 33; continue;
} else {
leanh::lean_inc(v_a_2007_);
leanh::lean_dec(v___x_1974_);
v___x_2009_ = leanh::lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
state = 33; continue;
}
}
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v___x_1838_,
                                                                    );
                                                                    v___x_2015_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_1829_, v_a_1801_);
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_2015_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_2016_ = leanh::lean_ctor_get(v___x_2015_, 0);
                                                                        v_isSharedCheck_2047_ = (!leanh::lean_is_exclusive(v___x_2015_)) as u8;
                                                                        if v_isSharedCheck_2047_
                                                                            == 0
                                                                        {
                                                                            v___x_2018_ =
                                                                                v___x_2015_;
                                                                            v_isShared_2019_ = v_isSharedCheck_2047_;
                                                                            state = 35;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_2016_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_2015_,
                                                                            );
                                                                            v___x_2018_ = leanh::lean_box(0);
                                                                            v_isShared_2019_ = v_isSharedCheck_2047_;
                                                                            state = 35;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_1826_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_1817_,
                                                                        );
                                                                        v_a_2048_ = leanh::lean_ctor_get(v___x_2015_, 0);
                                                                        v_isSharedCheck_2055_ = (!leanh::lean_is_exclusive(v___x_2015_)) as u8;
                                                                        if v_isSharedCheck_2055_
                                                                            == 0
                                                                        {
                                                                            v___x_2050_ =
                                                                                v___x_2015_;
                                                                            v_isShared_2051_ = v_isSharedCheck_2055_;
                                                                            state = 41;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_2048_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_2015_,
                                                                            );
                                                                            v___x_2050_ = leanh::lean_box(0);
                                                                            v_isShared_2051_ = v_isSharedCheck_2055_;
                                                                            state = 41;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_1838_,
                                                                );
                                                                v___x_2056_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_1829_, v_a_1801_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_2056_,
                                                                ) == 0
                                                                {
                                                                    v_a_2057_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_2056_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_2106_ = (!leanh::lean_is_exclusive(v___x_2056_)) as u8;
                                                                    if v_isSharedCheck_2106_ == 0 {
                                                                        v___x_2059_ = v___x_2056_;
                                                                        v_isShared_2060_ =
                                                                            v_isSharedCheck_2106_;
                                                                        state = 43;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_2057_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_2056_,
                                                                        );
                                                                        v___x_2059_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_2060_ =
                                                                            v_isSharedCheck_2106_;
                                                                        state = 43;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_1826_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_1817_,
                                                                    );
                                                                    v_a_2107_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_2056_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_2114_ = (!leanh::lean_is_exclusive(v___x_2056_)) as u8;
                                                                    if v_isSharedCheck_2114_ == 0 {
                                                                        v___x_2109_ = v___x_2056_;
                                                                        v_isShared_2110_ =
                                                                            v_isSharedCheck_2114_;
                                                                        state = 53;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_2107_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_2056_,
                                                                        );
                                                                        v___x_2109_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_2110_ =
                                                                            v_isSharedCheck_2114_;
                                                                        state = 53;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_1830_);
                                                leanh::lean_dec_ref(v_arg_1829_);
                                                leanh::lean_dec_ref(v_arg_1826_);
                                                leanh::lean_dec_ref(v_arg_1817_);
                                                v___x_2115_ = l_Lean_Meta_getNatValue_x3f(
                                                    v_e_1794_, v_a_1800_, v_a_1801_, v_a_1802_,
                                                    v_a_1803_,
                                                );
                                                leanh::lean_dec_ref(v_e_1794_);
                                                if leanh::lean_obj_tag(v___x_2115_) == 0 {
                                                    v_a_2116_ =
                                                        leanh::lean_ctor_get(v___x_2115_, 0);
                                                    leanh::lean_inc(v_a_2116_);
                                                    if leanh::lean_obj_tag(v_a_2116_) == 1 {
                                                        leanh::lean_dec_ref_known(
                                                            v_a_2116_, 1,
                                                        );
                                                        return v___x_2115_;
                                                    } else {
                                                        leanh::lean_dec(v_a_2116_);
                                                        v_isSharedCheck_2124_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_2115_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2124_ == 0 {
                                                            v_unused_2125_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_2115_,
                                                                    0,
                                                                );
                                                            leanh::lean_dec(v_unused_2125_);
                                                            v___x_2118_ = v___x_2115_;
                                                            v_isShared_2119_ =
                                                                v_isSharedCheck_2124_;
                                                            state = 55;
                                                            continue;
                                                        } else {
                                                            leanh::lean_dec(v___x_2115_);
                                                            v___x_2118_ = leanh::lean_box(0);
                                                            v_isShared_2119_ =
                                                                v_isSharedCheck_2124_;
                                                            state = 55;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    return v___x_2115_;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_1818_);
                                    leanh::lean_dec_ref(v_e_1794_);
                                    v___x_2126_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                                    if leanh::lean_obj_tag(v___x_2126_) == 0 {
                                        v_a_2127_ = leanh::lean_ctor_get(v___x_2126_, 0);
                                        leanh::lean_inc(v_a_2127_);
                                        if leanh::lean_obj_tag(v_a_2127_) == 0 {
                                            return v___x_2126_;
                                        } else {
                                            v_isSharedCheck_2144_ =
                                                (!leanh::lean_is_exclusive(v___x_2126_))
                                                    as u8;
                                            if v_isSharedCheck_2144_ == 0 {
                                                v_unused_2145_ =
                                                    leanh::lean_ctor_get(v___x_2126_, 0);
                                                leanh::lean_dec(v_unused_2145_);
                                                v___x_2129_ = v___x_2126_;
                                                v_isShared_2130_ = v_isSharedCheck_2144_;
                                                state = 57;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v___x_2126_);
                                                v___x_2129_ = leanh::lean_box(0);
                                                v_isShared_2130_ = v_isSharedCheck_2144_;
                                                state = 57;
                                                continue;
                                            }
                                        }
                                    } else {
                                        return v___x_2126_;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1818_);
                                leanh::lean_dec_ref(v_e_1794_);
                                v___x_2146_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                                if leanh::lean_obj_tag(v___x_2146_) == 0 {
                                    v_a_2147_ = leanh::lean_ctor_get(v___x_2146_, 0);
                                    v_isSharedCheck_2167_ =
                                        (!leanh::lean_is_exclusive(v___x_2146_)) as u8;
                                    if v_isSharedCheck_2167_ == 0 {
                                        v___x_2149_ = v___x_2146_;
                                        v_isShared_2150_ = v_isSharedCheck_2167_;
                                        state = 61;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2147_);
                                        leanh::lean_dec(v___x_2146_);
                                        v___x_2149_ = leanh::lean_box(0);
                                        v_isShared_2150_ = v_isSharedCheck_2167_;
                                        state = 61;
                                        continue;
                                    }
                                } else {
                                    v_a_2168_ = leanh::lean_ctor_get(v___x_2146_, 0);
                                    v_isSharedCheck_2175_ =
                                        (!leanh::lean_is_exclusive(v___x_2146_)) as u8;
                                    if v_isSharedCheck_2175_ == 0 {
                                        v___x_2170_ = v___x_2146_;
                                        v_isShared_2171_ = v_isSharedCheck_2175_;
                                        state = 66;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2168_);
                                        leanh::lean_dec(v___x_2146_);
                                        v___x_2170_ = leanh::lean_box(0);
                                        v_isShared_2171_ = v_isSharedCheck_2175_;
                                        state = 66;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1818_);
                            leanh::lean_dec_ref(v_e_1794_);
                            v___x_2176_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if leanh::lean_obj_tag(v___x_2176_) == 0 {
                                v_a_2177_ = leanh::lean_ctor_get(v___x_2176_, 0);
                                v_isSharedCheck_2197_ =
                                    (!leanh::lean_is_exclusive(v___x_2176_)) as u8;
                                if v_isSharedCheck_2197_ == 0 {
                                    v___x_2179_ = v___x_2176_;
                                    v_isShared_2180_ = v_isSharedCheck_2197_;
                                    state = 68;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2177_);
                                    leanh::lean_dec(v___x_2176_);
                                    v___x_2179_ = leanh::lean_box(0);
                                    v_isShared_2180_ = v_isSharedCheck_2197_;
                                    state = 68;
                                    continue;
                                }
                            } else {
                                v_a_2198_ = leanh::lean_ctor_get(v___x_2176_, 0);
                                v_isSharedCheck_2205_ =
                                    (!leanh::lean_is_exclusive(v___x_2176_)) as u8;
                                if v_isSharedCheck_2205_ == 0 {
                                    v___x_2200_ = v___x_2176_;
                                    v_isShared_2201_ = v_isSharedCheck_2205_;
                                    state = 73;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2198_);
                                    leanh::lean_dec(v___x_2176_);
                                    v___x_2200_ = leanh::lean_box(0);
                                    v_isShared_2201_ = v_isSharedCheck_2205_;
                                    state = 73;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1813_);
                    leanh::lean_dec_ref(v_e_1794_);
                    v___x_2206_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31;
                    if v_isShared_1812_ == 0 {
                        leanh::lean_ctor_set(v___x_1811_, 0, v___x_2206_);
                        v___x_2208_ = v___x_1811_;
                        state = 75;
                        continue;
                    } else {
                        v_reuseFailAlloc_2209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
                        v___x_2208_ = v_reuseFailAlloc_2209_;
                        state = 75;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1856_ = (leanh::lean_unbox(v_a_1852_) as u8);
                leanh::lean_dec(v_a_1852_);
                if v___x_1856_ == 0 {
                    leanh::lean_dec_ref(v_arg_1826_);
                    leanh::lean_dec_ref(v_arg_1817_);
                    v___x_1857_ = leanh::lean_box(0);
                    if v_isShared_1855_ == 0 {
                        leanh::lean_ctor_set(v___x_1854_, 0, v___x_1857_);
                        v___x_1859_ = v___x_1854_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
                        v___x_1859_ = v_reuseFailAlloc_1860_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1854_);
                    v___x_1861_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if leanh::lean_obj_tag(v___x_1861_) == 0 {
                        v_a_1862_ = leanh::lean_ctor_get(v___x_1861_, 0);
                        leanh::lean_inc(v_a_1862_);
                        if leanh::lean_obj_tag(v_a_1862_) == 0 {
                            leanh::lean_dec_ref(v_arg_1817_);
                            return v___x_1861_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1861_, 1);
                            v_val_1863_ = leanh::lean_ctor_get(v_a_1862_, 0);
                            leanh::lean_inc(v_val_1863_);
                            leanh::lean_dec_ref_known(v_a_1862_, 1);
                            v___x_1864_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if leanh::lean_obj_tag(v___x_1864_) == 0 {
                                v_a_1865_ = leanh::lean_ctor_get(v___x_1864_, 0);
                                leanh::lean_inc(v_a_1865_);
                                if leanh::lean_obj_tag(v_a_1865_) == 0 {
                                    leanh::lean_dec(v_val_1863_);
                                    return v___x_1864_;
                                } else {
                                    v_isSharedCheck_1881_ =
                                        (!leanh::lean_is_exclusive(v___x_1864_)) as u8;
                                    if v_isSharedCheck_1881_ == 0 {
                                        v_unused_1882_ =
                                            leanh::lean_ctor_get(v___x_1864_, 0);
                                        leanh::lean_dec(v_unused_1882_);
                                        v___x_1867_ = v___x_1864_;
                                        v_isShared_1868_ = v_isSharedCheck_1881_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1864_);
                                        v___x_1867_ = leanh::lean_box(0);
                                        v_isShared_1868_ = v_isSharedCheck_1881_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1863_);
                                return v___x_1864_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1817_);
                        return v___x_1861_;
                    }
                }
            }
            4 => {
                return v___x_1859_;
            }
            5 => {
                v_val_1869_ = leanh::lean_ctor_get(v_a_1865_, 0);
                v_isSharedCheck_1880_ = (!leanh::lean_is_exclusive(v_a_1865_)) as u8;
                if v_isSharedCheck_1880_ == 0 {
                    v___x_1871_ = v_a_1865_;
                    v_isShared_1872_ = v_isSharedCheck_1880_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1869_);
                    leanh::lean_dec(v_a_1865_);
                    v___x_1871_ = leanh::lean_box(0);
                    v_isShared_1872_ = v_isSharedCheck_1880_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1873_ = lean_nat_add(v_val_1863_, v_val_1869_);
                leanh::lean_dec(v_val_1869_);
                leanh::lean_dec(v_val_1863_);
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_1873_);
                    v___x_1875_ = v___x_1871_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1879_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1873_);
                    v___x_1875_ = v_reuseFailAlloc_1879_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1868_ == 0 {
                    leanh::lean_ctor_set(v___x_1867_, 0, v___x_1875_);
                    v___x_1877_ = v___x_1867_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1878_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
                    v___x_1877_ = v_reuseFailAlloc_1878_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1877_;
            }
            9 => {
                if v_isShared_1887_ == 0 {
                    v___x_1889_ = v___x_1886_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
                    v___x_1889_ = v_reuseFailAlloc_1890_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1889_;
            }
            11 => {
                v___x_1897_ = (leanh::lean_unbox(v_a_1893_) as u8);
                leanh::lean_dec(v_a_1893_);
                if v___x_1897_ == 0 {
                    leanh::lean_dec_ref(v_arg_1826_);
                    leanh::lean_dec_ref(v_arg_1817_);
                    v___x_1898_ = leanh::lean_box(0);
                    if v_isShared_1896_ == 0 {
                        leanh::lean_ctor_set(v___x_1895_, 0, v___x_1898_);
                        v___x_1900_ = v___x_1895_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1901_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
                        v___x_1900_ = v_reuseFailAlloc_1901_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1895_);
                    v___x_1902_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if leanh::lean_obj_tag(v___x_1902_) == 0 {
                        v_a_1903_ = leanh::lean_ctor_get(v___x_1902_, 0);
                        leanh::lean_inc(v_a_1903_);
                        if leanh::lean_obj_tag(v_a_1903_) == 0 {
                            leanh::lean_dec_ref(v_arg_1817_);
                            return v___x_1902_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1902_, 1);
                            v_val_1904_ = leanh::lean_ctor_get(v_a_1903_, 0);
                            leanh::lean_inc(v_val_1904_);
                            leanh::lean_dec_ref_known(v_a_1903_, 1);
                            v___x_1905_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if leanh::lean_obj_tag(v___x_1905_) == 0 {
                                v_a_1906_ = leanh::lean_ctor_get(v___x_1905_, 0);
                                leanh::lean_inc(v_a_1906_);
                                if leanh::lean_obj_tag(v_a_1906_) == 0 {
                                    leanh::lean_dec(v_val_1904_);
                                    return v___x_1905_;
                                } else {
                                    v_isSharedCheck_1922_ =
                                        (!leanh::lean_is_exclusive(v___x_1905_)) as u8;
                                    if v_isSharedCheck_1922_ == 0 {
                                        v_unused_1923_ =
                                            leanh::lean_ctor_get(v___x_1905_, 0);
                                        leanh::lean_dec(v_unused_1923_);
                                        v___x_1908_ = v___x_1905_;
                                        v_isShared_1909_ = v_isSharedCheck_1922_;
                                        state = 13;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1905_);
                                        v___x_1908_ = leanh::lean_box(0);
                                        v_isShared_1909_ = v_isSharedCheck_1922_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1904_);
                                return v___x_1905_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1817_);
                        return v___x_1902_;
                    }
                }
            }
            12 => {
                return v___x_1900_;
            }
            13 => {
                v_val_1910_ = leanh::lean_ctor_get(v_a_1906_, 0);
                v_isSharedCheck_1921_ = (!leanh::lean_is_exclusive(v_a_1906_)) as u8;
                if v_isSharedCheck_1921_ == 0 {
                    v___x_1912_ = v_a_1906_;
                    v_isShared_1913_ = v_isSharedCheck_1921_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1910_);
                    leanh::lean_dec(v_a_1906_);
                    v___x_1912_ = leanh::lean_box(0);
                    v_isShared_1913_ = v_isSharedCheck_1921_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1914_ = lean_nat_mul(v_val_1904_, v_val_1910_);
                leanh::lean_dec(v_val_1910_);
                leanh::lean_dec(v_val_1904_);
                if v_isShared_1913_ == 0 {
                    leanh::lean_ctor_set(v___x_1912_, 0, v___x_1914_);
                    v___x_1916_ = v___x_1912_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1914_);
                    v___x_1916_ = v_reuseFailAlloc_1920_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1909_ == 0 {
                    leanh::lean_ctor_set(v___x_1908_, 0, v___x_1916_);
                    v___x_1918_ = v___x_1908_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
                    v___x_1918_ = v_reuseFailAlloc_1919_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1918_;
            }
            17 => {
                if v_isShared_1928_ == 0 {
                    v___x_1930_ = v___x_1927_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
                    v___x_1930_ = v_reuseFailAlloc_1931_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1930_;
            }
            19 => {
                v___x_1938_ = (leanh::lean_unbox(v_a_1934_) as u8);
                leanh::lean_dec(v_a_1934_);
                if v___x_1938_ == 0 {
                    leanh::lean_dec_ref(v_arg_1826_);
                    leanh::lean_dec_ref(v_arg_1817_);
                    v___x_1939_ = leanh::lean_box(0);
                    if v_isShared_1937_ == 0 {
                        leanh::lean_ctor_set(v___x_1936_, 0, v___x_1939_);
                        v___x_1941_ = v___x_1936_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1942_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
                        v___x_1941_ = v_reuseFailAlloc_1942_;
                        state = 20;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1936_);
                    v___x_1943_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if leanh::lean_obj_tag(v___x_1943_) == 0 {
                        v_a_1944_ = leanh::lean_ctor_get(v___x_1943_, 0);
                        leanh::lean_inc(v_a_1944_);
                        if leanh::lean_obj_tag(v_a_1944_) == 0 {
                            leanh::lean_dec_ref(v_arg_1817_);
                            return v___x_1943_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1943_, 1);
                            v_val_1945_ = leanh::lean_ctor_get(v_a_1944_, 0);
                            leanh::lean_inc(v_val_1945_);
                            leanh::lean_dec_ref_known(v_a_1944_, 1);
                            v___x_1946_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if leanh::lean_obj_tag(v___x_1946_) == 0 {
                                v_a_1947_ = leanh::lean_ctor_get(v___x_1946_, 0);
                                leanh::lean_inc(v_a_1947_);
                                if leanh::lean_obj_tag(v_a_1947_) == 0 {
                                    leanh::lean_dec(v_val_1945_);
                                    return v___x_1946_;
                                } else {
                                    v_isSharedCheck_1963_ =
                                        (!leanh::lean_is_exclusive(v___x_1946_)) as u8;
                                    if v_isSharedCheck_1963_ == 0 {
                                        v_unused_1964_ =
                                            leanh::lean_ctor_get(v___x_1946_, 0);
                                        leanh::lean_dec(v_unused_1964_);
                                        v___x_1949_ = v___x_1946_;
                                        v_isShared_1950_ = v_isSharedCheck_1963_;
                                        state = 21;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1946_);
                                        v___x_1949_ = leanh::lean_box(0);
                                        v_isShared_1950_ = v_isSharedCheck_1963_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1945_);
                                return v___x_1946_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1817_);
                        return v___x_1943_;
                    }
                }
            }
            20 => {
                return v___x_1941_;
            }
            21 => {
                v_val_1951_ = leanh::lean_ctor_get(v_a_1947_, 0);
                v_isSharedCheck_1962_ = (!leanh::lean_is_exclusive(v_a_1947_)) as u8;
                if v_isSharedCheck_1962_ == 0 {
                    v___x_1953_ = v_a_1947_;
                    v_isShared_1954_ = v_isSharedCheck_1962_;
                    state = 22;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1951_);
                    leanh::lean_dec(v_a_1947_);
                    v___x_1953_ = leanh::lean_box(0);
                    v_isShared_1954_ = v_isSharedCheck_1962_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1955_ = lean_nat_sub(v_val_1945_, v_val_1951_);
                leanh::lean_dec(v_val_1951_);
                leanh::lean_dec(v_val_1945_);
                if v_isShared_1954_ == 0 {
                    leanh::lean_ctor_set(v___x_1953_, 0, v___x_1955_);
                    v___x_1957_ = v___x_1953_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1961_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1955_);
                    v___x_1957_ = v_reuseFailAlloc_1961_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1950_ == 0 {
                    leanh::lean_ctor_set(v___x_1949_, 0, v___x_1957_);
                    v___x_1959_ = v___x_1949_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1960_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
                    v___x_1959_ = v_reuseFailAlloc_1960_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1959_;
            }
            25 => {
                if v_isShared_1969_ == 0 {
                    v___x_1971_ = v___x_1968_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1971_;
            }
            27 => {
                v___x_1979_ = (leanh::lean_unbox(v_a_1975_) as u8);
                leanh::lean_dec(v_a_1975_);
                if v___x_1979_ == 0 {
                    leanh::lean_dec_ref(v_arg_1826_);
                    leanh::lean_dec_ref(v_arg_1817_);
                    v___x_1980_ = leanh::lean_box(0);
                    if v_isShared_1978_ == 0 {
                        leanh::lean_ctor_set(v___x_1977_, 0, v___x_1980_);
                        v___x_1982_ = v___x_1977_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_1983_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
                        v___x_1982_ = v_reuseFailAlloc_1983_;
                        state = 28;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1977_);
                    v___x_1984_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if leanh::lean_obj_tag(v___x_1984_) == 0 {
                        v_a_1985_ = leanh::lean_ctor_get(v___x_1984_, 0);
                        leanh::lean_inc(v_a_1985_);
                        if leanh::lean_obj_tag(v_a_1985_) == 0 {
                            leanh::lean_dec_ref(v_arg_1817_);
                            return v___x_1984_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1984_, 1);
                            v_val_1986_ = leanh::lean_ctor_get(v_a_1985_, 0);
                            leanh::lean_inc(v_val_1986_);
                            leanh::lean_dec_ref_known(v_a_1985_, 1);
                            v___x_1987_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if leanh::lean_obj_tag(v___x_1987_) == 0 {
                                v_a_1988_ = leanh::lean_ctor_get(v___x_1987_, 0);
                                leanh::lean_inc(v_a_1988_);
                                if leanh::lean_obj_tag(v_a_1988_) == 0 {
                                    leanh::lean_dec(v_val_1986_);
                                    return v___x_1987_;
                                } else {
                                    v_isSharedCheck_2004_ =
                                        (!leanh::lean_is_exclusive(v___x_1987_)) as u8;
                                    if v_isSharedCheck_2004_ == 0 {
                                        v_unused_2005_ =
                                            leanh::lean_ctor_get(v___x_1987_, 0);
                                        leanh::lean_dec(v_unused_2005_);
                                        v___x_1990_ = v___x_1987_;
                                        v_isShared_1991_ = v_isSharedCheck_2004_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1987_);
                                        v___x_1990_ = leanh::lean_box(0);
                                        v_isShared_1991_ = v_isSharedCheck_2004_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_1986_);
                                return v___x_1987_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1817_);
                        return v___x_1984_;
                    }
                }
            }
            28 => {
                return v___x_1982_;
            }
            29 => {
                v_val_1992_ = leanh::lean_ctor_get(v_a_1988_, 0);
                v_isSharedCheck_2003_ = (!leanh::lean_is_exclusive(v_a_1988_)) as u8;
                if v_isSharedCheck_2003_ == 0 {
                    v___x_1994_ = v_a_1988_;
                    v_isShared_1995_ = v_isSharedCheck_2003_;
                    state = 30;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1992_);
                    leanh::lean_dec(v_a_1988_);
                    v___x_1994_ = leanh::lean_box(0);
                    v_isShared_1995_ = v_isSharedCheck_2003_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1996_ = lean_nat_div(v_val_1986_, v_val_1992_);
                leanh::lean_dec(v_val_1992_);
                leanh::lean_dec(v_val_1986_);
                if v_isShared_1995_ == 0 {
                    leanh::lean_ctor_set(v___x_1994_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1994_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1996_);
                    v___x_1998_ = v_reuseFailAlloc_2002_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_1991_ == 0 {
                    leanh::lean_ctor_set(v___x_1990_, 0, v___x_1998_);
                    v___x_2000_ = v___x_1990_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
                    v___x_2000_ = v_reuseFailAlloc_2001_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_2000_;
            }
            33 => {
                if v_isShared_2010_ == 0 {
                    v___x_2012_ = v___x_2009_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
                    v___x_2012_ = v_reuseFailAlloc_2013_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2012_;
            }
            35 => {
                v___x_2020_ = (leanh::lean_unbox(v_a_2016_) as u8);
                leanh::lean_dec(v_a_2016_);
                if v___x_2020_ == 0 {
                    leanh::lean_dec_ref(v_arg_1826_);
                    leanh::lean_dec_ref(v_arg_1817_);
                    v___x_2021_ = leanh::lean_box(0);
                    if v_isShared_2019_ == 0 {
                        leanh::lean_ctor_set(v___x_2018_, 0, v___x_2021_);
                        v___x_2023_ = v___x_2018_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_2024_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
                        v___x_2023_ = v_reuseFailAlloc_2024_;
                        state = 36;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2018_);
                    v___x_2025_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if leanh::lean_obj_tag(v___x_2025_) == 0 {
                        v_a_2026_ = leanh::lean_ctor_get(v___x_2025_, 0);
                        leanh::lean_inc(v_a_2026_);
                        if leanh::lean_obj_tag(v_a_2026_) == 0 {
                            leanh::lean_dec_ref(v_arg_1817_);
                            return v___x_2025_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2025_, 1);
                            v_val_2027_ = leanh::lean_ctor_get(v_a_2026_, 0);
                            leanh::lean_inc(v_val_2027_);
                            leanh::lean_dec_ref_known(v_a_2026_, 1);
                            v___x_2028_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if leanh::lean_obj_tag(v___x_2028_) == 0 {
                                v_a_2029_ = leanh::lean_ctor_get(v___x_2028_, 0);
                                leanh::lean_inc(v_a_2029_);
                                if leanh::lean_obj_tag(v_a_2029_) == 0 {
                                    leanh::lean_dec(v_val_2027_);
                                    return v___x_2028_;
                                } else {
                                    v_isSharedCheck_2045_ =
                                        (!leanh::lean_is_exclusive(v___x_2028_)) as u8;
                                    if v_isSharedCheck_2045_ == 0 {
                                        v_unused_2046_ =
                                            leanh::lean_ctor_get(v___x_2028_, 0);
                                        leanh::lean_dec(v_unused_2046_);
                                        v___x_2031_ = v___x_2028_;
                                        v_isShared_2032_ = v_isSharedCheck_2045_;
                                        state = 37;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_2028_);
                                        v___x_2031_ = leanh::lean_box(0);
                                        v_isShared_2032_ = v_isSharedCheck_2045_;
                                        state = 37;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_2027_);
                                return v___x_2028_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1817_);
                        return v___x_2025_;
                    }
                }
            }
            36 => {
                return v___x_2023_;
            }
            37 => {
                v_val_2033_ = leanh::lean_ctor_get(v_a_2029_, 0);
                v_isSharedCheck_2044_ = (!leanh::lean_is_exclusive(v_a_2029_)) as u8;
                if v_isSharedCheck_2044_ == 0 {
                    v___x_2035_ = v_a_2029_;
                    v_isShared_2036_ = v_isSharedCheck_2044_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_inc(v_val_2033_);
                    leanh::lean_dec(v_a_2029_);
                    v___x_2035_ = leanh::lean_box(0);
                    v_isShared_2036_ = v_isSharedCheck_2044_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_2037_ = lean_nat_mod(v_val_2027_, v_val_2033_);
                leanh::lean_dec(v_val_2033_);
                leanh::lean_dec(v_val_2027_);
                if v_isShared_2036_ == 0 {
                    leanh::lean_ctor_set(v___x_2035_, 0, v___x_2037_);
                    v___x_2039_ = v___x_2035_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2043_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2037_);
                    v___x_2039_ = v_reuseFailAlloc_2043_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_2032_ == 0 {
                    leanh::lean_ctor_set(v___x_2031_, 0, v___x_2039_);
                    v___x_2041_ = v___x_2031_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
                    v___x_2041_ = v_reuseFailAlloc_2042_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2041_;
            }
            41 => {
                if v_isShared_2051_ == 0 {
                    v___x_2053_ = v___x_2050_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
                    v___x_2053_ = v_reuseFailAlloc_2054_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2053_;
            }
            43 => {
                v___x_2061_ = (leanh::lean_unbox(v_a_2057_) as u8);
                leanh::lean_dec(v_a_2057_);
                if v___x_2061_ == 0 {
                    leanh::lean_dec_ref(v_arg_1826_);
                    leanh::lean_dec_ref(v_arg_1817_);
                    v___x_2062_ = leanh::lean_box(0);
                    if v_isShared_2060_ == 0 {
                        leanh::lean_ctor_set(v___x_2059_, 0, v___x_2062_);
                        v___x_2064_ = v___x_2059_;
                        state = 44;
                        continue;
                    } else {
                        v_reuseFailAlloc_2065_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
                        v___x_2064_ = v_reuseFailAlloc_2065_;
                        state = 44;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2059_);
                    v___x_2066_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if leanh::lean_obj_tag(v___x_2066_) == 0 {
                        v_a_2067_ = leanh::lean_ctor_get(v___x_2066_, 0);
                        leanh::lean_inc(v_a_2067_);
                        if leanh::lean_obj_tag(v_a_2067_) == 0 {
                            leanh::lean_dec_ref(v_arg_1826_);
                            return v___x_2066_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2066_, 1);
                            v_val_2068_ = leanh::lean_ctor_get(v_a_2067_, 0);
                            leanh::lean_inc_n(v_val_2068_, 2);
                            leanh::lean_dec_ref_known(v_a_2067_, 1);
                            v___x_2069_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(
                                v_val_2068_,
                                v_a_1796_,
                                v_a_1798_,
                                v_a_1799_,
                                v_a_1800_,
                                v_a_1801_,
                                v_a_1802_,
                                v_a_1803_,
                            );
                            if leanh::lean_obj_tag(v___x_2069_) == 0 {
                                v_a_2070_ = leanh::lean_ctor_get(v___x_2069_, 0);
                                v_isSharedCheck_2097_ =
                                    (!leanh::lean_is_exclusive(v___x_2069_)) as u8;
                                if v_isSharedCheck_2097_ == 0 {
                                    v___x_2072_ = v___x_2069_;
                                    v_isShared_2073_ = v_isSharedCheck_2097_;
                                    state = 45;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2070_);
                                    leanh::lean_dec(v___x_2069_);
                                    v___x_2072_ = leanh::lean_box(0);
                                    v_isShared_2073_ = v_isSharedCheck_2097_;
                                    state = 45;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_2068_);
                                leanh::lean_dec_ref(v_arg_1826_);
                                v_a_2098_ = leanh::lean_ctor_get(v___x_2069_, 0);
                                v_isSharedCheck_2105_ =
                                    (!leanh::lean_is_exclusive(v___x_2069_)) as u8;
                                if v_isSharedCheck_2105_ == 0 {
                                    v___x_2100_ = v___x_2069_;
                                    v_isShared_2101_ = v_isSharedCheck_2105_;
                                    state = 51;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2098_);
                                    leanh::lean_dec(v___x_2069_);
                                    v___x_2100_ = leanh::lean_box(0);
                                    v_isShared_2101_ = v_isSharedCheck_2105_;
                                    state = 51;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_1826_);
                        return v___x_2066_;
                    }
                }
            }
            44 => {
                return v___x_2064_;
            }
            45 => {
                if leanh::lean_obj_tag(v_a_2070_) == 0 {
                    leanh::lean_dec(v_val_2068_);
                    leanh::lean_dec_ref(v_arg_1826_);
                    v___x_2074_ = leanh::lean_box(0);
                    if v_isShared_2073_ == 0 {
                        leanh::lean_ctor_set(v___x_2072_, 0, v___x_2074_);
                        v___x_2076_ = v___x_2072_;
                        state = 46;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 46;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_2070_, 1);
                    leanh::lean_del_object(v___x_2072_);
                    v___x_2078_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if leanh::lean_obj_tag(v___x_2078_) == 0 {
                        v_a_2079_ = leanh::lean_ctor_get(v___x_2078_, 0);
                        leanh::lean_inc(v_a_2079_);
                        if leanh::lean_obj_tag(v_a_2079_) == 0 {
                            leanh::lean_dec(v_val_2068_);
                            return v___x_2078_;
                        } else {
                            v_isSharedCheck_2095_ =
                                (!leanh::lean_is_exclusive(v___x_2078_)) as u8;
                            if v_isSharedCheck_2095_ == 0 {
                                v_unused_2096_ = leanh::lean_ctor_get(v___x_2078_, 0);
                                leanh::lean_dec(v_unused_2096_);
                                v___x_2081_ = v___x_2078_;
                                v_isShared_2082_ = v_isSharedCheck_2095_;
                                state = 47;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2078_);
                                v___x_2081_ = leanh::lean_box(0);
                                v_isShared_2082_ = v_isSharedCheck_2095_;
                                state = 47;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_2068_);
                        return v___x_2078_;
                    }
                }
            }
            46 => {
                return v___x_2076_;
            }
            47 => {
                v_val_2083_ = leanh::lean_ctor_get(v_a_2079_, 0);
                v_isSharedCheck_2094_ = (!leanh::lean_is_exclusive(v_a_2079_)) as u8;
                if v_isSharedCheck_2094_ == 0 {
                    v___x_2085_ = v_a_2079_;
                    v_isShared_2086_ = v_isSharedCheck_2094_;
                    state = 48;
                    continue;
                } else {
                    leanh::lean_inc(v_val_2083_);
                    leanh::lean_dec(v_a_2079_);
                    v___x_2085_ = leanh::lean_box(0);
                    v_isShared_2086_ = v_isSharedCheck_2094_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                v___x_2087_ = lean_nat_pow(v_val_2083_, v_val_2068_);
                leanh::lean_dec(v_val_2068_);
                leanh::lean_dec(v_val_2083_);
                if v_isShared_2086_ == 0 {
                    leanh::lean_ctor_set(v___x_2085_, 0, v___x_2087_);
                    v___x_2089_ = v___x_2085_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2087_);
                    v___x_2089_ = v_reuseFailAlloc_2093_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_2082_ == 0 {
                    leanh::lean_ctor_set(v___x_2081_, 0, v___x_2089_);
                    v___x_2091_ = v___x_2081_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
                    v___x_2091_ = v_reuseFailAlloc_2092_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_2091_;
            }
            51 => {
                if v_isShared_2101_ == 0 {
                    v___x_2103_ = v___x_2100_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_2104_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
                    v___x_2103_ = v_reuseFailAlloc_2104_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_2103_;
            }
            53 => {
                if v_isShared_2110_ == 0 {
                    v___x_2112_ = v___x_2109_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2113_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
                    v___x_2112_ = v_reuseFailAlloc_2113_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_2112_;
            }
            55 => {
                v___x_2120_ = leanh::lean_box(0);
                if v_isShared_2119_ == 0 {
                    leanh::lean_ctor_set(v___x_2118_, 0, v___x_2120_);
                    v___x_2122_ = v___x_2118_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2123_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_2122_;
            }
            57 => {
                v_val_2131_ = leanh::lean_ctor_get(v_a_2127_, 0);
                v_isSharedCheck_2143_ = (!leanh::lean_is_exclusive(v_a_2127_)) as u8;
                if v_isSharedCheck_2143_ == 0 {
                    v___x_2133_ = v_a_2127_;
                    v_isShared_2134_ = v_isSharedCheck_2143_;
                    state = 58;
                    continue;
                } else {
                    leanh::lean_inc(v_val_2131_);
                    leanh::lean_dec(v_a_2127_);
                    v___x_2133_ = leanh::lean_box(0);
                    v_isShared_2134_ = v_isSharedCheck_2143_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_2135_ = leanh::lean_unsigned_to_nat(1);
                v___x_2136_ = lean_nat_add(v_val_2131_, v___x_2135_);
                leanh::lean_dec(v_val_2131_);
                if v_isShared_2134_ == 0 {
                    leanh::lean_ctor_set(v___x_2133_, 0, v___x_2136_);
                    v___x_2138_ = v___x_2133_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2136_);
                    v___x_2138_ = v_reuseFailAlloc_2142_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_2130_ == 0 {
                    leanh::lean_ctor_set(v___x_2129_, 0, v___x_2138_);
                    v___x_2140_ = v___x_2129_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
                    v___x_2140_ = v_reuseFailAlloc_2141_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2140_;
            }
            61 => {
                if leanh::lean_obj_tag(v_a_2147_) == 0 {
                    v___x_2151_ = leanh::lean_box(0);
                    if v_isShared_2150_ == 0 {
                        leanh::lean_ctor_set(v___x_2149_, 0, v___x_2151_);
                        v___x_2153_ = v___x_2149_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_2154_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
                        v___x_2153_ = v_reuseFailAlloc_2154_;
                        state = 62;
                        continue;
                    }
                } else {
                    v_val_2155_ = leanh::lean_ctor_get(v_a_2147_, 0);
                    v_isSharedCheck_2166_ = (!leanh::lean_is_exclusive(v_a_2147_)) as u8;
                    if v_isSharedCheck_2166_ == 0 {
                        v___x_2157_ = v_a_2147_;
                        v_isShared_2158_ = v_isSharedCheck_2166_;
                        state = 63;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2155_);
                        leanh::lean_dec(v_a_2147_);
                        v___x_2157_ = leanh::lean_box(0);
                        v_isShared_2158_ = v_isSharedCheck_2166_;
                        state = 63;
                        continue;
                    }
                }
            }
            62 => {
                return v___x_2153_;
            }
            63 => {
                v___x_2159_ = l_Int_toNat(v_val_2155_);
                leanh::lean_dec(v_val_2155_);
                if v_isShared_2158_ == 0 {
                    leanh::lean_ctor_set(v___x_2157_, 0, v___x_2159_);
                    v___x_2161_ = v___x_2157_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2159_);
                    v___x_2161_ = v_reuseFailAlloc_2165_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                if v_isShared_2150_ == 0 {
                    leanh::lean_ctor_set(v___x_2149_, 0, v___x_2161_);
                    v___x_2163_ = v___x_2149_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
                    v___x_2163_ = v_reuseFailAlloc_2164_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2163_;
            }
            66 => {
                if v_isShared_2171_ == 0 {
                    v___x_2173_ = v___x_2170_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2173_;
            }
            68 => {
                if leanh::lean_obj_tag(v_a_2177_) == 0 {
                    v___x_2181_ = leanh::lean_box(0);
                    if v_isShared_2180_ == 0 {
                        leanh::lean_ctor_set(v___x_2179_, 0, v___x_2181_);
                        v___x_2183_ = v___x_2179_;
                        state = 69;
                        continue;
                    } else {
                        v_reuseFailAlloc_2184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
                        v___x_2183_ = v_reuseFailAlloc_2184_;
                        state = 69;
                        continue;
                    }
                } else {
                    v_val_2185_ = leanh::lean_ctor_get(v_a_2177_, 0);
                    v_isSharedCheck_2196_ = (!leanh::lean_is_exclusive(v_a_2177_)) as u8;
                    if v_isSharedCheck_2196_ == 0 {
                        v___x_2187_ = v_a_2177_;
                        v_isShared_2188_ = v_isSharedCheck_2196_;
                        state = 70;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2185_);
                        leanh::lean_dec(v_a_2177_);
                        v___x_2187_ = leanh::lean_box(0);
                        v_isShared_2188_ = v_isSharedCheck_2196_;
                        state = 70;
                        continue;
                    }
                }
            }
            69 => {
                return v___x_2183_;
            }
            70 => {
                v___x_2189_ = lean_nat_abs(v_val_2185_);
                leanh::lean_dec(v_val_2185_);
                if v_isShared_2188_ == 0 {
                    leanh::lean_ctor_set(v___x_2187_, 0, v___x_2189_);
                    v___x_2191_ = v___x_2187_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
                    v___x_2191_ = v_reuseFailAlloc_2195_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_2180_ == 0 {
                    leanh::lean_ctor_set(v___x_2179_, 0, v___x_2191_);
                    v___x_2193_ = v___x_2179_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_2194_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
                    v___x_2193_ = v_reuseFailAlloc_2194_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_2193_;
            }
            73 => {
                if v_isShared_2201_ == 0 {
                    v___x_2203_ = v___x_2200_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_2204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
                    v___x_2203_ = v_reuseFailAlloc_2204_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_2203_;
            }
            75 => {
                return v___x_2208_;
            }
            76 => {
                if v_isShared_2214_ == 0 {
                    v___x_2216_ = v___x_2213_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_2217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
                    v___x_2216_ = v_reuseFailAlloc_2217_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_2216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(
    mut v_e_2219_: *mut leanh::LeanObject,
    mut v_a_2220_: *mut leanh::LeanObject,
    mut v_a_2221_: *mut leanh::LeanObject,
    mut v_a_2222_: *mut leanh::LeanObject,
    mut v_a_2223_: *mut leanh::LeanObject,
    mut v_a_2224_: *mut leanh::LeanObject,
    mut v_a_2225_: *mut leanh::LeanObject,
    mut v_a_2226_: *mut leanh::LeanObject,
    mut v_a_2227_: *mut leanh::LeanObject,
    mut v_a_2228_: *mut leanh::LeanObject,
    mut v_a_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(
            v_e_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_,
            v_a_2227_, v_a_2228_,
        );
    leanh::lean_dec(v_a_2228_);
    leanh::lean_dec_ref(v_a_2227_);
    leanh::lean_dec(v_a_2226_);
    leanh::lean_dec_ref(v_a_2225_);
    leanh::lean_dec(v_a_2224_);
    leanh::lean_dec_ref(v_a_2223_);
    leanh::lean_dec(v_a_2222_);
    leanh::lean_dec_ref(v_a_2221_);
    leanh::lean_dec(v_a_2220_);
    return v_res_2230_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(
    mut v_e_2231_: *mut leanh::LeanObject,
    mut v_a_2232_: *mut leanh::LeanObject,
    mut v_a_2233_: *mut leanh::LeanObject,
    mut v_a_2234_: *mut leanh::LeanObject,
    mut v_a_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
    mut v_a_2237_: *mut leanh::LeanObject,
    mut v_a_2238_: *mut leanh::LeanObject,
    mut v_a_2239_: *mut leanh::LeanObject,
    mut v_a_2240_: *mut leanh::LeanObject,
    mut v_a_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2242_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(
            v_e_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_,
            v_a_2239_, v_a_2240_,
        );
    leanh::lean_dec(v_a_2240_);
    leanh::lean_dec_ref(v_a_2239_);
    leanh::lean_dec(v_a_2238_);
    leanh::lean_dec_ref(v_a_2237_);
    leanh::lean_dec(v_a_2236_);
    leanh::lean_dec_ref(v_a_2235_);
    leanh::lean_dec(v_a_2234_);
    leanh::lean_dec_ref(v_a_2233_);
    leanh::lean_dec(v_a_2232_);
    return v_res_2242_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(
    mut v_a_2243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2244_ = lean_nat_to_int(v_a_2243_);
    return v___x_2244_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalNat_x3f(
    mut v_e_2245_: *mut leanh::LeanObject,
    mut v_a_2246_: *mut leanh::LeanObject,
    mut v_a_2247_: *mut leanh::LeanObject,
    mut v_a_2248_: *mut leanh::LeanObject,
    mut v_a_2249_: *mut leanh::LeanObject,
    mut v_a_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
    mut v_a_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
    mut v_a_2254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(
            v_e_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_,
            v_a_2253_, v_a_2254_,
        );
    return v___x_2256_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(
    mut v_e_2257_: *mut leanh::LeanObject,
    mut v_a_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: *mut leanh::LeanObject,
    mut v_a_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
    mut v_a_2262_: *mut leanh::LeanObject,
    mut v_a_2263_: *mut leanh::LeanObject,
    mut v_a_2264_: *mut leanh::LeanObject,
    mut v_a_2265_: *mut leanh::LeanObject,
    mut v_a_2266_: *mut leanh::LeanObject,
    mut v_a_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(
        v_e_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_,
        v_a_2265_, v_a_2266_,
    );
    leanh::lean_dec(v_a_2266_);
    leanh::lean_dec_ref(v_a_2265_);
    leanh::lean_dec(v_a_2264_);
    leanh::lean_dec_ref(v_a_2263_);
    leanh::lean_dec(v_a_2262_);
    leanh::lean_dec_ref(v_a_2261_);
    leanh::lean_dec(v_a_2260_);
    leanh::lean_dec_ref(v_a_2259_);
    leanh::lean_dec(v_a_2258_);
    return v_res_2268_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalInt_x3f(
    mut v_e_2269_: *mut leanh::LeanObject,
    mut v_a_2270_: *mut leanh::LeanObject,
    mut v_a_2271_: *mut leanh::LeanObject,
    mut v_a_2272_: *mut leanh::LeanObject,
    mut v_a_2273_: *mut leanh::LeanObject,
    mut v_a_2274_: *mut leanh::LeanObject,
    mut v_a_2275_: *mut leanh::LeanObject,
    mut v_a_2276_: *mut leanh::LeanObject,
    mut v_a_2277_: *mut leanh::LeanObject,
    mut v_a_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(
            v_e_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_,
            v_a_2277_, v_a_2278_,
        );
    return v___x_2280_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(
    mut v_e_2281_: *mut leanh::LeanObject,
    mut v_a_2282_: *mut leanh::LeanObject,
    mut v_a_2283_: *mut leanh::LeanObject,
    mut v_a_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: *mut leanh::LeanObject,
    mut v_a_2286_: *mut leanh::LeanObject,
    mut v_a_2287_: *mut leanh::LeanObject,
    mut v_a_2288_: *mut leanh::LeanObject,
    mut v_a_2289_: *mut leanh::LeanObject,
    mut v_a_2290_: *mut leanh::LeanObject,
    mut v_a_2291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2292_ = l_Lean_Meta_Grind_Arith_evalInt_x3f(
        v_e_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_,
        v_a_2289_, v_a_2290_,
    );
    leanh::lean_dec(v_a_2290_);
    leanh::lean_dec_ref(v_a_2289_);
    leanh::lean_dec(v_a_2288_);
    leanh::lean_dec_ref(v_a_2287_);
    leanh::lean_dec(v_a_2286_);
    leanh::lean_dec_ref(v_a_2285_);
    leanh::lean_dec(v_a_2284_);
    leanh::lean_dec_ref(v_a_2283_);
    leanh::lean_dec(v_a_2282_);
    return v_res_2292_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_IntInstTesters(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
}