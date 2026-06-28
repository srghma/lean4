// Lean compiler output
// Module: Lean.Meta.Sym.Arith.EvalNum
// Imports: Lean.Meta.Sym.Arith.Types Lean.Meta.Sym.LitValues Lean.Meta.IntInstTesters Lean.Meta.NatInstTesters
use crate::r#gen::Init::Data::Int::Basic::{l_Int_pow, l_Int_toNat};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
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
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_Structural_isInstHAddNat___redArg,
    l_Lean_Meta_Structural_isInstHDivNat___redArg, l_Lean_Meta_Structural_isInstHModNat___redArg,
    l_Lean_Meta_Structural_isInstHMulNat___redArg, l_Lean_Meta_Structural_isInstHPowNat___redArg,
    l_Lean_Meta_Structural_isInstHSubNat___redArg, runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::Meta::Sym::Arith::Types::{
    initialize_Lean_Meta_Sym_Arith_Types, l_Lean_Meta_Sym_Arith_getExpThreshold___redArg,
    runtime_initialize_Lean_Meta_Sym_Arith_Types,
};
use crate::r#gen::Lean::Meta::Sym::LitValues::{
    initialize_Lean_Meta_Sym_LitValues, l_Lean_Meta_Sym_getIntValue_x3f,
    l_Lean_Meta_Sym_getNatValue_x3f, runtime_initialize_Lean_Meta_Sym_LitValues,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_mul, lean_nat_pow,
    lean_nat_sub,
};
pub static l_Lean_Meta_Sym_Arith_checkExp___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
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
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_checkExp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_checkExp___closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_checkExp___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_checkExp___closed__3_value: crate::leanh::LeanStringObject<48> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 48,
        m_capacity: 48,
        m_length: 47,
        m_data: [
            32, 101, 120, 99, 101, 101, 100, 115, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100,
            32, 102, 111, 114, 32, 101, 120, 112, 111, 110, 101, 110, 116, 105, 97, 116, 105, 111,
            110, 32, 96, 40, 101, 120, 112, 32, 58, 61, 32, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_checkExp___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_checkExp___closed__5_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_checkExp___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_checkExp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__1_value) as *mut crate::leanh::LeanObject,13428217069302927667 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 65, 98, 115, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__4_value) as *mut crate::leanh::LeanObject,12132318982517471999 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__6_value) as *mut crate::leanh::LeanObject,13897037934312376979 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 117, 99, 99, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__8_value) as *mut crate::leanh::LeanObject,16112798088292836701 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__11_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__11_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__10_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__11_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__13_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__14_value) as *mut crate::leanh::LeanObject,10422657989269798688 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__17_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__16_value) as *mut crate::leanh::LeanObject,13744984671752750173 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__17_value) as *mut crate::leanh::LeanObject,9682224670061807480 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__20_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__19_value) as *mut crate::leanh::LeanObject,11858238400308895562 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__20_value) as *mut crate::leanh::LeanObject,6100819061652633370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__22_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__23_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__23_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__22_value) as *mut crate::leanh::LeanObject,16856108565602861689 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__23_value) as *mut crate::leanh::LeanObject,4187025665268973031 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__25_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__26_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__26_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__25_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__26_value) as *mut crate::leanh::LeanObject,1611444129324655608 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__28_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__29_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__29_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__28_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__29_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 115, 116, 78, 97, 116, 67, 97, 115, 116, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__0_value) as *mut crate::leanh::LeanObject,14240220390202531956 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__2_value) as *mut crate::leanh::LeanObject,8075995802451307795 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__4_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__4_value) as *mut crate::leanh::LeanObject,5779414593499529281 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__5_value) as *mut crate::leanh::LeanObject,7063772860359172143 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__8_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__7_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__8_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_checkExp___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1075_ = l_Lean_Meta_Sym_Arith_checkExp___closed__1;
    v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
    return v___x_1076_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_checkExp___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = l_Lean_Meta_Sym_Arith_checkExp___closed__3;
    v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
    return v___x_1079_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_checkExp___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lean_Meta_Sym_Arith_checkExp___closed__5;
    v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
    return v___x_1082_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_checkExp(
    mut v_k_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
    mut v_a_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: u8 = 0;
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: u8 = 0;
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1124_: u8 = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1128_: u8 = 0;
    let mut v_a_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1136_: u8 = 0;
    let mut v_isSharedCheck_1137_: u8 = 0;
    let mut v_a_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1141_: u8 = 0;
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1094_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_1085_, v_a_1088_);
                if crate::leanh::lean_obj_tag(v___x_1094_) == 0 {
                    v_a_1095_ = crate::leanh::lean_ctor_get(v___x_1094_, 0);
                    v_isSharedCheck_1137_ = (!crate::leanh::lean_is_exclusive(v___x_1094_)) as u8;
                    if v_isSharedCheck_1137_ == 0 {
                        v___x_1097_ = v___x_1094_;
                        v_isShared_1098_ = v_isSharedCheck_1137_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1095_);
                        crate::leanh::lean_dec(v___x_1094_);
                        v___x_1097_ = crate::leanh::lean_box(0);
                        v_isShared_1098_ = v_isSharedCheck_1137_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_1083_);
                    v_a_1138_ = crate::leanh::lean_ctor_get(v___x_1094_, 0);
                    v_isSharedCheck_1145_ = (!crate::leanh::lean_is_exclusive(v___x_1094_)) as u8;
                    if v_isSharedCheck_1145_ == 0 {
                        v___x_1140_ = v___x_1094_;
                        v_isShared_1141_ = v_isSharedCheck_1145_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1138_);
                        crate::leanh::lean_dec(v___x_1094_);
                        v___x_1140_ = crate::leanh::lean_box(0);
                        v_isShared_1141_ = v_isSharedCheck_1145_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1092_ = crate::leanh::lean_box(0);
                v___x_1093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1093_, 0, v___x_1092_);
                return v___x_1093_;
            }
            2 => {
                v___x_1099_ = lean_nat_dec_lt(v_a_1095_, v_k_1083_);
                if v___x_1099_ == 0 {
                    crate::leanh::lean_dec(v_a_1095_);
                    crate::leanh::lean_dec(v_k_1083_);
                    v___x_1100_ = l_Lean_Meta_Sym_Arith_checkExp___closed__0;
                    if v_isShared_1098_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1097_, 0, v___x_1100_);
                        v___x_1102_ = v___x_1097_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1103_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
                        v___x_1102_ = v_reuseFailAlloc_1103_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1097_);
                    v___x_1104_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1084_);
                    if crate::leanh::lean_obj_tag(v___x_1104_) == 0 {
                        v_a_1105_ = crate::leanh::lean_ctor_get(v___x_1104_, 0);
                        crate::leanh::lean_inc(v_a_1105_);
                        crate::leanh::lean_dec_ref_known(v___x_1104_, 1);
                        v___x_1106_ = (crate::leanh::lean_unbox(v_a_1105_) as u8);
                        crate::leanh::lean_dec(v_a_1105_);
                        if v___x_1106_ == 0 {
                            crate::leanh::lean_dec(v_a_1095_);
                            crate::leanh::lean_dec(v_k_1083_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1107_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_checkExp___closed__2),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_Arith_checkExp___closed__2_once
                                ),
                                _init_l_Lean_Meta_Sym_Arith_checkExp___closed__2,
                            );
                            v___x_1108_ = l_Nat_reprFast(v_k_1083_);
                            v___x_1109_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1109_, 0, v___x_1108_);
                            v___x_1110_ = l_Lean_MessageData_ofFormat(v___x_1109_);
                            v___x_1111_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1111_, 0, v___x_1107_);
                            crate::leanh::lean_ctor_set(v___x_1111_, 1, v___x_1110_);
                            v___x_1112_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_checkExp___closed__4),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_Arith_checkExp___closed__4_once
                                ),
                                _init_l_Lean_Meta_Sym_Arith_checkExp___closed__4,
                            );
                            v___x_1113_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1113_, 0, v___x_1111_);
                            crate::leanh::lean_ctor_set(v___x_1113_, 1, v___x_1112_);
                            v___x_1114_ = l_Nat_reprFast(v_a_1095_);
                            v___x_1115_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1115_, 0, v___x_1114_);
                            v___x_1116_ = l_Lean_MessageData_ofFormat(v___x_1115_);
                            v___x_1117_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1117_, 0, v___x_1113_);
                            crate::leanh::lean_ctor_set(v___x_1117_, 1, v___x_1116_);
                            v___x_1118_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_checkExp___closed__6),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Sym_Arith_checkExp___closed__6_once
                                ),
                                _init_l_Lean_Meta_Sym_Arith_checkExp___closed__6,
                            );
                            v___x_1119_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1119_, 0, v___x_1117_);
                            crate::leanh::lean_ctor_set(v___x_1119_, 1, v___x_1118_);
                            v___x_1120_ = l_Lean_Meta_Sym_reportIssue(
                                v___x_1119_,
                                v_a_1084_,
                                v_a_1085_,
                                v_a_1086_,
                                v_a_1087_,
                                v_a_1088_,
                                v_a_1089_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1120_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1120_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_1121_ = crate::leanh::lean_ctor_get(v___x_1120_, 0);
                                v_isSharedCheck_1128_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1120_)) as u8;
                                if v_isSharedCheck_1128_ == 0 {
                                    v___x_1123_ = v___x_1120_;
                                    v_isShared_1124_ = v_isSharedCheck_1128_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1121_);
                                    crate::leanh::lean_dec(v___x_1120_);
                                    v___x_1123_ = crate::leanh::lean_box(0);
                                    v_isShared_1124_ = v_isSharedCheck_1128_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1095_);
                        crate::leanh::lean_dec(v_k_1083_);
                        v_a_1129_ = crate::leanh::lean_ctor_get(v___x_1104_, 0);
                        v_isSharedCheck_1136_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1104_)) as u8;
                        if v_isSharedCheck_1136_ == 0 {
                            v___x_1131_ = v___x_1104_;
                            v_isShared_1132_ = v_isSharedCheck_1136_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1129_);
                            crate::leanh::lean_dec(v___x_1104_);
                            v___x_1131_ = crate::leanh::lean_box(0);
                            v_isShared_1132_ = v_isSharedCheck_1136_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_1102_;
            }
            4 => {
                if v_isShared_1124_ == 0 {
                    v___x_1126_ = v___x_1123_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
                    v___x_1126_ = v_reuseFailAlloc_1127_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1126_;
            }
            6 => {
                if v_isShared_1132_ == 0 {
                    v___x_1134_ = v___x_1131_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1135_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
                    v___x_1134_ = v_reuseFailAlloc_1135_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1134_;
            }
            8 => {
                if v_isShared_1141_ == 0 {
                    v___x_1143_ = v___x_1140_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
                    v___x_1143_ = v_reuseFailAlloc_1144_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_checkExp___boxed(
    mut v_k_1146_: *mut crate::leanh::LeanObject,
    mut v_a_1147_: *mut crate::leanh::LeanObject,
    mut v_a_1148_: *mut crate::leanh::LeanObject,
    mut v_a_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lean_Meta_Sym_Arith_checkExp(
        v_k_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_,
    );
    crate::leanh::lean_dec(v_a_1152_);
    crate::leanh::lean_dec_ref(v_a_1151_);
    crate::leanh::lean_dec(v_a_1150_);
    crate::leanh::lean_dec_ref(v_a_1149_);
    crate::leanh::lean_dec(v_a_1148_);
    crate::leanh::lean_dec_ref(v_a_1147_);
    return v_res_1154_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
    mut v_e_1227_: *mut crate::leanh::LeanObject,
    mut v_a_1228_: *mut crate::leanh::LeanObject,
    mut v_a_1229_: *mut crate::leanh::LeanObject,
    mut v_a_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_a_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1268_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut v_a_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut v_a_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1299_: u8 = 0;
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v_arg_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut v_arg_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v_arg_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: u8 = 0;
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: u8 = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v_val_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_unused_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v_a_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1377_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1399_: u8 = 0;
    let mut v_val_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1403_: u8 = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_unused_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_a_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1427_: u8 = 0;
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1440_: u8 = 0;
    let mut v_val_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1452_: u8 = 0;
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_unused_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut v_a_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1459_: u8 = 0;
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v_val_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1485_: u8 = 0;
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1493_: u8 = 0;
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut v_unused_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut v_a_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1500_: u8 = 0;
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1504_: u8 = 0;
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v_val_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut v_unused_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1537_: u8 = 0;
    let mut v_a_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1573_: u8 = 0;
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1580_: u8 = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1588_: u8 = 0;
    let mut v_unused_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_a_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_a_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut v_a_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v_val_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_unused_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut v_a_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1650_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1654_: u8 = 0;
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v_a_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1227_);
                v___x_1295_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1227_, v_a_1231_);
                if crate::leanh::lean_obj_tag(v___x_1295_) == 0 {
                    v_a_1296_ = crate::leanh::lean_ctor_get(v___x_1295_, 0);
                    v_isSharedCheck_1659_ = (!crate::leanh::lean_is_exclusive(v___x_1295_)) as u8;
                    if v_isSharedCheck_1659_ == 0 {
                        v___x_1298_ = v___x_1295_;
                        v_isShared_1299_ = v_isSharedCheck_1659_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1296_);
                        crate::leanh::lean_dec(v___x_1295_);
                        v___x_1298_ = crate::leanh::lean_box(0);
                        v_isShared_1299_ = v_isSharedCheck_1659_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1227_);
                    v_a_1660_ = crate::leanh::lean_ctor_get(v___x_1295_, 0);
                    v_isSharedCheck_1667_ = (!crate::leanh::lean_is_exclusive(v___x_1295_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1662_ = v___x_1295_;
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 79;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1660_);
                        crate::leanh::lean_dec(v___x_1295_);
                        v___x_1662_ = crate::leanh::lean_box(0);
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 79;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1244_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_i_1236_, v___y_1241_);
                if crate::leanh::lean_obj_tag(v___x_1244_) == 0 {
                    v_a_1245_ = crate::leanh::lean_ctor_get(v___x_1244_, 0);
                    v_isSharedCheck_1286_ = (!crate::leanh::lean_is_exclusive(v___x_1244_)) as u8;
                    if v_isSharedCheck_1286_ == 0 {
                        v___x_1247_ = v___x_1244_;
                        v_isShared_1248_ = v_isSharedCheck_1286_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1245_);
                        crate::leanh::lean_dec(v___x_1244_);
                        v___x_1247_ = crate::leanh::lean_box(0);
                        v_isShared_1248_ = v_isSharedCheck_1286_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1237_);
                    v_a_1287_ = crate::leanh::lean_ctor_get(v___x_1244_, 0);
                    v_isSharedCheck_1294_ = (!crate::leanh::lean_is_exclusive(v___x_1244_)) as u8;
                    if v_isSharedCheck_1294_ == 0 {
                        v___x_1289_ = v___x_1244_;
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1287_);
                        crate::leanh::lean_dec(v___x_1244_);
                        v___x_1289_ = crate::leanh::lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1249_ = l_Lean_Expr_cleanupAnnotations(v_a_1245_);
                v___x_1250_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1;
                v___x_1251_ = l_Lean_Expr_isConstOf(v___x_1249_, v___x_1250_);
                crate::leanh::lean_dec_ref(v___x_1249_);
                if v___x_1251_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_1237_);
                    v___x_1252_ = crate::leanh::lean_box(0);
                    if v_isShared_1248_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1247_, 0, v___x_1252_);
                        v___x_1254_ = v___x_1247_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
                        v___x_1254_ = v_reuseFailAlloc_1255_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1247_);
                    v___x_1256_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
                            v_a_1237_,
                            v___y_1238_,
                            v___y_1239_,
                            v___y_1240_,
                            v___y_1241_,
                            v___y_1242_,
                            v___y_1243_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1256_) == 0 {
                        v_a_1257_ = crate::leanh::lean_ctor_get(v___x_1256_, 0);
                        v_isSharedCheck_1277_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1256_)) as u8;
                        if v_isSharedCheck_1277_ == 0 {
                            v___x_1259_ = v___x_1256_;
                            v_isShared_1260_ = v_isSharedCheck_1277_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1257_);
                            crate::leanh::lean_dec(v___x_1256_);
                            v___x_1259_ = crate::leanh::lean_box(0);
                            v_isShared_1260_ = v_isSharedCheck_1277_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_1278_ = crate::leanh::lean_ctor_get(v___x_1256_, 0);
                        v_isSharedCheck_1285_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1256_)) as u8;
                        if v_isSharedCheck_1285_ == 0 {
                            v___x_1280_ = v___x_1256_;
                            v_isShared_1281_ = v_isSharedCheck_1285_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1278_);
                            crate::leanh::lean_dec(v___x_1256_);
                            v___x_1280_ = crate::leanh::lean_box(0);
                            v_isShared_1281_ = v_isSharedCheck_1285_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_1254_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_1257_) == 0 {
                    v___x_1261_ = crate::leanh::lean_box(0);
                    if v_isShared_1260_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1259_, 0, v___x_1261_);
                        v___x_1263_ = v___x_1259_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
                        v___x_1263_ = v_reuseFailAlloc_1264_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_1265_ = crate::leanh::lean_ctor_get(v_a_1257_, 0);
                    v_isSharedCheck_1276_ = (!crate::leanh::lean_is_exclusive(v_a_1257_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1267_ = v_a_1257_;
                        v_isShared_1268_ = v_isSharedCheck_1276_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1265_);
                        crate::leanh::lean_dec(v_a_1257_);
                        v___x_1267_ = crate::leanh::lean_box(0);
                        v_isShared_1268_ = v_isSharedCheck_1276_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1263_;
            }
            6 => {
                v___x_1269_ = lean_nat_to_int(v_val_1265_);
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1269_);
                    v___x_1271_ = v___x_1267_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1269_);
                    v___x_1271_ = v_reuseFailAlloc_1275_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1259_, 0, v___x_1271_);
                    v___x_1273_ = v___x_1259_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
                    v___x_1273_ = v_reuseFailAlloc_1274_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1273_;
            }
            9 => {
                if v_isShared_1281_ == 0 {
                    v___x_1283_ = v___x_1280_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
                    v___x_1283_ = v_reuseFailAlloc_1284_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1283_;
            }
            11 => {
                if v_isShared_1290_ == 0 {
                    v___x_1292_ = v___x_1289_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
                    v___x_1292_ = v_reuseFailAlloc_1293_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1292_;
            }
            13 => {
                v___x_1305_ = l_Lean_Expr_cleanupAnnotations(v_a_1296_);
                v___x_1306_ = l_Lean_Expr_isApp(v___x_1305_);
                if v___x_1306_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1305_);
                    crate::leanh::lean_dec_ref(v_e_1227_);
                    state = 14;
                    continue;
                } else {
                    v_arg_1307_ = crate::leanh::lean_ctor_get(v___x_1305_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1307_);
                    v___x_1308_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1305_);
                    v___x_1309_ = l_Lean_Expr_isApp(v___x_1308_);
                    if v___x_1309_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1308_);
                        crate::leanh::lean_dec_ref(v_arg_1307_);
                        crate::leanh::lean_dec_ref(v_e_1227_);
                        state = 14;
                        continue;
                    } else {
                        v_arg_1310_ = crate::leanh::lean_ctor_get(v___x_1308_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1310_);
                        v___x_1311_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1308_);
                        v___x_1312_ = l_Lean_Expr_isApp(v___x_1311_);
                        if v___x_1312_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1311_);
                            crate::leanh::lean_dec_ref(v_arg_1310_);
                            crate::leanh::lean_dec_ref(v_arg_1307_);
                            crate::leanh::lean_dec_ref(v_e_1227_);
                            state = 14;
                            continue;
                        } else {
                            v_arg_1313_ = crate::leanh::lean_ctor_get(v___x_1311_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1313_);
                            v___x_1314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1311_);
                            v___x_1315_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3;
                            v___x_1316_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1315_);
                            if v___x_1316_ == 0 {
                                v___x_1317_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6;
                                v___x_1318_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1317_);
                                if v___x_1318_ == 0 {
                                    v___x_1319_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12;
                                    v___x_1320_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1319_);
                                    if v___x_1320_ == 0 {
                                        crate::leanh::lean_dec_ref(v_e_1227_);
                                        v___x_1321_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9;
                                        v___x_1322_ =
                                            l_Lean_Expr_isConstOf(v___x_1314_, v___x_1321_);
                                        if v___x_1322_ == 0 {
                                            v___x_1323_ = l_Lean_Expr_isApp(v___x_1314_);
                                            if v___x_1323_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_1314_);
                                                crate::leanh::lean_dec_ref(v_arg_1313_);
                                                crate::leanh::lean_dec_ref(v_arg_1310_);
                                                crate::leanh::lean_dec_ref(v_arg_1307_);
                                                state = 14;
                                                continue;
                                            } else {
                                                v___x_1324_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_1314_);
                                                v___x_1325_ = l_Lean_Expr_isApp(v___x_1324_);
                                                if v___x_1325_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_1324_);
                                                    crate::leanh::lean_dec_ref(v_arg_1313_);
                                                    crate::leanh::lean_dec_ref(v_arg_1310_);
                                                    crate::leanh::lean_dec_ref(v_arg_1307_);
                                                    state = 14;
                                                    continue;
                                                } else {
                                                    v___x_1326_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1324_,
                                                    );
                                                    v___x_1327_ = l_Lean_Expr_isApp(v___x_1326_);
                                                    if v___x_1327_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_1326_);
                                                        crate::leanh::lean_dec_ref(v_arg_1313_);
                                                        crate::leanh::lean_dec_ref(v_arg_1310_);
                                                        crate::leanh::lean_dec_ref(v_arg_1307_);
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        v___x_1328_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_1326_,
                                                            );
                                                        v___x_1329_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15;
                                                        v___x_1330_ = l_Lean_Expr_isConstOf(
                                                            v___x_1328_,
                                                            v___x_1329_,
                                                        );
                                                        if v___x_1330_ == 0 {
                                                            v___x_1331_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18;
                                                            v___x_1332_ = l_Lean_Expr_isConstOf(
                                                                v___x_1328_,
                                                                v___x_1331_,
                                                            );
                                                            if v___x_1332_ == 0 {
                                                                v___x_1333_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21;
                                                                v___x_1334_ = l_Lean_Expr_isConstOf(
                                                                    v___x_1328_,
                                                                    v___x_1333_,
                                                                );
                                                                if v___x_1334_ == 0 {
                                                                    v___x_1335_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27;
                                                                    v___x_1336_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_1328_,
                                                                            v___x_1335_,
                                                                        );
                                                                    if v___x_1336_ == 0 {
                                                                        v___x_1337_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24;
                                                                        v___x_1338_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_1328_,
                                                                                v___x_1337_,
                                                                            );
                                                                        if v___x_1338_ == 0 {
                                                                            v___x_1339_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30;
                                                                            v___x_1340_ = l_Lean_Expr_isConstOf(v___x_1328_, v___x_1339_);
                                                                            crate::leanh::lean_dec_ref(v___x_1328_);
                                                                            if v___x_1340_ == 0 {
                                                                                crate::leanh::lean_dec_ref(v_arg_1313_);
                                                                                crate::leanh::lean_dec_ref(v_arg_1310_);
                                                                                crate::leanh::lean_dec_ref(v_arg_1307_);
                                                                                state = 14;
                                                                                continue;
                                                                            } else {
                                                                                crate::leanh::lean_del_object(v___x_1298_);
                                                                                v___x_1341_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1313_, v_a_1231_);
                                                                                if crate::leanh::lean_obj_tag(v___x_1341_) == 0 {
v_a_1342_ = crate::leanh::lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1373_ = (!crate::leanh::lean_is_exclusive(v___x_1341_)) as u8;
if v_isSharedCheck_1373_ == 0 {
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1373_;
state = 16; continue;
} else {
crate::leanh::lean_inc(v_a_1342_);
crate::leanh::lean_dec(v___x_1341_);
v___x_1344_ = crate::leanh::lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1373_;
state = 16; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1310_);
crate::leanh::lean_dec_ref(v_arg_1307_);
v_a_1374_ = crate::leanh::lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1381_ = (!crate::leanh::lean_is_exclusive(v___x_1341_)) as u8;
if v_isSharedCheck_1381_ == 0 {
v___x_1376_ = v___x_1341_;
v_isShared_1377_ = v_isSharedCheck_1381_;
state = 22; continue;
} else {
crate::leanh::lean_inc(v_a_1374_);
crate::leanh::lean_dec(v___x_1341_);
v___x_1376_ = crate::leanh::lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
state = 22; continue;
}
}
                                                                            }
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v___x_1328_);
                                                                            crate::leanh::lean_del_object(v___x_1298_);
                                                                            v___x_1382_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_1313_, v_a_1231_);
                                                                            if crate::leanh::lean_obj_tag(v___x_1382_) == 0 {
v_a_1383_ = crate::leanh::lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1414_ = (!crate::leanh::lean_is_exclusive(v___x_1382_)) as u8;
if v_isSharedCheck_1414_ == 0 {
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1414_;
state = 24; continue;
} else {
crate::leanh::lean_inc(v_a_1383_);
crate::leanh::lean_dec(v___x_1382_);
v___x_1385_ = crate::leanh::lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1414_;
state = 24; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1310_);
crate::leanh::lean_dec_ref(v_arg_1307_);
v_a_1415_ = crate::leanh::lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1422_ = (!crate::leanh::lean_is_exclusive(v___x_1382_)) as u8;
if v_isSharedCheck_1422_ == 0 {
v___x_1417_ = v___x_1382_;
v_isShared_1418_ = v_isSharedCheck_1422_;
state = 30; continue;
} else {
crate::leanh::lean_inc(v_a_1415_);
crate::leanh::lean_dec(v___x_1382_);
v___x_1417_ = crate::leanh::lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
state = 30; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_1328_,
                                                                        );
                                                                        crate::leanh::lean_del_object(v___x_1298_);
                                                                        v___x_1423_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1313_, v_a_1231_);
                                                                        if crate::leanh::lean_obj_tag(v___x_1423_) == 0 {
v_a_1424_ = crate::leanh::lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1455_ = (!crate::leanh::lean_is_exclusive(v___x_1423_)) as u8;
if v_isSharedCheck_1455_ == 0 {
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1455_;
state = 32; continue;
} else {
crate::leanh::lean_inc(v_a_1424_);
crate::leanh::lean_dec(v___x_1423_);
v___x_1426_ = crate::leanh::lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1455_;
state = 32; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1310_);
crate::leanh::lean_dec_ref(v_arg_1307_);
v_a_1456_ = crate::leanh::lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1463_ = (!crate::leanh::lean_is_exclusive(v___x_1423_)) as u8;
if v_isSharedCheck_1463_ == 0 {
v___x_1458_ = v___x_1423_;
v_isShared_1459_ = v_isSharedCheck_1463_;
state = 38; continue;
} else {
crate::leanh::lean_inc(v_a_1456_);
crate::leanh::lean_dec(v___x_1423_);
v___x_1458_ = crate::leanh::lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
state = 38; continue;
}
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_1328_,
                                                                    );
                                                                    crate::leanh::lean_del_object(
                                                                        v___x_1298_,
                                                                    );
                                                                    v___x_1464_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_1313_, v_a_1231_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_1464_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_1465_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                                                                        v_isSharedCheck_1496_ = (!crate::leanh::lean_is_exclusive(v___x_1464_)) as u8;
                                                                        if v_isSharedCheck_1496_
                                                                            == 0
                                                                        {
                                                                            v___x_1467_ =
                                                                                v___x_1464_;
                                                                            v_isShared_1468_ = v_isSharedCheck_1496_;
                                                                            state = 40;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_1465_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1464_,
                                                                            );
                                                                            v___x_1467_ = crate::leanh::lean_box(0);
                                                                            v_isShared_1468_ = v_isSharedCheck_1496_;
                                                                            state = 40;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1310_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1307_,
                                                                        );
                                                                        v_a_1497_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                                                                        v_isSharedCheck_1504_ = (!crate::leanh::lean_is_exclusive(v___x_1464_)) as u8;
                                                                        if v_isSharedCheck_1504_
                                                                            == 0
                                                                        {
                                                                            v___x_1499_ =
                                                                                v___x_1464_;
                                                                            v_isShared_1500_ = v_isSharedCheck_1504_;
                                                                            state = 46;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_1497_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1464_,
                                                                            );
                                                                            v___x_1499_ = crate::leanh::lean_box(0);
                                                                            v_isShared_1500_ = v_isSharedCheck_1504_;
                                                                            state = 46;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_1328_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_1298_,
                                                                );
                                                                v___x_1505_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_1313_, v_a_1231_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_1505_,
                                                                ) == 0
                                                                {
                                                                    v_a_1506_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1505_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1537_ = (!crate::leanh::lean_is_exclusive(v___x_1505_)) as u8;
                                                                    if v_isSharedCheck_1537_ == 0 {
                                                                        v___x_1508_ = v___x_1505_;
                                                                        v_isShared_1509_ =
                                                                            v_isSharedCheck_1537_;
                                                                        state = 48;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1506_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1505_,
                                                                        );
                                                                        v___x_1508_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1509_ =
                                                                            v_isSharedCheck_1537_;
                                                                        state = 48;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1310_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1307_,
                                                                    );
                                                                    v_a_1538_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1505_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1545_ = (!crate::leanh::lean_is_exclusive(v___x_1505_)) as u8;
                                                                    if v_isSharedCheck_1545_ == 0 {
                                                                        v___x_1540_ = v___x_1505_;
                                                                        v_isShared_1541_ =
                                                                            v_isSharedCheck_1545_;
                                                                        state = 54;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1538_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1505_,
                                                                        );
                                                                        v___x_1540_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1541_ =
                                                                            v_isSharedCheck_1545_;
                                                                        state = 54;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_1328_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_1298_,
                                                            );
                                                            v___x_1546_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_1313_, v_a_1231_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_1546_,
                                                            ) == 0
                                                            {
                                                                v_a_1547_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_1546_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_1608_ = (!crate::leanh::lean_is_exclusive(v___x_1546_)) as u8;
                                                                if v_isSharedCheck_1608_ == 0 {
                                                                    v___x_1549_ = v___x_1546_;
                                                                    v_isShared_1550_ =
                                                                        v_isSharedCheck_1608_;
                                                                    state = 56;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_1547_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1546_,
                                                                    );
                                                                    v___x_1549_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_1550_ =
                                                                        v_isSharedCheck_1608_;
                                                                    state = 56;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1310_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1307_,
                                                                );
                                                                v_a_1609_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_1546_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_1616_ = (!crate::leanh::lean_is_exclusive(v___x_1546_)) as u8;
                                                                if v_isSharedCheck_1616_ == 0 {
                                                                    v___x_1611_ = v___x_1546_;
                                                                    v_isShared_1612_ =
                                                                        v_isSharedCheck_1616_;
                                                                    state = 69;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_1609_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1546_,
                                                                    );
                                                                    v___x_1611_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_1612_ =
                                                                        v_isSharedCheck_1616_;
                                                                    state = 69;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1314_);
                                            crate::leanh::lean_dec_ref(v_arg_1313_);
                                            crate::leanh::lean_del_object(v___x_1298_);
                                            v___x_1617_ =
                                                l_Lean_Meta_Structural_isInstNegInt___redArg(
                                                    v_arg_1310_,
                                                    v_a_1231_,
                                                );
                                            if crate::leanh::lean_obj_tag(v___x_1617_) == 0 {
                                                v_a_1618_ =
                                                    crate::leanh::lean_ctor_get(v___x_1617_, 0);
                                                v_isSharedCheck_1646_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_1617_))
                                                        as u8;
                                                if v_isSharedCheck_1646_ == 0 {
                                                    v___x_1620_ = v___x_1617_;
                                                    v_isShared_1621_ = v_isSharedCheck_1646_;
                                                    state = 71;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_1618_);
                                                    crate::leanh::lean_dec(v___x_1617_);
                                                    v___x_1620_ = crate::leanh::lean_box(0);
                                                    v_isShared_1621_ = v_isSharedCheck_1646_;
                                                    state = 71;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_arg_1307_);
                                                v_a_1647_ =
                                                    crate::leanh::lean_ctor_get(v___x_1617_, 0);
                                                v_isSharedCheck_1654_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_1617_))
                                                        as u8;
                                                if v_isSharedCheck_1654_ == 0 {
                                                    v___x_1649_ = v___x_1617_;
                                                    v_isShared_1650_ = v_isSharedCheck_1654_;
                                                    state = 77;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_1647_);
                                                    crate::leanh::lean_dec(v___x_1617_);
                                                    v___x_1649_ = crate::leanh::lean_box(0);
                                                    v_isShared_1650_ = v_isSharedCheck_1654_;
                                                    state = 77;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_1314_);
                                        crate::leanh::lean_dec_ref(v_arg_1313_);
                                        crate::leanh::lean_dec_ref(v_arg_1310_);
                                        crate::leanh::lean_dec_ref(v_arg_1307_);
                                        crate::leanh::lean_del_object(v___x_1298_);
                                        v___x_1655_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_1227_);
                                        if crate::leanh::lean_obj_tag(v___x_1655_) == 1 {
                                            v___x_1656_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1656_,
                                                0,
                                                v___x_1655_,
                                            );
                                            return v___x_1656_;
                                        } else {
                                            crate::leanh::lean_dec(v___x_1655_);
                                            v___x_1657_ = crate::leanh::lean_box(0);
                                            v___x_1658_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1658_,
                                                0,
                                                v___x_1657_,
                                            );
                                            return v___x_1658_;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_1314_);
                                    crate::leanh::lean_dec_ref(v_arg_1313_);
                                    crate::leanh::lean_del_object(v___x_1298_);
                                    crate::leanh::lean_dec_ref(v_e_1227_);
                                    v_i_1236_ = v_arg_1310_;
                                    v_a_1237_ = v_arg_1307_;
                                    v___y_1238_ = v_a_1228_;
                                    v___y_1239_ = v_a_1229_;
                                    v___y_1240_ = v_a_1230_;
                                    v___y_1241_ = v_a_1231_;
                                    v___y_1242_ = v_a_1232_;
                                    v___y_1243_ = v_a_1233_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1314_);
                                crate::leanh::lean_dec_ref(v_arg_1313_);
                                crate::leanh::lean_del_object(v___x_1298_);
                                crate::leanh::lean_dec_ref(v_e_1227_);
                                v_i_1236_ = v_arg_1310_;
                                v_a_1237_ = v_arg_1307_;
                                v___y_1238_ = v_a_1228_;
                                v___y_1239_ = v_a_1229_;
                                v___y_1240_ = v_a_1230_;
                                v___y_1241_ = v_a_1231_;
                                v___y_1242_ = v_a_1232_;
                                v___y_1243_ = v_a_1233_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            14 => {
                v___x_1301_ = crate::leanh::lean_box(0);
                if v_isShared_1299_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1298_, 0, v___x_1301_);
                    v___x_1303_ = v___x_1298_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
                    v___x_1303_ = v_reuseFailAlloc_1304_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1303_;
            }
            16 => {
                v___x_1346_ = (crate::leanh::lean_unbox(v_a_1342_) as u8);
                crate::leanh::lean_dec(v_a_1342_);
                if v___x_1346_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1310_);
                    crate::leanh::lean_dec_ref(v_arg_1307_);
                    v___x_1347_ = crate::leanh::lean_box(0);
                    if v_isShared_1345_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1344_, 0, v___x_1347_);
                        v___x_1349_ = v___x_1344_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
                        v___x_1349_ = v_reuseFailAlloc_1350_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1344_);
                    v___x_1351_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
                            v_arg_1310_,
                            v_a_1228_,
                            v_a_1229_,
                            v_a_1230_,
                            v_a_1231_,
                            v_a_1232_,
                            v_a_1233_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1351_) == 0 {
                        v_a_1352_ = crate::leanh::lean_ctor_get(v___x_1351_, 0);
                        crate::leanh::lean_inc(v_a_1352_);
                        if crate::leanh::lean_obj_tag(v_a_1352_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1307_);
                            return v___x_1351_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1351_, 1);
                            v_val_1353_ = crate::leanh::lean_ctor_get(v_a_1352_, 0);
                            crate::leanh::lean_inc(v_val_1353_);
                            crate::leanh::lean_dec_ref_known(v_a_1352_, 1);
                            v___x_1354_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_1307_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
                            if crate::leanh::lean_obj_tag(v___x_1354_) == 0 {
                                v_a_1355_ = crate::leanh::lean_ctor_get(v___x_1354_, 0);
                                crate::leanh::lean_inc(v_a_1355_);
                                if crate::leanh::lean_obj_tag(v_a_1355_) == 0 {
                                    crate::leanh::lean_dec(v_val_1353_);
                                    return v___x_1354_;
                                } else {
                                    v_isSharedCheck_1371_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1354_)) as u8;
                                    if v_isSharedCheck_1371_ == 0 {
                                        v_unused_1372_ =
                                            crate::leanh::lean_ctor_get(v___x_1354_, 0);
                                        crate::leanh::lean_dec(v_unused_1372_);
                                        v___x_1357_ = v___x_1354_;
                                        v_isShared_1358_ = v_isSharedCheck_1371_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1354_);
                                        v___x_1357_ = crate::leanh::lean_box(0);
                                        v_isShared_1358_ = v_isSharedCheck_1371_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1353_);
                                return v___x_1354_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1307_);
                        return v___x_1351_;
                    }
                }
            }
            17 => {
                return v___x_1349_;
            }
            18 => {
                v_val_1359_ = crate::leanh::lean_ctor_get(v_a_1355_, 0);
                v_isSharedCheck_1370_ = (!crate::leanh::lean_is_exclusive(v_a_1355_)) as u8;
                if v_isSharedCheck_1370_ == 0 {
                    v___x_1361_ = v_a_1355_;
                    v_isShared_1362_ = v_isSharedCheck_1370_;
                    state = 19;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1359_);
                    crate::leanh::lean_dec(v_a_1355_);
                    v___x_1361_ = crate::leanh::lean_box(0);
                    v_isShared_1362_ = v_isSharedCheck_1370_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1363_ = lean_int_add(v_val_1353_, v_val_1359_);
                crate::leanh::lean_dec(v_val_1359_);
                crate::leanh::lean_dec(v_val_1353_);
                if v_isShared_1362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1361_, 0, v___x_1363_);
                    v___x_1365_ = v___x_1361_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1363_);
                    v___x_1365_ = v_reuseFailAlloc_1369_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1365_);
                    v___x_1367_ = v___x_1357_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
                    v___x_1367_ = v_reuseFailAlloc_1368_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1367_;
            }
            22 => {
                if v_isShared_1377_ == 0 {
                    v___x_1379_ = v___x_1376_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
                    v___x_1379_ = v_reuseFailAlloc_1380_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1379_;
            }
            24 => {
                v___x_1387_ = (crate::leanh::lean_unbox(v_a_1383_) as u8);
                crate::leanh::lean_dec(v_a_1383_);
                if v___x_1387_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1310_);
                    crate::leanh::lean_dec_ref(v_arg_1307_);
                    v___x_1388_ = crate::leanh::lean_box(0);
                    if v_isShared_1386_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1385_, 0, v___x_1388_);
                        v___x_1390_ = v___x_1385_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_1391_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
                        v___x_1390_ = v_reuseFailAlloc_1391_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1385_);
                    v___x_1392_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
                            v_arg_1310_,
                            v_a_1228_,
                            v_a_1229_,
                            v_a_1230_,
                            v_a_1231_,
                            v_a_1232_,
                            v_a_1233_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1392_) == 0 {
                        v_a_1393_ = crate::leanh::lean_ctor_get(v___x_1392_, 0);
                        crate::leanh::lean_inc(v_a_1393_);
                        if crate::leanh::lean_obj_tag(v_a_1393_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1307_);
                            return v___x_1392_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1392_, 1);
                            v_val_1394_ = crate::leanh::lean_ctor_get(v_a_1393_, 0);
                            crate::leanh::lean_inc(v_val_1394_);
                            crate::leanh::lean_dec_ref_known(v_a_1393_, 1);
                            v___x_1395_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_1307_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
                            if crate::leanh::lean_obj_tag(v___x_1395_) == 0 {
                                v_a_1396_ = crate::leanh::lean_ctor_get(v___x_1395_, 0);
                                crate::leanh::lean_inc(v_a_1396_);
                                if crate::leanh::lean_obj_tag(v_a_1396_) == 0 {
                                    crate::leanh::lean_dec(v_val_1394_);
                                    return v___x_1395_;
                                } else {
                                    v_isSharedCheck_1412_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1395_)) as u8;
                                    if v_isSharedCheck_1412_ == 0 {
                                        v_unused_1413_ =
                                            crate::leanh::lean_ctor_get(v___x_1395_, 0);
                                        crate::leanh::lean_dec(v_unused_1413_);
                                        v___x_1398_ = v___x_1395_;
                                        v_isShared_1399_ = v_isSharedCheck_1412_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1395_);
                                        v___x_1398_ = crate::leanh::lean_box(0);
                                        v_isShared_1399_ = v_isSharedCheck_1412_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1394_);
                                return v___x_1395_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1307_);
                        return v___x_1392_;
                    }
                }
            }
            25 => {
                return v___x_1390_;
            }
            26 => {
                v_val_1400_ = crate::leanh::lean_ctor_get(v_a_1396_, 0);
                v_isSharedCheck_1411_ = (!crate::leanh::lean_is_exclusive(v_a_1396_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v___x_1402_ = v_a_1396_;
                    v_isShared_1403_ = v_isSharedCheck_1411_;
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1400_);
                    crate::leanh::lean_dec(v_a_1396_);
                    v___x_1402_ = crate::leanh::lean_box(0);
                    v_isShared_1403_ = v_isSharedCheck_1411_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_1404_ = lean_int_sub(v_val_1394_, v_val_1400_);
                crate::leanh::lean_dec(v_val_1400_);
                crate::leanh::lean_dec(v_val_1394_);
                if v_isShared_1403_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1402_, 0, v___x_1404_);
                    v___x_1406_ = v___x_1402_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1404_);
                    v___x_1406_ = v_reuseFailAlloc_1410_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_1399_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1398_, 0, v___x_1406_);
                    v___x_1408_ = v___x_1398_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
                    v___x_1408_ = v_reuseFailAlloc_1409_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1408_;
            }
            30 => {
                if v_isShared_1418_ == 0 {
                    v___x_1420_ = v___x_1417_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
                    v___x_1420_ = v_reuseFailAlloc_1421_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1420_;
            }
            32 => {
                v___x_1428_ = (crate::leanh::lean_unbox(v_a_1424_) as u8);
                crate::leanh::lean_dec(v_a_1424_);
                if v___x_1428_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1310_);
                    crate::leanh::lean_dec_ref(v_arg_1307_);
                    v___x_1429_ = crate::leanh::lean_box(0);
                    if v_isShared_1427_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1429_);
                        v___x_1431_ = v___x_1426_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_1432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
                        v___x_1431_ = v_reuseFailAlloc_1432_;
                        state = 33;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1426_);
                    v___x_1433_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
                            v_arg_1310_,
                            v_a_1228_,
                            v_a_1229_,
                            v_a_1230_,
                            v_a_1231_,
                            v_a_1232_,
                            v_a_1233_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1433_) == 0 {
                        v_a_1434_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                        crate::leanh::lean_inc(v_a_1434_);
                        if crate::leanh::lean_obj_tag(v_a_1434_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1307_);
                            return v___x_1433_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1433_, 1);
                            v_val_1435_ = crate::leanh::lean_ctor_get(v_a_1434_, 0);
                            crate::leanh::lean_inc(v_val_1435_);
                            crate::leanh::lean_dec_ref_known(v_a_1434_, 1);
                            v___x_1436_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_1307_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
                            if crate::leanh::lean_obj_tag(v___x_1436_) == 0 {
                                v_a_1437_ = crate::leanh::lean_ctor_get(v___x_1436_, 0);
                                crate::leanh::lean_inc(v_a_1437_);
                                if crate::leanh::lean_obj_tag(v_a_1437_) == 0 {
                                    crate::leanh::lean_dec(v_val_1435_);
                                    return v___x_1436_;
                                } else {
                                    v_isSharedCheck_1453_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1436_)) as u8;
                                    if v_isSharedCheck_1453_ == 0 {
                                        v_unused_1454_ =
                                            crate::leanh::lean_ctor_get(v___x_1436_, 0);
                                        crate::leanh::lean_dec(v_unused_1454_);
                                        v___x_1439_ = v___x_1436_;
                                        v_isShared_1440_ = v_isSharedCheck_1453_;
                                        state = 34;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1436_);
                                        v___x_1439_ = crate::leanh::lean_box(0);
                                        v_isShared_1440_ = v_isSharedCheck_1453_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1435_);
                                return v___x_1436_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1307_);
                        return v___x_1433_;
                    }
                }
            }
            33 => {
                return v___x_1431_;
            }
            34 => {
                v_val_1441_ = crate::leanh::lean_ctor_get(v_a_1437_, 0);
                v_isSharedCheck_1452_ = (!crate::leanh::lean_is_exclusive(v_a_1437_)) as u8;
                if v_isSharedCheck_1452_ == 0 {
                    v___x_1443_ = v_a_1437_;
                    v_isShared_1444_ = v_isSharedCheck_1452_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1441_);
                    crate::leanh::lean_dec(v_a_1437_);
                    v___x_1443_ = crate::leanh::lean_box(0);
                    v_isShared_1444_ = v_isSharedCheck_1452_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1445_ = lean_int_mul(v_val_1435_, v_val_1441_);
                crate::leanh::lean_dec(v_val_1441_);
                crate::leanh::lean_dec(v_val_1435_);
                if v_isShared_1444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1443_, 0, v___x_1445_);
                    v___x_1447_ = v___x_1443_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1445_);
                    v___x_1447_ = v_reuseFailAlloc_1451_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1439_, 0, v___x_1447_);
                    v___x_1449_ = v___x_1439_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
                    v___x_1449_ = v_reuseFailAlloc_1450_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1449_;
            }
            38 => {
                if v_isShared_1459_ == 0 {
                    v___x_1461_ = v___x_1458_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
                    v___x_1461_ = v_reuseFailAlloc_1462_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1461_;
            }
            40 => {
                v___x_1469_ = (crate::leanh::lean_unbox(v_a_1465_) as u8);
                crate::leanh::lean_dec(v_a_1465_);
                if v___x_1469_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1310_);
                    crate::leanh::lean_dec_ref(v_arg_1307_);
                    v___x_1470_ = crate::leanh::lean_box(0);
                    if v_isShared_1468_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1470_);
                        v___x_1472_ = v___x_1467_;
                        state = 41;
                        continue;
                    } else {
                        v_reuseFailAlloc_1473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
                        v___x_1472_ = v_reuseFailAlloc_1473_;
                        state = 41;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1467_);
                    v___x_1474_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
                            v_arg_1310_,
                            v_a_1228_,
                            v_a_1229_,
                            v_a_1230_,
                            v_a_1231_,
                            v_a_1232_,
                            v_a_1233_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1474_) == 0 {
                        v_a_1475_ = crate::leanh::lean_ctor_get(v___x_1474_, 0);
                        crate::leanh::lean_inc(v_a_1475_);
                        if crate::leanh::lean_obj_tag(v_a_1475_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1307_);
                            return v___x_1474_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1474_, 1);
                            v_val_1476_ = crate::leanh::lean_ctor_get(v_a_1475_, 0);
                            crate::leanh::lean_inc(v_val_1476_);
                            crate::leanh::lean_dec_ref_known(v_a_1475_, 1);
                            v___x_1477_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_1307_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
                            if crate::leanh::lean_obj_tag(v___x_1477_) == 0 {
                                v_a_1478_ = crate::leanh::lean_ctor_get(v___x_1477_, 0);
                                crate::leanh::lean_inc(v_a_1478_);
                                if crate::leanh::lean_obj_tag(v_a_1478_) == 0 {
                                    crate::leanh::lean_dec(v_val_1476_);
                                    return v___x_1477_;
                                } else {
                                    v_isSharedCheck_1494_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1477_)) as u8;
                                    if v_isSharedCheck_1494_ == 0 {
                                        v_unused_1495_ =
                                            crate::leanh::lean_ctor_get(v___x_1477_, 0);
                                        crate::leanh::lean_dec(v_unused_1495_);
                                        v___x_1480_ = v___x_1477_;
                                        v_isShared_1481_ = v_isSharedCheck_1494_;
                                        state = 42;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1477_);
                                        v___x_1480_ = crate::leanh::lean_box(0);
                                        v_isShared_1481_ = v_isSharedCheck_1494_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1476_);
                                return v___x_1477_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1307_);
                        return v___x_1474_;
                    }
                }
            }
            41 => {
                return v___x_1472_;
            }
            42 => {
                v_val_1482_ = crate::leanh::lean_ctor_get(v_a_1478_, 0);
                v_isSharedCheck_1493_ = (!crate::leanh::lean_is_exclusive(v_a_1478_)) as u8;
                if v_isSharedCheck_1493_ == 0 {
                    v___x_1484_ = v_a_1478_;
                    v_isShared_1485_ = v_isSharedCheck_1493_;
                    state = 43;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1482_);
                    crate::leanh::lean_dec(v_a_1478_);
                    v___x_1484_ = crate::leanh::lean_box(0);
                    v_isShared_1485_ = v_isSharedCheck_1493_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_1486_ = lean_int_ediv(v_val_1476_, v_val_1482_);
                crate::leanh::lean_dec(v_val_1482_);
                crate::leanh::lean_dec(v_val_1476_);
                if v_isShared_1485_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1484_, 0, v___x_1486_);
                    v___x_1488_ = v___x_1484_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_1492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
                    v___x_1488_ = v_reuseFailAlloc_1492_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_1481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1480_, 0, v___x_1488_);
                    v___x_1490_ = v___x_1480_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
                    v___x_1490_ = v_reuseFailAlloc_1491_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_1490_;
            }
            46 => {
                if v_isShared_1500_ == 0 {
                    v___x_1502_ = v___x_1499_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_1503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
                    v___x_1502_ = v_reuseFailAlloc_1503_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1502_;
            }
            48 => {
                v___x_1510_ = (crate::leanh::lean_unbox(v_a_1506_) as u8);
                crate::leanh::lean_dec(v_a_1506_);
                if v___x_1510_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1310_);
                    crate::leanh::lean_dec_ref(v_arg_1307_);
                    v___x_1511_ = crate::leanh::lean_box(0);
                    if v_isShared_1509_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1508_, 0, v___x_1511_);
                        v___x_1513_ = v___x_1508_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_1514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
                        v___x_1513_ = v_reuseFailAlloc_1514_;
                        state = 49;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1508_);
                    v___x_1515_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
                            v_arg_1310_,
                            v_a_1228_,
                            v_a_1229_,
                            v_a_1230_,
                            v_a_1231_,
                            v_a_1232_,
                            v_a_1233_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1515_) == 0 {
                        v_a_1516_ = crate::leanh::lean_ctor_get(v___x_1515_, 0);
                        crate::leanh::lean_inc(v_a_1516_);
                        if crate::leanh::lean_obj_tag(v_a_1516_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1307_);
                            return v___x_1515_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1515_, 1);
                            v_val_1517_ = crate::leanh::lean_ctor_get(v_a_1516_, 0);
                            crate::leanh::lean_inc(v_val_1517_);
                            crate::leanh::lean_dec_ref_known(v_a_1516_, 1);
                            v___x_1518_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_1307_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
                            if crate::leanh::lean_obj_tag(v___x_1518_) == 0 {
                                v_a_1519_ = crate::leanh::lean_ctor_get(v___x_1518_, 0);
                                crate::leanh::lean_inc(v_a_1519_);
                                if crate::leanh::lean_obj_tag(v_a_1519_) == 0 {
                                    crate::leanh::lean_dec(v_val_1517_);
                                    return v___x_1518_;
                                } else {
                                    v_isSharedCheck_1535_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1518_)) as u8;
                                    if v_isSharedCheck_1535_ == 0 {
                                        v_unused_1536_ =
                                            crate::leanh::lean_ctor_get(v___x_1518_, 0);
                                        crate::leanh::lean_dec(v_unused_1536_);
                                        v___x_1521_ = v___x_1518_;
                                        v_isShared_1522_ = v_isSharedCheck_1535_;
                                        state = 50;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1518_);
                                        v___x_1521_ = crate::leanh::lean_box(0);
                                        v_isShared_1522_ = v_isSharedCheck_1535_;
                                        state = 50;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1517_);
                                return v___x_1518_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1307_);
                        return v___x_1515_;
                    }
                }
            }
            49 => {
                return v___x_1513_;
            }
            50 => {
                v_val_1523_ = crate::leanh::lean_ctor_get(v_a_1519_, 0);
                v_isSharedCheck_1534_ = (!crate::leanh::lean_is_exclusive(v_a_1519_)) as u8;
                if v_isSharedCheck_1534_ == 0 {
                    v___x_1525_ = v_a_1519_;
                    v_isShared_1526_ = v_isSharedCheck_1534_;
                    state = 51;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1523_);
                    crate::leanh::lean_dec(v_a_1519_);
                    v___x_1525_ = crate::leanh::lean_box(0);
                    v_isShared_1526_ = v_isSharedCheck_1534_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                v___x_1527_ = lean_int_emod(v_val_1517_, v_val_1523_);
                crate::leanh::lean_dec(v_val_1523_);
                crate::leanh::lean_dec(v_val_1517_);
                if v_isShared_1526_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1527_);
                    v___x_1529_ = v___x_1525_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_1533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1527_);
                    v___x_1529_ = v_reuseFailAlloc_1533_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                if v_isShared_1522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1521_, 0, v___x_1529_);
                    v___x_1531_ = v___x_1521_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_1532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
                    v___x_1531_ = v_reuseFailAlloc_1532_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_1531_;
            }
            54 => {
                if v_isShared_1541_ == 0 {
                    v___x_1543_ = v___x_1540_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_1544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
                    v___x_1543_ = v_reuseFailAlloc_1544_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_1543_;
            }
            56 => {
                v___x_1551_ = (crate::leanh::lean_unbox(v_a_1547_) as u8);
                crate::leanh::lean_dec(v_a_1547_);
                if v___x_1551_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1310_);
                    crate::leanh::lean_dec_ref(v_arg_1307_);
                    v___x_1552_ = crate::leanh::lean_box(0);
                    if v_isShared_1550_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1549_, 0, v___x_1552_);
                        v___x_1554_ = v___x_1549_;
                        state = 57;
                        continue;
                    } else {
                        v_reuseFailAlloc_1555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
                        v___x_1554_ = v_reuseFailAlloc_1555_;
                        state = 57;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1549_);
                    v___x_1556_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
                            v_arg_1310_,
                            v_a_1228_,
                            v_a_1229_,
                            v_a_1230_,
                            v_a_1231_,
                            v_a_1232_,
                            v_a_1233_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1556_) == 0 {
                        v_a_1557_ = crate::leanh::lean_ctor_get(v___x_1556_, 0);
                        crate::leanh::lean_inc(v_a_1557_);
                        if crate::leanh::lean_obj_tag(v_a_1557_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1307_);
                            return v___x_1556_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1556_, 1);
                            v_val_1558_ = crate::leanh::lean_ctor_get(v_a_1557_, 0);
                            crate::leanh::lean_inc(v_val_1558_);
                            crate::leanh::lean_dec_ref_known(v_a_1557_, 1);
                            v___x_1559_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1307_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
                            if crate::leanh::lean_obj_tag(v___x_1559_) == 0 {
                                v_a_1560_ = crate::leanh::lean_ctor_get(v___x_1559_, 0);
                                v_isSharedCheck_1599_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1559_)) as u8;
                                if v_isSharedCheck_1599_ == 0 {
                                    v___x_1562_ = v___x_1559_;
                                    v_isShared_1563_ = v_isSharedCheck_1599_;
                                    state = 58;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1560_);
                                    crate::leanh::lean_dec(v___x_1559_);
                                    v___x_1562_ = crate::leanh::lean_box(0);
                                    v_isShared_1563_ = v_isSharedCheck_1599_;
                                    state = 58;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1558_);
                                v_a_1600_ = crate::leanh::lean_ctor_get(v___x_1559_, 0);
                                v_isSharedCheck_1607_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1559_)) as u8;
                                if v_isSharedCheck_1607_ == 0 {
                                    v___x_1602_ = v___x_1559_;
                                    v_isShared_1603_ = v_isSharedCheck_1607_;
                                    state = 67;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1600_);
                                    crate::leanh::lean_dec(v___x_1559_);
                                    v___x_1602_ = crate::leanh::lean_box(0);
                                    v_isShared_1603_ = v_isSharedCheck_1607_;
                                    state = 67;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1307_);
                        return v___x_1556_;
                    }
                }
            }
            57 => {
                return v___x_1554_;
            }
            58 => {
                if crate::leanh::lean_obj_tag(v_a_1560_) == 0 {
                    crate::leanh::lean_dec(v_val_1558_);
                    v___x_1564_ = crate::leanh::lean_box(0);
                    if v_isShared_1563_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1562_, 0, v___x_1564_);
                        v___x_1566_ = v___x_1562_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_1567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
                        v___x_1566_ = v_reuseFailAlloc_1567_;
                        state = 59;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1562_);
                    v_val_1568_ = crate::leanh::lean_ctor_get(v_a_1560_, 0);
                    crate::leanh::lean_inc_n(v_val_1568_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_1560_, 1);
                    v___x_1569_ = l_Lean_Meta_Sym_Arith_checkExp(
                        v_val_1568_,
                        v_a_1228_,
                        v_a_1229_,
                        v_a_1230_,
                        v_a_1231_,
                        v_a_1232_,
                        v_a_1233_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1569_) == 0 {
                        v_a_1570_ = crate::leanh::lean_ctor_get(v___x_1569_, 0);
                        v_isSharedCheck_1590_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1569_)) as u8;
                        if v_isSharedCheck_1590_ == 0 {
                            v___x_1572_ = v___x_1569_;
                            v_isShared_1573_ = v_isSharedCheck_1590_;
                            state = 60;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1570_);
                            crate::leanh::lean_dec(v___x_1569_);
                            v___x_1572_ = crate::leanh::lean_box(0);
                            v_isShared_1573_ = v_isSharedCheck_1590_;
                            state = 60;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1568_);
                        crate::leanh::lean_dec(v_val_1558_);
                        v_a_1591_ = crate::leanh::lean_ctor_get(v___x_1569_, 0);
                        v_isSharedCheck_1598_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1569_)) as u8;
                        if v_isSharedCheck_1598_ == 0 {
                            v___x_1593_ = v___x_1569_;
                            v_isShared_1594_ = v_isSharedCheck_1598_;
                            state = 65;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1591_);
                            crate::leanh::lean_dec(v___x_1569_);
                            v___x_1593_ = crate::leanh::lean_box(0);
                            v_isShared_1594_ = v_isSharedCheck_1598_;
                            state = 65;
                            continue;
                        }
                    }
                }
            }
            59 => {
                return v___x_1566_;
            }
            60 => {
                if crate::leanh::lean_obj_tag(v_a_1570_) == 0 {
                    crate::leanh::lean_dec(v_val_1568_);
                    crate::leanh::lean_dec(v_val_1558_);
                    v___x_1574_ = crate::leanh::lean_box(0);
                    if v_isShared_1573_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1572_, 0, v___x_1574_);
                        v___x_1576_ = v___x_1572_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_1577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
                        v___x_1576_ = v_reuseFailAlloc_1577_;
                        state = 61;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1588_ = (!crate::leanh::lean_is_exclusive(v_a_1570_)) as u8;
                    if v_isSharedCheck_1588_ == 0 {
                        v_unused_1589_ = crate::leanh::lean_ctor_get(v_a_1570_, 0);
                        crate::leanh::lean_dec(v_unused_1589_);
                        v___x_1579_ = v_a_1570_;
                        v_isShared_1580_ = v_isSharedCheck_1588_;
                        state = 62;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1570_);
                        v___x_1579_ = crate::leanh::lean_box(0);
                        v_isShared_1580_ = v_isSharedCheck_1588_;
                        state = 62;
                        continue;
                    }
                }
            }
            61 => {
                return v___x_1576_;
            }
            62 => {
                v___x_1581_ = l_Int_pow(v_val_1558_, v_val_1568_);
                crate::leanh::lean_dec(v_val_1568_);
                crate::leanh::lean_dec(v_val_1558_);
                if v_isShared_1580_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1579_, 0, v___x_1581_);
                    v___x_1583_ = v___x_1579_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_1587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1581_);
                    v___x_1583_ = v_reuseFailAlloc_1587_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v_isShared_1573_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1572_, 0, v___x_1583_);
                    v___x_1585_ = v___x_1572_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
                    v___x_1585_ = v_reuseFailAlloc_1586_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_1585_;
            }
            65 => {
                if v_isShared_1594_ == 0 {
                    v___x_1596_ = v___x_1593_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
                    v___x_1596_ = v_reuseFailAlloc_1597_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_1596_;
            }
            67 => {
                if v_isShared_1603_ == 0 {
                    v___x_1605_ = v___x_1602_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
                    v___x_1605_ = v_reuseFailAlloc_1606_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_1605_;
            }
            69 => {
                if v_isShared_1612_ == 0 {
                    v___x_1614_ = v___x_1611_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
                    v___x_1614_ = v_reuseFailAlloc_1615_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_1614_;
            }
            71 => {
                v___x_1622_ = (crate::leanh::lean_unbox(v_a_1618_) as u8);
                crate::leanh::lean_dec(v_a_1618_);
                if v___x_1622_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1307_);
                    v___x_1623_ = crate::leanh::lean_box(0);
                    if v_isShared_1621_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1623_);
                        v___x_1625_ = v___x_1620_;
                        state = 72;
                        continue;
                    } else {
                        v_reuseFailAlloc_1626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
                        v___x_1625_ = v_reuseFailAlloc_1626_;
                        state = 72;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1620_);
                    v___x_1627_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
                            v_arg_1307_,
                            v_a_1228_,
                            v_a_1229_,
                            v_a_1230_,
                            v_a_1231_,
                            v_a_1232_,
                            v_a_1233_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1627_) == 0 {
                        v_a_1628_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                        crate::leanh::lean_inc(v_a_1628_);
                        if crate::leanh::lean_obj_tag(v_a_1628_) == 0 {
                            return v___x_1627_;
                        } else {
                            v_isSharedCheck_1644_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1627_)) as u8;
                            if v_isSharedCheck_1644_ == 0 {
                                v_unused_1645_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                                crate::leanh::lean_dec(v_unused_1645_);
                                v___x_1630_ = v___x_1627_;
                                v_isShared_1631_ = v_isSharedCheck_1644_;
                                state = 73;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1627_);
                                v___x_1630_ = crate::leanh::lean_box(0);
                                v_isShared_1631_ = v_isSharedCheck_1644_;
                                state = 73;
                                continue;
                            }
                        }
                    } else {
                        return v___x_1627_;
                    }
                }
            }
            72 => {
                return v___x_1625_;
            }
            73 => {
                v_val_1632_ = crate::leanh::lean_ctor_get(v_a_1628_, 0);
                v_isSharedCheck_1643_ = (!crate::leanh::lean_is_exclusive(v_a_1628_)) as u8;
                if v_isSharedCheck_1643_ == 0 {
                    v___x_1634_ = v_a_1628_;
                    v_isShared_1635_ = v_isSharedCheck_1643_;
                    state = 74;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1632_);
                    crate::leanh::lean_dec(v_a_1628_);
                    v___x_1634_ = crate::leanh::lean_box(0);
                    v_isShared_1635_ = v_isSharedCheck_1643_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                v___x_1636_ = lean_int_neg(v_val_1632_);
                crate::leanh::lean_dec(v_val_1632_);
                if v_isShared_1635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1634_, 0, v___x_1636_);
                    v___x_1638_ = v___x_1634_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1636_);
                    v___x_1638_ = v_reuseFailAlloc_1642_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_1631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1630_, 0, v___x_1638_);
                    v___x_1640_ = v___x_1630_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_1641_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
                    v___x_1640_ = v_reuseFailAlloc_1641_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                return v___x_1640_;
            }
            77 => {
                if v_isShared_1650_ == 0 {
                    v___x_1652_ = v___x_1649_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_1653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
                    v___x_1652_ = v_reuseFailAlloc_1653_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                return v___x_1652_;
            }
            79 => {
                if v_isShared_1663_ == 0 {
                    v___x_1665_ = v___x_1662_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_1666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
                    v___x_1665_ = v_reuseFailAlloc_1666_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                return v___x_1665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
    mut v_e_1668_: *mut crate::leanh::LeanObject,
    mut v_a_1669_: *mut crate::leanh::LeanObject,
    mut v_a_1670_: *mut crate::leanh::LeanObject,
    mut v_a_1671_: *mut crate::leanh::LeanObject,
    mut v_a_1672_: *mut crate::leanh::LeanObject,
    mut v_a_1673_: *mut crate::leanh::LeanObject,
    mut v_a_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: u8 = 0;
    let mut v_arg_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: u8 = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: u8 = 0;
    let mut v_arg_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: u8 = 0;
    let mut v_arg_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: u8 = 0;
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: u8 = 0;
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v_val_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v_unused_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut v_a_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1762_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v_val_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut v_unused_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_a_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v_val_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v_unused_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut v_a_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1849_: u8 = 0;
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v_val_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut v_unused_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut v_a_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1891_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1903_: u8 = 0;
    let mut v_val_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut v_a_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v_val_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1957_: u8 = 0;
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_unused_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut v_a_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1976_: u8 = 0;
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut v_a_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1985_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v_val_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_isSharedCheck_2012_: u8 = 0;
    let mut v_unused_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2018_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v_a_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2039_: u8 = 0;
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2064_: u8 = 0;
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut v_a_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2078_: u8 = 0;
    let mut v_a_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1668_);
                v___x_1679_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1668_, v_a_1672_);
                if crate::leanh::lean_obj_tag(v___x_1679_) == 0 {
                    v_a_1680_ = crate::leanh::lean_ctor_get(v___x_1679_, 0);
                    v_isSharedCheck_2078_ = (!crate::leanh::lean_is_exclusive(v___x_1679_)) as u8;
                    if v_isSharedCheck_2078_ == 0 {
                        v___x_1682_ = v___x_1679_;
                        v_isShared_1683_ = v_isSharedCheck_2078_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1680_);
                        crate::leanh::lean_dec(v___x_1679_);
                        v___x_1682_ = crate::leanh::lean_box(0);
                        v_isShared_1683_ = v_isSharedCheck_2078_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1668_);
                    v_a_2079_ = crate::leanh::lean_ctor_get(v___x_1679_, 0);
                    v_isSharedCheck_2086_ = (!crate::leanh::lean_is_exclusive(v___x_1679_)) as u8;
                    if v_isSharedCheck_2086_ == 0 {
                        v___x_2081_ = v___x_1679_;
                        v_isShared_2082_ = v_isSharedCheck_2086_;
                        state = 76;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2079_);
                        crate::leanh::lean_dec(v___x_1679_);
                        v___x_2081_ = crate::leanh::lean_box(0);
                        v_isShared_2082_ = v_isSharedCheck_2086_;
                        state = 76;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1677_ = crate::leanh::lean_box(0);
                v___x_1678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                return v___x_1678_;
            }
            2 => {
                v___x_1684_ = l_Lean_Expr_cleanupAnnotations(v_a_1680_);
                v___x_1685_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2;
                v___x_1686_ = l_Lean_Expr_isConstOf(v___x_1684_, v___x_1685_);
                if v___x_1686_ == 0 {
                    v___x_1687_ = l_Lean_Expr_isApp(v___x_1684_);
                    if v___x_1687_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1684_);
                        crate::leanh::lean_del_object(v___x_1682_);
                        crate::leanh::lean_dec_ref(v_e_1668_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_1688_ = crate::leanh::lean_ctor_get(v___x_1684_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1688_);
                        v___x_1689_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1684_);
                        v___x_1690_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5;
                        v___x_1691_ = l_Lean_Expr_isConstOf(v___x_1689_, v___x_1690_);
                        if v___x_1691_ == 0 {
                            v___x_1692_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7;
                            v___x_1693_ = l_Lean_Expr_isConstOf(v___x_1689_, v___x_1692_);
                            if v___x_1693_ == 0 {
                                v___x_1694_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9;
                                v___x_1695_ = l_Lean_Expr_isConstOf(v___x_1689_, v___x_1694_);
                                if v___x_1695_ == 0 {
                                    v___x_1696_ = l_Lean_Expr_isApp(v___x_1689_);
                                    if v___x_1696_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_1689_);
                                        crate::leanh::lean_dec_ref(v_arg_1688_);
                                        crate::leanh::lean_del_object(v___x_1682_);
                                        crate::leanh::lean_dec_ref(v_e_1668_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_1697_ = crate::leanh::lean_ctor_get(v___x_1689_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_1697_);
                                        v___x_1698_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_1689_);
                                        v___x_1699_ = l_Lean_Expr_isApp(v___x_1698_);
                                        if v___x_1699_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_1698_);
                                            crate::leanh::lean_dec_ref(v_arg_1697_);
                                            crate::leanh::lean_dec_ref(v_arg_1688_);
                                            crate::leanh::lean_del_object(v___x_1682_);
                                            crate::leanh::lean_dec_ref(v_e_1668_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_1700_ =
                                                crate::leanh::lean_ctor_get(v___x_1698_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_1700_);
                                            v___x_1701_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_1698_);
                                            v___x_1702_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12;
                                            v___x_1703_ =
                                                l_Lean_Expr_isConstOf(v___x_1701_, v___x_1702_);
                                            if v___x_1703_ == 0 {
                                                crate::leanh::lean_del_object(v___x_1682_);
                                                crate::leanh::lean_dec_ref(v_e_1668_);
                                                v___x_1704_ = l_Lean_Expr_isApp(v___x_1701_);
                                                if v___x_1704_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_1701_);
                                                    crate::leanh::lean_dec_ref(v_arg_1700_);
                                                    crate::leanh::lean_dec_ref(v_arg_1697_);
                                                    crate::leanh::lean_dec_ref(v_arg_1688_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_1705_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1701_,
                                                    );
                                                    v___x_1706_ = l_Lean_Expr_isApp(v___x_1705_);
                                                    if v___x_1706_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_1705_);
                                                        crate::leanh::lean_dec_ref(v_arg_1700_);
                                                        crate::leanh::lean_dec_ref(v_arg_1697_);
                                                        crate::leanh::lean_dec_ref(v_arg_1688_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1707_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_1705_,
                                                            );
                                                        v___x_1708_ =
                                                            l_Lean_Expr_isApp(v___x_1707_);
                                                        if v___x_1708_ == 0 {
                                                            crate::leanh::lean_dec_ref(v___x_1707_);
                                                            crate::leanh::lean_dec_ref(v_arg_1700_);
                                                            crate::leanh::lean_dec_ref(v_arg_1697_);
                                                            crate::leanh::lean_dec_ref(v_arg_1688_);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_1709_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_1707_,
                                                                );
                                                            v___x_1710_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15;
                                                            v___x_1711_ = l_Lean_Expr_isConstOf(
                                                                v___x_1709_,
                                                                v___x_1710_,
                                                            );
                                                            if v___x_1711_ == 0 {
                                                                v___x_1712_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18;
                                                                v___x_1713_ = l_Lean_Expr_isConstOf(
                                                                    v___x_1709_,
                                                                    v___x_1712_,
                                                                );
                                                                if v___x_1713_ == 0 {
                                                                    v___x_1714_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21;
                                                                    v___x_1715_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_1709_,
                                                                            v___x_1714_,
                                                                        );
                                                                    if v___x_1715_ == 0 {
                                                                        v___x_1716_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24;
                                                                        v___x_1717_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_1709_,
                                                                                v___x_1716_,
                                                                            );
                                                                        if v___x_1717_ == 0 {
                                                                            v___x_1718_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27;
                                                                            v___x_1719_ = l_Lean_Expr_isConstOf(v___x_1709_, v___x_1718_);
                                                                            if v___x_1719_ == 0 {
                                                                                v___x_1720_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30;
                                                                                v___x_1721_ = l_Lean_Expr_isConstOf(v___x_1709_, v___x_1720_);
                                                                                crate::leanh::lean_dec_ref(v___x_1709_);
                                                                                if v___x_1721_ == 0
                                                                                {
                                                                                    crate::leanh::lean_dec_ref(v_arg_1700_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_1697_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_1688_);
                                                                                    state = 1;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_1722_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_1700_, v_a_1672_);
                                                                                    if crate::leanh::lean_obj_tag(v___x_1722_) == 0 {
v_a_1723_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1754_ = (!crate::leanh::lean_is_exclusive(v___x_1722_)) as u8;
if v_isSharedCheck_1754_ == 0 {
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1754_;
state = 3; continue;
} else {
crate::leanh::lean_inc(v_a_1723_);
crate::leanh::lean_dec(v___x_1722_);
v___x_1725_ = crate::leanh::lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1754_;
state = 3; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1697_);
crate::leanh::lean_dec_ref(v_arg_1688_);
v_a_1755_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1762_ = (!crate::leanh::lean_is_exclusive(v___x_1722_)) as u8;
if v_isSharedCheck_1762_ == 0 {
v___x_1757_ = v___x_1722_;
v_isShared_1758_ = v_isSharedCheck_1762_;
state = 9; continue;
} else {
crate::leanh::lean_inc(v_a_1755_);
crate::leanh::lean_dec(v___x_1722_);
v___x_1757_ = crate::leanh::lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
state = 9; continue;
}
}
                                                                                }
                                                                            } else {
                                                                                crate::leanh::lean_dec_ref(v___x_1709_);
                                                                                v___x_1763_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_1700_, v_a_1672_);
                                                                                if crate::leanh::lean_obj_tag(v___x_1763_) == 0 {
v_a_1764_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1795_ = (!crate::leanh::lean_is_exclusive(v___x_1763_)) as u8;
if v_isSharedCheck_1795_ == 0 {
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1795_;
state = 11; continue;
} else {
crate::leanh::lean_inc(v_a_1764_);
crate::leanh::lean_dec(v___x_1763_);
v___x_1766_ = crate::leanh::lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1795_;
state = 11; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1697_);
crate::leanh::lean_dec_ref(v_arg_1688_);
v_a_1796_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1803_ = (!crate::leanh::lean_is_exclusive(v___x_1763_)) as u8;
if v_isSharedCheck_1803_ == 0 {
v___x_1798_ = v___x_1763_;
v_isShared_1799_ = v_isSharedCheck_1803_;
state = 17; continue;
} else {
crate::leanh::lean_inc(v_a_1796_);
crate::leanh::lean_dec(v___x_1763_);
v___x_1798_ = crate::leanh::lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
state = 17; continue;
}
}
                                                                            }
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v___x_1709_);
                                                                            v___x_1804_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_1700_, v_a_1672_);
                                                                            if crate::leanh::lean_obj_tag(v___x_1804_) == 0 {
v_a_1805_ = crate::leanh::lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1836_ = (!crate::leanh::lean_is_exclusive(v___x_1804_)) as u8;
if v_isSharedCheck_1836_ == 0 {
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1836_;
state = 19; continue;
} else {
crate::leanh::lean_inc(v_a_1805_);
crate::leanh::lean_dec(v___x_1804_);
v___x_1807_ = crate::leanh::lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1836_;
state = 19; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1697_);
crate::leanh::lean_dec_ref(v_arg_1688_);
v_a_1837_ = crate::leanh::lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1844_ = (!crate::leanh::lean_is_exclusive(v___x_1804_)) as u8;
if v_isSharedCheck_1844_ == 0 {
v___x_1839_ = v___x_1804_;
v_isShared_1840_ = v_isSharedCheck_1844_;
state = 25; continue;
} else {
crate::leanh::lean_inc(v_a_1837_);
crate::leanh::lean_dec(v___x_1804_);
v___x_1839_ = crate::leanh::lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
state = 25; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_1709_,
                                                                        );
                                                                        v___x_1845_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_1700_, v_a_1672_);
                                                                        if crate::leanh::lean_obj_tag(v___x_1845_) == 0 {
v_a_1846_ = crate::leanh::lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1877_ = (!crate::leanh::lean_is_exclusive(v___x_1845_)) as u8;
if v_isSharedCheck_1877_ == 0 {
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1877_;
state = 27; continue;
} else {
crate::leanh::lean_inc(v_a_1846_);
crate::leanh::lean_dec(v___x_1845_);
v___x_1848_ = crate::leanh::lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1877_;
state = 27; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1697_);
crate::leanh::lean_dec_ref(v_arg_1688_);
v_a_1878_ = crate::leanh::lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1885_ = (!crate::leanh::lean_is_exclusive(v___x_1845_)) as u8;
if v_isSharedCheck_1885_ == 0 {
v___x_1880_ = v___x_1845_;
v_isShared_1881_ = v_isSharedCheck_1885_;
state = 33; continue;
} else {
crate::leanh::lean_inc(v_a_1878_);
crate::leanh::lean_dec(v___x_1845_);
v___x_1880_ = crate::leanh::lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
state = 33; continue;
}
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_1709_,
                                                                    );
                                                                    v___x_1886_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_1700_, v_a_1672_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_1886_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_1887_ = crate::leanh::lean_ctor_get(v___x_1886_, 0);
                                                                        v_isSharedCheck_1918_ = (!crate::leanh::lean_is_exclusive(v___x_1886_)) as u8;
                                                                        if v_isSharedCheck_1918_
                                                                            == 0
                                                                        {
                                                                            v___x_1889_ =
                                                                                v___x_1886_;
                                                                            v_isShared_1890_ = v_isSharedCheck_1918_;
                                                                            state = 35;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_1887_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1886_,
                                                                            );
                                                                            v___x_1889_ = crate::leanh::lean_box(0);
                                                                            v_isShared_1890_ = v_isSharedCheck_1918_;
                                                                            state = 35;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1697_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1688_,
                                                                        );
                                                                        v_a_1919_ = crate::leanh::lean_ctor_get(v___x_1886_, 0);
                                                                        v_isSharedCheck_1926_ = (!crate::leanh::lean_is_exclusive(v___x_1886_)) as u8;
                                                                        if v_isSharedCheck_1926_
                                                                            == 0
                                                                        {
                                                                            v___x_1921_ =
                                                                                v___x_1886_;
                                                                            v_isShared_1922_ = v_isSharedCheck_1926_;
                                                                            state = 41;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_1919_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1886_,
                                                                            );
                                                                            v___x_1921_ = crate::leanh::lean_box(0);
                                                                            v_isShared_1922_ = v_isSharedCheck_1926_;
                                                                            state = 41;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_1709_,
                                                                );
                                                                v___x_1927_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_1700_, v_a_1672_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_1927_,
                                                                ) == 0
                                                                {
                                                                    v_a_1928_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1927_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1977_ = (!crate::leanh::lean_is_exclusive(v___x_1927_)) as u8;
                                                                    if v_isSharedCheck_1977_ == 0 {
                                                                        v___x_1930_ = v___x_1927_;
                                                                        v_isShared_1931_ =
                                                                            v_isSharedCheck_1977_;
                                                                        state = 43;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1928_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1927_,
                                                                        );
                                                                        v___x_1930_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1931_ =
                                                                            v_isSharedCheck_1977_;
                                                                        state = 43;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1697_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1688_,
                                                                    );
                                                                    v_a_1978_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1927_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1985_ = (!crate::leanh::lean_is_exclusive(v___x_1927_)) as u8;
                                                                    if v_isSharedCheck_1985_ == 0 {
                                                                        v___x_1980_ = v___x_1927_;
                                                                        v_isShared_1981_ =
                                                                            v_isSharedCheck_1985_;
                                                                        state = 53;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1978_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1927_,
                                                                        );
                                                                        v___x_1980_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1981_ =
                                                                            v_isSharedCheck_1985_;
                                                                        state = 53;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_1701_);
                                                crate::leanh::lean_dec_ref(v_arg_1700_);
                                                crate::leanh::lean_dec_ref(v_arg_1697_);
                                                crate::leanh::lean_dec_ref(v_arg_1688_);
                                                v___x_1986_ =
                                                    l_Lean_Meta_Sym_getNatValue_x3f(v_e_1668_);
                                                if crate::leanh::lean_obj_tag(v___x_1986_) == 1 {
                                                    if v_isShared_1683_ == 0 {
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_1682_,
                                                            0,
                                                            v___x_1986_,
                                                        );
                                                        v___x_1988_ = v___x_1682_;
                                                        state = 55;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_1989_ =
                                                            crate::leanh::lean_alloc_ctor(
                                                                0,
                                                                1,
                                                                (0) as u32,
                                                            );
                                                        crate::leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_1989_,
                                                            0,
                                                            v___x_1986_,
                                                        );
                                                        v___x_1988_ = v_reuseFailAlloc_1989_;
                                                        state = 55;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v___x_1986_);
                                                    v___x_1990_ = crate::leanh::lean_box(0);
                                                    if v_isShared_1683_ == 0 {
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_1682_,
                                                            0,
                                                            v___x_1990_,
                                                        );
                                                        v___x_1992_ = v___x_1682_;
                                                        state = 56;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_1993_ =
                                                            crate::leanh::lean_alloc_ctor(
                                                                0,
                                                                1,
                                                                (0) as u32,
                                                            );
                                                        crate::leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_1993_,
                                                            0,
                                                            v___x_1990_,
                                                        );
                                                        v___x_1992_ = v_reuseFailAlloc_1993_;
                                                        state = 56;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_1689_);
                                    crate::leanh::lean_del_object(v___x_1682_);
                                    crate::leanh::lean_dec_ref(v_e_1668_);
                                    v___x_1994_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1688_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
                                    if crate::leanh::lean_obj_tag(v___x_1994_) == 0 {
                                        v_a_1995_ = crate::leanh::lean_ctor_get(v___x_1994_, 0);
                                        crate::leanh::lean_inc(v_a_1995_);
                                        if crate::leanh::lean_obj_tag(v_a_1995_) == 0 {
                                            return v___x_1994_;
                                        } else {
                                            v_isSharedCheck_2012_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1994_))
                                                    as u8;
                                            if v_isSharedCheck_2012_ == 0 {
                                                v_unused_2013_ =
                                                    crate::leanh::lean_ctor_get(v___x_1994_, 0);
                                                crate::leanh::lean_dec(v_unused_2013_);
                                                v___x_1997_ = v___x_1994_;
                                                v_isShared_1998_ = v_isSharedCheck_2012_;
                                                state = 57;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_1994_);
                                                v___x_1997_ = crate::leanh::lean_box(0);
                                                v_isShared_1998_ = v_isSharedCheck_2012_;
                                                state = 57;
                                                continue;
                                            }
                                        }
                                    } else {
                                        return v___x_1994_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1689_);
                                crate::leanh::lean_del_object(v___x_1682_);
                                crate::leanh::lean_dec_ref(v_e_1668_);
                                v___x_2014_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_1688_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
                                if crate::leanh::lean_obj_tag(v___x_2014_) == 0 {
                                    v_a_2015_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
                                    v_isSharedCheck_2035_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2014_)) as u8;
                                    if v_isSharedCheck_2035_ == 0 {
                                        v___x_2017_ = v___x_2014_;
                                        v_isShared_2018_ = v_isSharedCheck_2035_;
                                        state = 61;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2015_);
                                        crate::leanh::lean_dec(v___x_2014_);
                                        v___x_2017_ = crate::leanh::lean_box(0);
                                        v_isShared_2018_ = v_isSharedCheck_2035_;
                                        state = 61;
                                        continue;
                                    }
                                } else {
                                    v_a_2036_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
                                    v_isSharedCheck_2043_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2014_)) as u8;
                                    if v_isSharedCheck_2043_ == 0 {
                                        v___x_2038_ = v___x_2014_;
                                        v_isShared_2039_ = v_isSharedCheck_2043_;
                                        state = 66;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2036_);
                                        crate::leanh::lean_dec(v___x_2014_);
                                        v___x_2038_ = crate::leanh::lean_box(0);
                                        v_isShared_2039_ = v_isSharedCheck_2043_;
                                        state = 66;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1689_);
                            crate::leanh::lean_del_object(v___x_1682_);
                            crate::leanh::lean_dec_ref(v_e_1668_);
                            v___x_2044_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_1688_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
                            if crate::leanh::lean_obj_tag(v___x_2044_) == 0 {
                                v_a_2045_ = crate::leanh::lean_ctor_get(v___x_2044_, 0);
                                v_isSharedCheck_2065_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2044_)) as u8;
                                if v_isSharedCheck_2065_ == 0 {
                                    v___x_2047_ = v___x_2044_;
                                    v_isShared_2048_ = v_isSharedCheck_2065_;
                                    state = 68;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2045_);
                                    crate::leanh::lean_dec(v___x_2044_);
                                    v___x_2047_ = crate::leanh::lean_box(0);
                                    v_isShared_2048_ = v_isSharedCheck_2065_;
                                    state = 68;
                                    continue;
                                }
                            } else {
                                v_a_2066_ = crate::leanh::lean_ctor_get(v___x_2044_, 0);
                                v_isSharedCheck_2073_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2044_)) as u8;
                                if v_isSharedCheck_2073_ == 0 {
                                    v___x_2068_ = v___x_2044_;
                                    v_isShared_2069_ = v_isSharedCheck_2073_;
                                    state = 73;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2066_);
                                    crate::leanh::lean_dec(v___x_2044_);
                                    v___x_2068_ = crate::leanh::lean_box(0);
                                    v_isShared_2069_ = v_isSharedCheck_2073_;
                                    state = 73;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1684_);
                    crate::leanh::lean_dec_ref(v_e_1668_);
                    v___x_2074_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31;
                    if v_isShared_1683_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_2074_);
                        v___x_2076_ = v___x_1682_;
                        state = 75;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 75;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1727_ = (crate::leanh::lean_unbox(v_a_1723_) as u8);
                crate::leanh::lean_dec(v_a_1723_);
                if v___x_1727_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1697_);
                    crate::leanh::lean_dec_ref(v_arg_1688_);
                    v___x_1728_ = crate::leanh::lean_box(0);
                    if v_isShared_1726_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1728_);
                        v___x_1730_ = v___x_1725_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1731_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
                        v___x_1730_ = v_reuseFailAlloc_1731_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1725_);
                    v___x_1732_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
                            v_arg_1697_,
                            v_a_1669_,
                            v_a_1670_,
                            v_a_1671_,
                            v_a_1672_,
                            v_a_1673_,
                            v_a_1674_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1732_) == 0 {
                        v_a_1733_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                        crate::leanh::lean_inc(v_a_1733_);
                        if crate::leanh::lean_obj_tag(v_a_1733_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1688_);
                            return v___x_1732_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1732_, 1);
                            v_val_1734_ = crate::leanh::lean_ctor_get(v_a_1733_, 0);
                            crate::leanh::lean_inc(v_val_1734_);
                            crate::leanh::lean_dec_ref_known(v_a_1733_, 1);
                            v___x_1735_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1688_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
                            if crate::leanh::lean_obj_tag(v___x_1735_) == 0 {
                                v_a_1736_ = crate::leanh::lean_ctor_get(v___x_1735_, 0);
                                crate::leanh::lean_inc(v_a_1736_);
                                if crate::leanh::lean_obj_tag(v_a_1736_) == 0 {
                                    crate::leanh::lean_dec(v_val_1734_);
                                    return v___x_1735_;
                                } else {
                                    v_isSharedCheck_1752_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1735_)) as u8;
                                    if v_isSharedCheck_1752_ == 0 {
                                        v_unused_1753_ =
                                            crate::leanh::lean_ctor_get(v___x_1735_, 0);
                                        crate::leanh::lean_dec(v_unused_1753_);
                                        v___x_1738_ = v___x_1735_;
                                        v_isShared_1739_ = v_isSharedCheck_1752_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1735_);
                                        v___x_1738_ = crate::leanh::lean_box(0);
                                        v_isShared_1739_ = v_isSharedCheck_1752_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1734_);
                                return v___x_1735_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1688_);
                        return v___x_1732_;
                    }
                }
            }
            4 => {
                return v___x_1730_;
            }
            5 => {
                v_val_1740_ = crate::leanh::lean_ctor_get(v_a_1736_, 0);
                v_isSharedCheck_1751_ = (!crate::leanh::lean_is_exclusive(v_a_1736_)) as u8;
                if v_isSharedCheck_1751_ == 0 {
                    v___x_1742_ = v_a_1736_;
                    v_isShared_1743_ = v_isSharedCheck_1751_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1740_);
                    crate::leanh::lean_dec(v_a_1736_);
                    v___x_1742_ = crate::leanh::lean_box(0);
                    v_isShared_1743_ = v_isSharedCheck_1751_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1744_ = lean_nat_add(v_val_1734_, v_val_1740_);
                crate::leanh::lean_dec(v_val_1740_);
                crate::leanh::lean_dec(v_val_1734_);
                if v_isShared_1743_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1742_, 0, v___x_1744_);
                    v___x_1746_ = v___x_1742_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1744_);
                    v___x_1746_ = v_reuseFailAlloc_1750_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1739_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1738_, 0, v___x_1746_);
                    v___x_1748_ = v___x_1738_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1748_;
            }
            9 => {
                if v_isShared_1758_ == 0 {
                    v___x_1760_ = v___x_1757_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
                    v___x_1760_ = v_reuseFailAlloc_1761_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1760_;
            }
            11 => {
                v___x_1768_ = (crate::leanh::lean_unbox(v_a_1764_) as u8);
                crate::leanh::lean_dec(v_a_1764_);
                if v___x_1768_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1697_);
                    crate::leanh::lean_dec_ref(v_arg_1688_);
                    v___x_1769_ = crate::leanh::lean_box(0);
                    if v_isShared_1767_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1769_);
                        v___x_1771_ = v___x_1766_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
                        v___x_1771_ = v_reuseFailAlloc_1772_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1766_);
                    v___x_1773_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
                            v_arg_1697_,
                            v_a_1669_,
                            v_a_1670_,
                            v_a_1671_,
                            v_a_1672_,
                            v_a_1673_,
                            v_a_1674_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1773_) == 0 {
                        v_a_1774_ = crate::leanh::lean_ctor_get(v___x_1773_, 0);
                        crate::leanh::lean_inc(v_a_1774_);
                        if crate::leanh::lean_obj_tag(v_a_1774_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1688_);
                            return v___x_1773_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1773_, 1);
                            v_val_1775_ = crate::leanh::lean_ctor_get(v_a_1774_, 0);
                            crate::leanh::lean_inc(v_val_1775_);
                            crate::leanh::lean_dec_ref_known(v_a_1774_, 1);
                            v___x_1776_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1688_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
                            if crate::leanh::lean_obj_tag(v___x_1776_) == 0 {
                                v_a_1777_ = crate::leanh::lean_ctor_get(v___x_1776_, 0);
                                crate::leanh::lean_inc(v_a_1777_);
                                if crate::leanh::lean_obj_tag(v_a_1777_) == 0 {
                                    crate::leanh::lean_dec(v_val_1775_);
                                    return v___x_1776_;
                                } else {
                                    v_isSharedCheck_1793_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1776_)) as u8;
                                    if v_isSharedCheck_1793_ == 0 {
                                        v_unused_1794_ =
                                            crate::leanh::lean_ctor_get(v___x_1776_, 0);
                                        crate::leanh::lean_dec(v_unused_1794_);
                                        v___x_1779_ = v___x_1776_;
                                        v_isShared_1780_ = v_isSharedCheck_1793_;
                                        state = 13;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1776_);
                                        v___x_1779_ = crate::leanh::lean_box(0);
                                        v_isShared_1780_ = v_isSharedCheck_1793_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1775_);
                                return v___x_1776_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1688_);
                        return v___x_1773_;
                    }
                }
            }
            12 => {
                return v___x_1771_;
            }
            13 => {
                v_val_1781_ = crate::leanh::lean_ctor_get(v_a_1777_, 0);
                v_isSharedCheck_1792_ = (!crate::leanh::lean_is_exclusive(v_a_1777_)) as u8;
                if v_isSharedCheck_1792_ == 0 {
                    v___x_1783_ = v_a_1777_;
                    v_isShared_1784_ = v_isSharedCheck_1792_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1781_);
                    crate::leanh::lean_dec(v_a_1777_);
                    v___x_1783_ = crate::leanh::lean_box(0);
                    v_isShared_1784_ = v_isSharedCheck_1792_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1785_ = lean_nat_mul(v_val_1775_, v_val_1781_);
                crate::leanh::lean_dec(v_val_1781_);
                crate::leanh::lean_dec(v_val_1775_);
                if v_isShared_1784_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1783_, 0, v___x_1785_);
                    v___x_1787_ = v___x_1783_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1785_);
                    v___x_1787_ = v_reuseFailAlloc_1791_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1779_, 0, v___x_1787_);
                    v___x_1789_ = v___x_1779_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
                    v___x_1789_ = v_reuseFailAlloc_1790_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1789_;
            }
            17 => {
                if v_isShared_1799_ == 0 {
                    v___x_1801_ = v___x_1798_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
                    v___x_1801_ = v_reuseFailAlloc_1802_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1801_;
            }
            19 => {
                v___x_1809_ = (crate::leanh::lean_unbox(v_a_1805_) as u8);
                crate::leanh::lean_dec(v_a_1805_);
                if v___x_1809_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1697_);
                    crate::leanh::lean_dec_ref(v_arg_1688_);
                    v___x_1810_ = crate::leanh::lean_box(0);
                    if v_isShared_1808_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1807_, 0, v___x_1810_);
                        v___x_1812_ = v___x_1807_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
                        v___x_1812_ = v_reuseFailAlloc_1813_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1807_);
                    v___x_1814_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
                            v_arg_1697_,
                            v_a_1669_,
                            v_a_1670_,
                            v_a_1671_,
                            v_a_1672_,
                            v_a_1673_,
                            v_a_1674_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1814_) == 0 {
                        v_a_1815_ = crate::leanh::lean_ctor_get(v___x_1814_, 0);
                        crate::leanh::lean_inc(v_a_1815_);
                        if crate::leanh::lean_obj_tag(v_a_1815_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1688_);
                            return v___x_1814_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1814_, 1);
                            v_val_1816_ = crate::leanh::lean_ctor_get(v_a_1815_, 0);
                            crate::leanh::lean_inc(v_val_1816_);
                            crate::leanh::lean_dec_ref_known(v_a_1815_, 1);
                            v___x_1817_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1688_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
                            if crate::leanh::lean_obj_tag(v___x_1817_) == 0 {
                                v_a_1818_ = crate::leanh::lean_ctor_get(v___x_1817_, 0);
                                crate::leanh::lean_inc(v_a_1818_);
                                if crate::leanh::lean_obj_tag(v_a_1818_) == 0 {
                                    crate::leanh::lean_dec(v_val_1816_);
                                    return v___x_1817_;
                                } else {
                                    v_isSharedCheck_1834_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1817_)) as u8;
                                    if v_isSharedCheck_1834_ == 0 {
                                        v_unused_1835_ =
                                            crate::leanh::lean_ctor_get(v___x_1817_, 0);
                                        crate::leanh::lean_dec(v_unused_1835_);
                                        v___x_1820_ = v___x_1817_;
                                        v_isShared_1821_ = v_isSharedCheck_1834_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1817_);
                                        v___x_1820_ = crate::leanh::lean_box(0);
                                        v_isShared_1821_ = v_isSharedCheck_1834_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1816_);
                                return v___x_1817_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1688_);
                        return v___x_1814_;
                    }
                }
            }
            20 => {
                return v___x_1812_;
            }
            21 => {
                v_val_1822_ = crate::leanh::lean_ctor_get(v_a_1818_, 0);
                v_isSharedCheck_1833_ = (!crate::leanh::lean_is_exclusive(v_a_1818_)) as u8;
                if v_isSharedCheck_1833_ == 0 {
                    v___x_1824_ = v_a_1818_;
                    v_isShared_1825_ = v_isSharedCheck_1833_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1822_);
                    crate::leanh::lean_dec(v_a_1818_);
                    v___x_1824_ = crate::leanh::lean_box(0);
                    v_isShared_1825_ = v_isSharedCheck_1833_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1826_ = lean_nat_sub(v_val_1816_, v_val_1822_);
                crate::leanh::lean_dec(v_val_1822_);
                crate::leanh::lean_dec(v_val_1816_);
                if v_isShared_1825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1824_, 0, v___x_1826_);
                    v___x_1828_ = v___x_1824_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1826_);
                    v___x_1828_ = v_reuseFailAlloc_1832_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1828_);
                    v___x_1830_ = v___x_1820_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
                    v___x_1830_ = v_reuseFailAlloc_1831_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1830_;
            }
            25 => {
                if v_isShared_1840_ == 0 {
                    v___x_1842_ = v___x_1839_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
                    v___x_1842_ = v_reuseFailAlloc_1843_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1842_;
            }
            27 => {
                v___x_1850_ = (crate::leanh::lean_unbox(v_a_1846_) as u8);
                crate::leanh::lean_dec(v_a_1846_);
                if v___x_1850_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1697_);
                    crate::leanh::lean_dec_ref(v_arg_1688_);
                    v___x_1851_ = crate::leanh::lean_box(0);
                    if v_isShared_1849_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1848_, 0, v___x_1851_);
                        v___x_1853_ = v___x_1848_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_1854_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
                        v___x_1853_ = v_reuseFailAlloc_1854_;
                        state = 28;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1848_);
                    v___x_1855_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
                            v_arg_1697_,
                            v_a_1669_,
                            v_a_1670_,
                            v_a_1671_,
                            v_a_1672_,
                            v_a_1673_,
                            v_a_1674_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1855_) == 0 {
                        v_a_1856_ = crate::leanh::lean_ctor_get(v___x_1855_, 0);
                        crate::leanh::lean_inc(v_a_1856_);
                        if crate::leanh::lean_obj_tag(v_a_1856_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1688_);
                            return v___x_1855_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1855_, 1);
                            v_val_1857_ = crate::leanh::lean_ctor_get(v_a_1856_, 0);
                            crate::leanh::lean_inc(v_val_1857_);
                            crate::leanh::lean_dec_ref_known(v_a_1856_, 1);
                            v___x_1858_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1688_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
                            if crate::leanh::lean_obj_tag(v___x_1858_) == 0 {
                                v_a_1859_ = crate::leanh::lean_ctor_get(v___x_1858_, 0);
                                crate::leanh::lean_inc(v_a_1859_);
                                if crate::leanh::lean_obj_tag(v_a_1859_) == 0 {
                                    crate::leanh::lean_dec(v_val_1857_);
                                    return v___x_1858_;
                                } else {
                                    v_isSharedCheck_1875_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1858_)) as u8;
                                    if v_isSharedCheck_1875_ == 0 {
                                        v_unused_1876_ =
                                            crate::leanh::lean_ctor_get(v___x_1858_, 0);
                                        crate::leanh::lean_dec(v_unused_1876_);
                                        v___x_1861_ = v___x_1858_;
                                        v_isShared_1862_ = v_isSharedCheck_1875_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1858_);
                                        v___x_1861_ = crate::leanh::lean_box(0);
                                        v_isShared_1862_ = v_isSharedCheck_1875_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1857_);
                                return v___x_1858_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1688_);
                        return v___x_1855_;
                    }
                }
            }
            28 => {
                return v___x_1853_;
            }
            29 => {
                v_val_1863_ = crate::leanh::lean_ctor_get(v_a_1859_, 0);
                v_isSharedCheck_1874_ = (!crate::leanh::lean_is_exclusive(v_a_1859_)) as u8;
                if v_isSharedCheck_1874_ == 0 {
                    v___x_1865_ = v_a_1859_;
                    v_isShared_1866_ = v_isSharedCheck_1874_;
                    state = 30;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1863_);
                    crate::leanh::lean_dec(v_a_1859_);
                    v___x_1865_ = crate::leanh::lean_box(0);
                    v_isShared_1866_ = v_isSharedCheck_1874_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1867_ = lean_nat_div(v_val_1857_, v_val_1863_);
                crate::leanh::lean_dec(v_val_1863_);
                crate::leanh::lean_dec(v_val_1857_);
                if v_isShared_1866_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1865_, 0, v___x_1867_);
                    v___x_1869_ = v___x_1865_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1867_);
                    v___x_1869_ = v_reuseFailAlloc_1873_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_1862_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1861_, 0, v___x_1869_);
                    v___x_1871_ = v___x_1861_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
                    v___x_1871_ = v_reuseFailAlloc_1872_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1871_;
            }
            33 => {
                if v_isShared_1881_ == 0 {
                    v___x_1883_ = v___x_1880_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_1883_;
            }
            35 => {
                v___x_1891_ = (crate::leanh::lean_unbox(v_a_1887_) as u8);
                crate::leanh::lean_dec(v_a_1887_);
                if v___x_1891_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1697_);
                    crate::leanh::lean_dec_ref(v_arg_1688_);
                    v___x_1892_ = crate::leanh::lean_box(0);
                    if v_isShared_1890_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1889_, 0, v___x_1892_);
                        v___x_1894_ = v___x_1889_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_1895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
                        v___x_1894_ = v_reuseFailAlloc_1895_;
                        state = 36;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1889_);
                    v___x_1896_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
                            v_arg_1697_,
                            v_a_1669_,
                            v_a_1670_,
                            v_a_1671_,
                            v_a_1672_,
                            v_a_1673_,
                            v_a_1674_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1896_) == 0 {
                        v_a_1897_ = crate::leanh::lean_ctor_get(v___x_1896_, 0);
                        crate::leanh::lean_inc(v_a_1897_);
                        if crate::leanh::lean_obj_tag(v_a_1897_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1688_);
                            return v___x_1896_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1896_, 1);
                            v_val_1898_ = crate::leanh::lean_ctor_get(v_a_1897_, 0);
                            crate::leanh::lean_inc(v_val_1898_);
                            crate::leanh::lean_dec_ref_known(v_a_1897_, 1);
                            v___x_1899_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1688_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
                            if crate::leanh::lean_obj_tag(v___x_1899_) == 0 {
                                v_a_1900_ = crate::leanh::lean_ctor_get(v___x_1899_, 0);
                                crate::leanh::lean_inc(v_a_1900_);
                                if crate::leanh::lean_obj_tag(v_a_1900_) == 0 {
                                    crate::leanh::lean_dec(v_val_1898_);
                                    return v___x_1899_;
                                } else {
                                    v_isSharedCheck_1916_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1899_)) as u8;
                                    if v_isSharedCheck_1916_ == 0 {
                                        v_unused_1917_ =
                                            crate::leanh::lean_ctor_get(v___x_1899_, 0);
                                        crate::leanh::lean_dec(v_unused_1917_);
                                        v___x_1902_ = v___x_1899_;
                                        v_isShared_1903_ = v_isSharedCheck_1916_;
                                        state = 37;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1899_);
                                        v___x_1902_ = crate::leanh::lean_box(0);
                                        v_isShared_1903_ = v_isSharedCheck_1916_;
                                        state = 37;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1898_);
                                return v___x_1899_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1688_);
                        return v___x_1896_;
                    }
                }
            }
            36 => {
                return v___x_1894_;
            }
            37 => {
                v_val_1904_ = crate::leanh::lean_ctor_get(v_a_1900_, 0);
                v_isSharedCheck_1915_ = (!crate::leanh::lean_is_exclusive(v_a_1900_)) as u8;
                if v_isSharedCheck_1915_ == 0 {
                    v___x_1906_ = v_a_1900_;
                    v_isShared_1907_ = v_isSharedCheck_1915_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1904_);
                    crate::leanh::lean_dec(v_a_1900_);
                    v___x_1906_ = crate::leanh::lean_box(0);
                    v_isShared_1907_ = v_isSharedCheck_1915_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_1908_ = lean_nat_mod(v_val_1898_, v_val_1904_);
                crate::leanh::lean_dec(v_val_1904_);
                crate::leanh::lean_dec(v_val_1898_);
                if v_isShared_1907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1908_);
                    v___x_1910_ = v___x_1906_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1908_);
                    v___x_1910_ = v_reuseFailAlloc_1914_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_1903_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1902_, 0, v___x_1910_);
                    v___x_1912_ = v___x_1902_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
                    v___x_1912_ = v_reuseFailAlloc_1913_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_1912_;
            }
            41 => {
                if v_isShared_1922_ == 0 {
                    v___x_1924_ = v___x_1921_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
                    v___x_1924_ = v_reuseFailAlloc_1925_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_1924_;
            }
            43 => {
                v___x_1932_ = (crate::leanh::lean_unbox(v_a_1928_) as u8);
                crate::leanh::lean_dec(v_a_1928_);
                if v___x_1932_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1697_);
                    crate::leanh::lean_dec_ref(v_arg_1688_);
                    v___x_1933_ = crate::leanh::lean_box(0);
                    if v_isShared_1931_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1930_, 0, v___x_1933_);
                        v___x_1935_ = v___x_1930_;
                        state = 44;
                        continue;
                    } else {
                        v_reuseFailAlloc_1936_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
                        v___x_1935_ = v_reuseFailAlloc_1936_;
                        state = 44;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1930_);
                    v___x_1937_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
                            v_arg_1688_,
                            v_a_1669_,
                            v_a_1670_,
                            v_a_1671_,
                            v_a_1672_,
                            v_a_1673_,
                            v_a_1674_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1937_) == 0 {
                        v_a_1938_ = crate::leanh::lean_ctor_get(v___x_1937_, 0);
                        crate::leanh::lean_inc(v_a_1938_);
                        if crate::leanh::lean_obj_tag(v_a_1938_) == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1697_);
                            return v___x_1937_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1937_, 1);
                            v_val_1939_ = crate::leanh::lean_ctor_get(v_a_1938_, 0);
                            crate::leanh::lean_inc_n(v_val_1939_, 2);
                            crate::leanh::lean_dec_ref_known(v_a_1938_, 1);
                            v___x_1940_ = l_Lean_Meta_Sym_Arith_checkExp(
                                v_val_1939_,
                                v_a_1669_,
                                v_a_1670_,
                                v_a_1671_,
                                v_a_1672_,
                                v_a_1673_,
                                v_a_1674_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1940_) == 0 {
                                v_a_1941_ = crate::leanh::lean_ctor_get(v___x_1940_, 0);
                                v_isSharedCheck_1968_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1940_)) as u8;
                                if v_isSharedCheck_1968_ == 0 {
                                    v___x_1943_ = v___x_1940_;
                                    v_isShared_1944_ = v_isSharedCheck_1968_;
                                    state = 45;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1941_);
                                    crate::leanh::lean_dec(v___x_1940_);
                                    v___x_1943_ = crate::leanh::lean_box(0);
                                    v_isShared_1944_ = v_isSharedCheck_1968_;
                                    state = 45;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_1939_);
                                crate::leanh::lean_dec_ref(v_arg_1697_);
                                v_a_1969_ = crate::leanh::lean_ctor_get(v___x_1940_, 0);
                                v_isSharedCheck_1976_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1940_)) as u8;
                                if v_isSharedCheck_1976_ == 0 {
                                    v___x_1971_ = v___x_1940_;
                                    v_isShared_1972_ = v_isSharedCheck_1976_;
                                    state = 51;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1969_);
                                    crate::leanh::lean_dec(v___x_1940_);
                                    v___x_1971_ = crate::leanh::lean_box(0);
                                    v_isShared_1972_ = v_isSharedCheck_1976_;
                                    state = 51;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1697_);
                        return v___x_1937_;
                    }
                }
            }
            44 => {
                return v___x_1935_;
            }
            45 => {
                if crate::leanh::lean_obj_tag(v_a_1941_) == 0 {
                    crate::leanh::lean_dec(v_val_1939_);
                    crate::leanh::lean_dec_ref(v_arg_1697_);
                    v___x_1945_ = crate::leanh::lean_box(0);
                    if v_isShared_1944_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1945_);
                        v___x_1947_ = v___x_1943_;
                        state = 46;
                        continue;
                    } else {
                        v_reuseFailAlloc_1948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
                        v___x_1947_ = v_reuseFailAlloc_1948_;
                        state = 46;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_1941_, 1);
                    crate::leanh::lean_del_object(v___x_1943_);
                    v___x_1949_ =
                        l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
                            v_arg_1697_,
                            v_a_1669_,
                            v_a_1670_,
                            v_a_1671_,
                            v_a_1672_,
                            v_a_1673_,
                            v_a_1674_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1949_) == 0 {
                        v_a_1950_ = crate::leanh::lean_ctor_get(v___x_1949_, 0);
                        crate::leanh::lean_inc(v_a_1950_);
                        if crate::leanh::lean_obj_tag(v_a_1950_) == 0 {
                            crate::leanh::lean_dec(v_val_1939_);
                            return v___x_1949_;
                        } else {
                            v_isSharedCheck_1966_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1949_)) as u8;
                            if v_isSharedCheck_1966_ == 0 {
                                v_unused_1967_ = crate::leanh::lean_ctor_get(v___x_1949_, 0);
                                crate::leanh::lean_dec(v_unused_1967_);
                                v___x_1952_ = v___x_1949_;
                                v_isShared_1953_ = v_isSharedCheck_1966_;
                                state = 47;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1949_);
                                v___x_1952_ = crate::leanh::lean_box(0);
                                v_isShared_1953_ = v_isSharedCheck_1966_;
                                state = 47;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1939_);
                        return v___x_1949_;
                    }
                }
            }
            46 => {
                return v___x_1947_;
            }
            47 => {
                v_val_1954_ = crate::leanh::lean_ctor_get(v_a_1950_, 0);
                v_isSharedCheck_1965_ = (!crate::leanh::lean_is_exclusive(v_a_1950_)) as u8;
                if v_isSharedCheck_1965_ == 0 {
                    v___x_1956_ = v_a_1950_;
                    v_isShared_1957_ = v_isSharedCheck_1965_;
                    state = 48;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1954_);
                    crate::leanh::lean_dec(v_a_1950_);
                    v___x_1956_ = crate::leanh::lean_box(0);
                    v_isShared_1957_ = v_isSharedCheck_1965_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                v___x_1958_ = lean_nat_pow(v_val_1954_, v_val_1939_);
                crate::leanh::lean_dec(v_val_1939_);
                crate::leanh::lean_dec(v_val_1954_);
                if v_isShared_1957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1956_, 0, v___x_1958_);
                    v___x_1960_ = v___x_1956_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1958_);
                    v___x_1960_ = v_reuseFailAlloc_1964_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_1953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1952_, 0, v___x_1960_);
                    v___x_1962_ = v___x_1952_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_1963_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
                    v___x_1962_ = v_reuseFailAlloc_1963_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_1962_;
            }
            51 => {
                if v_isShared_1972_ == 0 {
                    v___x_1974_ = v___x_1971_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_1975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
                    v___x_1974_ = v_reuseFailAlloc_1975_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_1974_;
            }
            53 => {
                if v_isShared_1981_ == 0 {
                    v___x_1983_ = v___x_1980_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_1984_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
                    v___x_1983_ = v_reuseFailAlloc_1984_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_1983_;
            }
            55 => {
                return v___x_1988_;
            }
            56 => {
                return v___x_1992_;
            }
            57 => {
                v_val_1999_ = crate::leanh::lean_ctor_get(v_a_1995_, 0);
                v_isSharedCheck_2011_ = (!crate::leanh::lean_is_exclusive(v_a_1995_)) as u8;
                if v_isSharedCheck_2011_ == 0 {
                    v___x_2001_ = v_a_1995_;
                    v_isShared_2002_ = v_isSharedCheck_2011_;
                    state = 58;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1999_);
                    crate::leanh::lean_dec(v_a_1995_);
                    v___x_2001_ = crate::leanh::lean_box(0);
                    v_isShared_2002_ = v_isSharedCheck_2011_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_2003_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2004_ = lean_nat_add(v_val_1999_, v___x_2003_);
                crate::leanh::lean_dec(v_val_1999_);
                if v_isShared_2002_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2001_, 0, v___x_2004_);
                    v___x_2006_ = v___x_2001_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2004_);
                    v___x_2006_ = v_reuseFailAlloc_2010_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_1998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1997_, 0, v___x_2006_);
                    v___x_2008_ = v___x_1997_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
                    v___x_2008_ = v_reuseFailAlloc_2009_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2008_;
            }
            61 => {
                if crate::leanh::lean_obj_tag(v_a_2015_) == 0 {
                    v___x_2019_ = crate::leanh::lean_box(0);
                    if v_isShared_2018_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2017_, 0, v___x_2019_);
                        v___x_2021_ = v___x_2017_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_2022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
                        v___x_2021_ = v_reuseFailAlloc_2022_;
                        state = 62;
                        continue;
                    }
                } else {
                    v_val_2023_ = crate::leanh::lean_ctor_get(v_a_2015_, 0);
                    v_isSharedCheck_2034_ = (!crate::leanh::lean_is_exclusive(v_a_2015_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_2025_ = v_a_2015_;
                        v_isShared_2026_ = v_isSharedCheck_2034_;
                        state = 63;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2023_);
                        crate::leanh::lean_dec(v_a_2015_);
                        v___x_2025_ = crate::leanh::lean_box(0);
                        v_isShared_2026_ = v_isSharedCheck_2034_;
                        state = 63;
                        continue;
                    }
                }
            }
            62 => {
                return v___x_2021_;
            }
            63 => {
                v___x_2027_ = l_Int_toNat(v_val_2023_);
                crate::leanh::lean_dec(v_val_2023_);
                if v_isShared_2026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2027_);
                    v___x_2029_ = v___x_2025_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2027_);
                    v___x_2029_ = v_reuseFailAlloc_2033_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                if v_isShared_2018_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2017_, 0, v___x_2029_);
                    v___x_2031_ = v___x_2017_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2032_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
                    v___x_2031_ = v_reuseFailAlloc_2032_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2031_;
            }
            66 => {
                if v_isShared_2039_ == 0 {
                    v___x_2041_ = v___x_2038_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
                    v___x_2041_ = v_reuseFailAlloc_2042_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2041_;
            }
            68 => {
                if crate::leanh::lean_obj_tag(v_a_2045_) == 0 {
                    v___x_2049_ = crate::leanh::lean_box(0);
                    if v_isShared_2048_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2047_, 0, v___x_2049_);
                        v___x_2051_ = v___x_2047_;
                        state = 69;
                        continue;
                    } else {
                        v_reuseFailAlloc_2052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
                        v___x_2051_ = v_reuseFailAlloc_2052_;
                        state = 69;
                        continue;
                    }
                } else {
                    v_val_2053_ = crate::leanh::lean_ctor_get(v_a_2045_, 0);
                    v_isSharedCheck_2064_ = (!crate::leanh::lean_is_exclusive(v_a_2045_)) as u8;
                    if v_isSharedCheck_2064_ == 0 {
                        v___x_2055_ = v_a_2045_;
                        v_isShared_2056_ = v_isSharedCheck_2064_;
                        state = 70;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2053_);
                        crate::leanh::lean_dec(v_a_2045_);
                        v___x_2055_ = crate::leanh::lean_box(0);
                        v_isShared_2056_ = v_isSharedCheck_2064_;
                        state = 70;
                        continue;
                    }
                }
            }
            69 => {
                return v___x_2051_;
            }
            70 => {
                v___x_2057_ = lean_nat_abs(v_val_2053_);
                crate::leanh::lean_dec(v_val_2053_);
                if v_isShared_2056_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_2057_);
                    v___x_2059_ = v___x_2055_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2057_);
                    v___x_2059_ = v_reuseFailAlloc_2063_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_2048_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2047_, 0, v___x_2059_);
                    v___x_2061_ = v___x_2047_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_2062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
                    v___x_2061_ = v_reuseFailAlloc_2062_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_2061_;
            }
            73 => {
                if v_isShared_2069_ == 0 {
                    v___x_2071_ = v___x_2068_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
                    v___x_2071_ = v_reuseFailAlloc_2072_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_2071_;
            }
            75 => {
                return v___x_2076_;
            }
            76 => {
                if v_isShared_2082_ == 0 {
                    v___x_2084_ = v___x_2081_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_2085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
                    v___x_2084_ = v_reuseFailAlloc_2085_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_2084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___boxed(
    mut v_e_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
    mut v_a_2090_: *mut crate::leanh::LeanObject,
    mut v_a_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
    mut v_a_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2095_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
        v_e_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_,
    );
    crate::leanh::lean_dec(v_a_2093_);
    crate::leanh::lean_dec_ref(v_a_2092_);
    crate::leanh::lean_dec(v_a_2091_);
    crate::leanh::lean_dec_ref(v_a_2090_);
    crate::leanh::lean_dec(v_a_2089_);
    crate::leanh::lean_dec_ref(v_a_2088_);
    return v_res_2095_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___boxed(
    mut v_e_2096_: *mut crate::leanh::LeanObject,
    mut v_a_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2104_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
        v_e_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_,
    );
    crate::leanh::lean_dec(v_a_2102_);
    crate::leanh::lean_dec_ref(v_a_2101_);
    crate::leanh::lean_dec(v_a_2100_);
    crate::leanh::lean_dec_ref(v_a_2099_);
    crate::leanh::lean_dec(v_a_2098_);
    crate::leanh::lean_dec_ref(v_a_2097_);
    return v_res_2104_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore_spec__1(
    mut v_a_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = lean_nat_to_int(v_a_2105_);
    return v___x_2106_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_evalNat_x3f(
    mut v_e_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(
        v_e_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_,
    );
    return v___x_2115_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed(
    mut v_e_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
    mut v_a_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
    mut v_a_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_a_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(
        v_e_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_,
    );
    crate::leanh::lean_dec(v_a_2122_);
    crate::leanh::lean_dec_ref(v_a_2121_);
    crate::leanh::lean_dec(v_a_2120_);
    crate::leanh::lean_dec_ref(v_a_2119_);
    crate::leanh::lean_dec(v_a_2118_);
    crate::leanh::lean_dec_ref(v_a_2117_);
    return v_res_2124_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_evalInt_x3f(
    mut v_e_2125_: *mut crate::leanh::LeanObject,
    mut v_a_2126_: *mut crate::leanh::LeanObject,
    mut v_a_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
    mut v_a_2129_: *mut crate::leanh::LeanObject,
    mut v_a_2130_: *mut crate::leanh::LeanObject,
    mut v_a_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2133_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(
        v_e_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_,
    );
    return v___x_2133_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_evalInt_x3f___boxed(
    mut v_e_2134_: *mut crate::leanh::LeanObject,
    mut v_a_2135_: *mut crate::leanh::LeanObject,
    mut v_a_2136_: *mut crate::leanh::LeanObject,
    mut v_a_2137_: *mut crate::leanh::LeanObject,
    mut v_a_2138_: *mut crate::leanh::LeanObject,
    mut v_a_2139_: *mut crate::leanh::LeanObject,
    mut v_a_2140_: *mut crate::leanh::LeanObject,
    mut v_a_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2142_ = l_Lean_Meta_Sym_Arith_evalInt_x3f(
        v_e_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_,
    );
    crate::leanh::lean_dec(v_a_2140_);
    crate::leanh::lean_dec_ref(v_a_2139_);
    crate::leanh::lean_dec(v_a_2138_);
    crate::leanh::lean_dec_ref(v_a_2137_);
    crate::leanh::lean_dec(v_a_2136_);
    crate::leanh::lean_dec_ref(v_a_2135_);
    return v_res_2142_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_EvalNum(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_EvalNum(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_IntInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
}
