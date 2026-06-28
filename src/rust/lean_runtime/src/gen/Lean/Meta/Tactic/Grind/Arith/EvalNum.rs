// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.EvalNum
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.IntInstTesters Lean.Meta.NatInstTesters
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_mul, lean_nat_pow,
    lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3_value: LeanStringObject<48> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5_value: LeanStringObject<3> =
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
        m_data: [41, 96, 0],
    };
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value) as *mut LeanObject,13428217069302927667 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 65, 98, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value) as *mut LeanObject,12132318982517471999 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value) as *mut LeanObject,13897037934312376979 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 117, 99, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value) as *mut LeanObject,16112798088292836701 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value) as *mut LeanObject,12847922472053947547 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value) as *mut LeanObject,10422657989269798688 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value) as *mut LeanObject,13744984671752750173 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value) as *mut LeanObject,9682224670061807480 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value) as *mut LeanObject,11858238400308895562 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value) as *mut LeanObject,6100819061652633370 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value) as *mut LeanObject,16856108565602861689 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value) as *mut LeanObject,4187025665268973031 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value) as *mut LeanObject,2929883540436775422 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value) as *mut LeanObject,1611444129324655608 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 115, 116, 78, 97, 116, 67, 97, 115, 116, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value) as *mut LeanObject,14240220390202531956 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value) as *mut LeanObject,8075995802451307795 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value) as *mut LeanObject,5779414593499529281 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value) as *mut LeanObject,7063772860359172143 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value) as *mut LeanObject,9626815015619986526 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value) as *mut LeanObject,17185717442815859305 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    v___x_1150_ = l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1;
    v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
    return v___x_1151_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3;
    v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
    return v___x_1154_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5;
    v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
    return v___x_1157_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_checkExp___redArg(
    mut v_k_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
    mut v_a_1160_: *mut LeanObject,
    mut v_a_1161_: *mut LeanObject,
    mut v_a_1162_: *mut LeanObject,
    mut v_a_1163_: *mut LeanObject,
    mut v_a_1164_: *mut LeanObject,
    mut v_a_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v_exp_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v_exp_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1204_: u8 = 0;
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1208_: u8 = 0;
    let mut v_a_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1216_: u8 = 0;
    let mut v_a_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1224_: u8 = 0;
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_a_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1170_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1159_);
                if lean_obj_tag(v___x_1170_) == 0 {
                    v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
                    v_isSharedCheck_1225_ = (!lean_is_exclusive(v___x_1170_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1173_ = v___x_1170_;
                        v_isShared_1174_ = v_isSharedCheck_1225_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1171_);
                        lean_dec(v___x_1170_);
                        v___x_1173_ = lean_box(0);
                        v_isShared_1174_ = v_isSharedCheck_1225_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_1158_);
                    v_a_1226_ = lean_ctor_get(v___x_1170_, 0);
                    v_isSharedCheck_1233_ = (!lean_is_exclusive(v___x_1170_)) as u8;
                    if v_isSharedCheck_1233_ == 0 {
                        v___x_1228_ = v___x_1170_;
                        v_isShared_1229_ = v_isSharedCheck_1233_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1226_);
                        lean_dec(v___x_1170_);
                        v___x_1228_ = lean_box(0);
                        v_isShared_1229_ = v_isSharedCheck_1233_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1168_ = lean_box(0);
                v___x_1169_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1169_, 0, v___x_1168_);
                return v___x_1169_;
            }
            2 => {
                v_exp_1175_ = lean_ctor_get(v_a_1171_, 9);
                lean_inc(v_exp_1175_);
                lean_dec(v_a_1171_);
                v___x_1176_ = lean_nat_dec_lt(v_exp_1175_, v_k_1158_);
                lean_dec(v_exp_1175_);
                if v___x_1176_ == 0 {
                    lean_dec(v_k_1158_);
                    v___x_1177_ = l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0;
                    if v_isShared_1174_ == 0 {
                        lean_ctor_set(v___x_1173_, 0, v___x_1177_);
                        v___x_1179_ = v___x_1173_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
                        v___x_1179_ = v_reuseFailAlloc_1180_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1173_);
                    v___x_1181_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1159_);
                    if lean_obj_tag(v___x_1181_) == 0 {
                        v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
                        lean_inc(v_a_1182_);
                        lean_dec_ref_known(v___x_1181_, 1);
                        v___x_1183_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1160_);
                        if lean_obj_tag(v___x_1183_) == 0 {
                            v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
                            lean_inc(v_a_1184_);
                            lean_dec_ref_known(v___x_1183_, 1);
                            v___x_1185_ = (lean_unbox(v_a_1184_) as u8);
                            lean_dec(v_a_1184_);
                            if v___x_1185_ == 0 {
                                lean_dec(v_a_1182_);
                                lean_dec(v_k_1158_);
                                state = 1;
                                continue;
                            } else {
                                v_exp_1186_ = lean_ctor_get(v_a_1182_, 9);
                                lean_inc(v_exp_1186_);
                                lean_dec(v_a_1182_);
                                v___x_1187_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2_once
                                    ),
                                    _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2,
                                );
                                v___x_1188_ = l_Nat_reprFast(v_k_1158_);
                                v___x_1189_ = lean_alloc_ctor(3, 1, (0) as u32);
                                lean_ctor_set(v___x_1189_, 0, v___x_1188_);
                                v___x_1190_ = l_Lean_MessageData_ofFormat(v___x_1189_);
                                v___x_1191_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1191_, 0, v___x_1187_);
                                lean_ctor_set(v___x_1191_, 1, v___x_1190_);
                                v___x_1192_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4_once
                                    ),
                                    _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4,
                                );
                                v___x_1193_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1193_, 0, v___x_1191_);
                                lean_ctor_set(v___x_1193_, 1, v___x_1192_);
                                v___x_1194_ = l_Nat_reprFast(v_exp_1186_);
                                v___x_1195_ = lean_alloc_ctor(3, 1, (0) as u32);
                                lean_ctor_set(v___x_1195_, 0, v___x_1194_);
                                v___x_1196_ = l_Lean_MessageData_ofFormat(v___x_1195_);
                                v___x_1197_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1197_, 0, v___x_1193_);
                                lean_ctor_set(v___x_1197_, 1, v___x_1196_);
                                v___x_1198_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6_once
                                    ),
                                    _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6,
                                );
                                v___x_1199_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1199_, 0, v___x_1197_);
                                lean_ctor_set(v___x_1199_, 1, v___x_1198_);
                                v___x_1200_ = l_Lean_Meta_Sym_reportIssue(
                                    v___x_1199_,
                                    v_a_1160_,
                                    v_a_1161_,
                                    v_a_1162_,
                                    v_a_1163_,
                                    v_a_1164_,
                                    v_a_1165_,
                                );
                                if lean_obj_tag(v___x_1200_) == 0 {
                                    lean_dec_ref_known(v___x_1200_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
                                    v_isSharedCheck_1208_ = (!lean_is_exclusive(v___x_1200_)) as u8;
                                    if v_isSharedCheck_1208_ == 0 {
                                        v___x_1203_ = v___x_1200_;
                                        v_isShared_1204_ = v_isSharedCheck_1208_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1201_);
                                        lean_dec(v___x_1200_);
                                        v___x_1203_ = lean_box(0);
                                        v_isShared_1204_ = v_isSharedCheck_1208_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_1182_);
                            lean_dec(v_k_1158_);
                            v_a_1209_ = lean_ctor_get(v___x_1183_, 0);
                            v_isSharedCheck_1216_ = (!lean_is_exclusive(v___x_1183_)) as u8;
                            if v_isSharedCheck_1216_ == 0 {
                                v___x_1211_ = v___x_1183_;
                                v_isShared_1212_ = v_isSharedCheck_1216_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1209_);
                                lean_dec(v___x_1183_);
                                v___x_1211_ = lean_box(0);
                                v_isShared_1212_ = v_isSharedCheck_1216_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_k_1158_);
                        v_a_1217_ = lean_ctor_get(v___x_1181_, 0);
                        v_isSharedCheck_1224_ = (!lean_is_exclusive(v___x_1181_)) as u8;
                        if v_isSharedCheck_1224_ == 0 {
                            v___x_1219_ = v___x_1181_;
                            v_isShared_1220_ = v_isSharedCheck_1224_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1217_);
                            lean_dec(v___x_1181_);
                            v___x_1219_ = lean_box(0);
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
                    v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
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
                    v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
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
                    v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
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
                    v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
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
    mut v_k_1234_: *mut LeanObject,
    mut v_a_1235_: *mut LeanObject,
    mut v_a_1236_: *mut LeanObject,
    mut v_a_1237_: *mut LeanObject,
    mut v_a_1238_: *mut LeanObject,
    mut v_a_1239_: *mut LeanObject,
    mut v_a_1240_: *mut LeanObject,
    mut v_a_1241_: *mut LeanObject,
    mut v_a_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1243_: *mut LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(
        v_k_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_,
    );
    lean_dec(v_a_1241_);
    lean_dec_ref(v_a_1240_);
    lean_dec(v_a_1239_);
    lean_dec_ref(v_a_1238_);
    lean_dec(v_a_1237_);
    lean_dec_ref(v_a_1236_);
    lean_dec_ref(v_a_1235_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_checkExp(
    mut v_k_1244_: *mut LeanObject,
    mut v_a_1245_: *mut LeanObject,
    mut v_a_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
    mut v_a_1248_: *mut LeanObject,
    mut v_a_1249_: *mut LeanObject,
    mut v_a_1250_: *mut LeanObject,
    mut v_a_1251_: *mut LeanObject,
    mut v_a_1252_: *mut LeanObject,
    mut v_a_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(
        v_k_1244_, v_a_1246_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_,
    );
    return v___x_1255_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_checkExp___boxed(
    mut v_k_1256_: *mut LeanObject,
    mut v_a_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
    mut v_a_1263_: *mut LeanObject,
    mut v_a_1264_: *mut LeanObject,
    mut v_a_1265_: *mut LeanObject,
    mut v_a_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1267_: *mut LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_Meta_Grind_Arith_checkExp(
        v_k_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_,
        v_a_1264_, v_a_1265_,
    );
    lean_dec(v_a_1265_);
    lean_dec_ref(v_a_1264_);
    lean_dec(v_a_1263_);
    lean_dec_ref(v_a_1262_);
    lean_dec(v_a_1261_);
    lean_dec_ref(v_a_1260_);
    lean_dec(v_a_1259_);
    lean_dec_ref(v_a_1258_);
    lean_dec(v_a_1257_);
    return v_res_1267_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(
    mut v_e_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
    mut v_a_1342_: *mut LeanObject,
    mut v_a_1343_: *mut LeanObject,
    mut v_a_1344_: *mut LeanObject,
    mut v_a_1345_: *mut LeanObject,
    mut v_a_1346_: *mut LeanObject,
    mut v_a_1347_: *mut LeanObject,
    mut v_a_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1379_: u8 = 0;
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut v_a_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1404_: u8 = 0;
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut v_a_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    let mut v_arg_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v_arg_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: u8 = 0;
    let mut v_arg_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v_val_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_unused_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_a_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1500_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1518_: u8 = 0;
    let mut v_val_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1530_: u8 = 0;
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_unused_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_a_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1537_: u8 = 0;
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1547_: u8 = 0;
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v_val_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_unused_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v_a_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v_val_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1604_: u8 = 0;
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_isSharedCheck_1613_: u8 = 0;
    let mut v_unused_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v_a_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v_val_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1645_: u8 = 0;
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v_isSharedCheck_1654_: u8 = 0;
    let mut v_unused_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1656_: u8 = 0;
    let mut v_a_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1660_: u8 = 0;
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1664_: u8 = 0;
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1669_: u8 = 0;
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut v_unused_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1709_: u8 = 0;
    let mut v_a_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_a_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1722_: u8 = 0;
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1726_: u8 = 0;
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_a_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1741_: u8 = 0;
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v_val_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1762_: u8 = 0;
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v_unused_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut v_a_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v_unused_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut v_a_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1340_);
                v___x_1414_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1340_, v_a_1347_);
                if lean_obj_tag(v___x_1414_) == 0 {
                    v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1785_ = (!lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1785_ == 0 {
                        v___x_1417_ = v___x_1414_;
                        v_isShared_1418_ = v_isSharedCheck_1785_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_1415_);
                        lean_dec(v___x_1414_);
                        v___x_1417_ = lean_box(0);
                        v_isShared_1418_ = v_isSharedCheck_1785_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1340_);
                    v_a_1786_ = lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1793_ = (!lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1793_ == 0 {
                        v___x_1788_ = v___x_1414_;
                        v_isShared_1789_ = v_isSharedCheck_1793_;
                        state = 81;
                        continue;
                    } else {
                        lean_inc(v_a_1786_);
                        lean_dec(v___x_1414_);
                        v___x_1788_ = lean_box(0);
                        v_isShared_1789_ = v_isSharedCheck_1793_;
                        state = 81;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1363_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_i_1352_, v___y_1360_);
                if lean_obj_tag(v___x_1363_) == 0 {
                    v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
                    v_isSharedCheck_1405_ = (!lean_is_exclusive(v___x_1363_)) as u8;
                    if v_isSharedCheck_1405_ == 0 {
                        v___x_1366_ = v___x_1363_;
                        v_isShared_1367_ = v_isSharedCheck_1405_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1364_);
                        lean_dec(v___x_1363_);
                        v___x_1366_ = lean_box(0);
                        v_isShared_1367_ = v_isSharedCheck_1405_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_1353_);
                    v_a_1406_ = lean_ctor_get(v___x_1363_, 0);
                    v_isSharedCheck_1413_ = (!lean_is_exclusive(v___x_1363_)) as u8;
                    if v_isSharedCheck_1413_ == 0 {
                        v___x_1408_ = v___x_1363_;
                        v_isShared_1409_ = v_isSharedCheck_1413_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1406_);
                        lean_dec(v___x_1363_);
                        v___x_1408_ = lean_box(0);
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
                lean_dec_ref(v___x_1368_);
                if v___x_1370_ == 0 {
                    lean_dec_ref(v_a_1353_);
                    v___x_1371_ = lean_box(0);
                    if v_isShared_1367_ == 0 {
                        lean_ctor_set(v___x_1366_, 0, v___x_1371_);
                        v___x_1373_ = v___x_1366_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
                        v___x_1373_ = v_reuseFailAlloc_1374_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1366_);
                    v___x_1375_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_a_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
                    if lean_obj_tag(v___x_1375_) == 0 {
                        v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
                        v_isSharedCheck_1396_ = (!lean_is_exclusive(v___x_1375_)) as u8;
                        if v_isSharedCheck_1396_ == 0 {
                            v___x_1378_ = v___x_1375_;
                            v_isShared_1379_ = v_isSharedCheck_1396_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1376_);
                            lean_dec(v___x_1375_);
                            v___x_1378_ = lean_box(0);
                            v_isShared_1379_ = v_isSharedCheck_1396_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_1397_ = lean_ctor_get(v___x_1375_, 0);
                        v_isSharedCheck_1404_ = (!lean_is_exclusive(v___x_1375_)) as u8;
                        if v_isSharedCheck_1404_ == 0 {
                            v___x_1399_ = v___x_1375_;
                            v_isShared_1400_ = v_isSharedCheck_1404_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1397_);
                            lean_dec(v___x_1375_);
                            v___x_1399_ = lean_box(0);
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
                if lean_obj_tag(v_a_1376_) == 0 {
                    v___x_1380_ = lean_box(0);
                    if v_isShared_1379_ == 0 {
                        lean_ctor_set(v___x_1378_, 0, v___x_1380_);
                        v___x_1382_ = v___x_1378_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
                        v___x_1382_ = v_reuseFailAlloc_1383_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_1384_ = lean_ctor_get(v_a_1376_, 0);
                    v_isSharedCheck_1395_ = (!lean_is_exclusive(v_a_1376_)) as u8;
                    if v_isSharedCheck_1395_ == 0 {
                        v___x_1386_ = v_a_1376_;
                        v_isShared_1387_ = v_isSharedCheck_1395_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_1384_);
                        lean_dec(v_a_1376_);
                        v___x_1386_ = lean_box(0);
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
                    lean_ctor_set(v___x_1386_, 0, v___x_1388_);
                    v___x_1390_ = v___x_1386_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1388_);
                    v___x_1390_ = v_reuseFailAlloc_1394_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1379_ == 0 {
                    lean_ctor_set(v___x_1378_, 0, v___x_1390_);
                    v___x_1392_ = v___x_1378_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
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
                    v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
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
                    v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
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
                    lean_dec_ref(v___x_1424_);
                    lean_dec_ref(v_e_1340_);
                    state = 14;
                    continue;
                } else {
                    v_arg_1426_ = lean_ctor_get(v___x_1424_, 1);
                    lean_inc_ref(v_arg_1426_);
                    v___x_1427_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1424_);
                    v___x_1428_ = l_Lean_Expr_isApp(v___x_1427_);
                    if v___x_1428_ == 0 {
                        lean_dec_ref(v___x_1427_);
                        lean_dec_ref(v_arg_1426_);
                        lean_dec_ref(v_e_1340_);
                        state = 14;
                        continue;
                    } else {
                        v_arg_1429_ = lean_ctor_get(v___x_1427_, 1);
                        lean_inc_ref(v_arg_1429_);
                        v___x_1430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1427_);
                        v___x_1431_ = l_Lean_Expr_isApp(v___x_1430_);
                        if v___x_1431_ == 0 {
                            lean_dec_ref(v___x_1430_);
                            lean_dec_ref(v_arg_1429_);
                            lean_dec_ref(v_arg_1426_);
                            lean_dec_ref(v_e_1340_);
                            state = 14;
                            continue;
                        } else {
                            v_arg_1432_ = lean_ctor_get(v___x_1430_, 1);
                            lean_inc_ref(v_arg_1432_);
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
                                        lean_dec_ref(v_e_1340_);
                                        v___x_1440_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9;
                                        v___x_1441_ =
                                            l_Lean_Expr_isConstOf(v___x_1433_, v___x_1440_);
                                        if v___x_1441_ == 0 {
                                            v___x_1442_ = l_Lean_Expr_isApp(v___x_1433_);
                                            if v___x_1442_ == 0 {
                                                lean_dec_ref(v___x_1433_);
                                                lean_dec_ref(v_arg_1432_);
                                                lean_dec_ref(v_arg_1429_);
                                                lean_dec_ref(v_arg_1426_);
                                                state = 14;
                                                continue;
                                            } else {
                                                v___x_1443_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_1433_);
                                                v___x_1444_ = l_Lean_Expr_isApp(v___x_1443_);
                                                if v___x_1444_ == 0 {
                                                    lean_dec_ref(v___x_1443_);
                                                    lean_dec_ref(v_arg_1432_);
                                                    lean_dec_ref(v_arg_1429_);
                                                    lean_dec_ref(v_arg_1426_);
                                                    state = 14;
                                                    continue;
                                                } else {
                                                    v___x_1445_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1443_,
                                                    );
                                                    v___x_1446_ = l_Lean_Expr_isApp(v___x_1445_);
                                                    if v___x_1446_ == 0 {
                                                        lean_dec_ref(v___x_1445_);
                                                        lean_dec_ref(v_arg_1432_);
                                                        lean_dec_ref(v_arg_1429_);
                                                        lean_dec_ref(v_arg_1426_);
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
                                                                            lean_dec_ref(
                                                                                v___x_1447_,
                                                                            );
                                                                            if v___x_1459_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v_arg_1432_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1429_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1426_,
                                                                                );
                                                                                state = 14;
                                                                                continue;
                                                                            } else {
                                                                                lean_del_object(
                                                                                    v___x_1417_,
                                                                                );
                                                                                v___x_1460_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1432_, v_a_1347_);
                                                                                if lean_obj_tag(
                                                                                    v___x_1460_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
                                                                                    v_isSharedCheck_1492_ = (!lean_is_exclusive(v___x_1460_)) as u8;
                                                                                    if v_isSharedCheck_1492_ == 0 {
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1492_;
state = 16; continue;
} else {
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1492_;
state = 16; continue;
}
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_arg_1429_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1426_,
                                                                                    );
                                                                                    v_a_1493_ = lean_ctor_get(v___x_1460_, 0);
                                                                                    v_isSharedCheck_1500_ = (!lean_is_exclusive(v___x_1460_)) as u8;
                                                                                    if v_isSharedCheck_1500_ == 0 {
v___x_1495_ = v___x_1460_;
v_isShared_1496_ = v_isSharedCheck_1500_;
state = 22; continue;
} else {
lean_inc(v_a_1493_);
lean_dec(v___x_1460_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
state = 22; continue;
}
                                                                                }
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v___x_1447_,
                                                                            );
                                                                            lean_del_object(
                                                                                v___x_1417_,
                                                                            );
                                                                            v___x_1501_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_1432_, v_a_1347_);
                                                                            if lean_obj_tag(
                                                                                v___x_1501_,
                                                                            ) == 0
                                                                            {
                                                                                v_a_1502_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_1501_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_1533_ = (!lean_is_exclusive(v___x_1501_)) as u8;
                                                                                if v_isSharedCheck_1533_ == 0 {
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1533_;
state = 24; continue;
} else {
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1533_;
state = 24; continue;
}
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_1429_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1426_,
                                                                                );
                                                                                v_a_1534_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_1501_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_1541_ = (!lean_is_exclusive(v___x_1501_)) as u8;
                                                                                if v_isSharedCheck_1541_ == 0 {
v___x_1536_ = v___x_1501_;
v_isShared_1537_ = v_isSharedCheck_1541_;
state = 30; continue;
} else {
lean_inc(v_a_1534_);
lean_dec(v___x_1501_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
state = 30; continue;
}
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v___x_1447_);
                                                                        lean_del_object(
                                                                            v___x_1417_,
                                                                        );
                                                                        v___x_1542_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1432_, v_a_1347_);
                                                                        if lean_obj_tag(v___x_1542_)
                                                                            == 0
                                                                        {
                                                                            v_a_1543_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1542_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_1574_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_1542_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_1574_
                                                                                == 0
                                                                            {
                                                                                v___x_1545_ =
                                                                                    v___x_1542_;
                                                                                v_isShared_1546_ = v_isSharedCheck_1574_;
                                                                                state = 32;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_1543_);
                                                                                lean_dec(
                                                                                    v___x_1542_,
                                                                                );
                                                                                v___x_1545_ =
                                                                                    lean_box(0);
                                                                                v_isShared_1546_ = v_isSharedCheck_1574_;
                                                                                state = 32;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_1429_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1426_,
                                                                            );
                                                                            v_a_1575_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1542_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_1582_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_1542_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_1582_
                                                                                == 0
                                                                            {
                                                                                v___x_1577_ =
                                                                                    v___x_1542_;
                                                                                v_isShared_1578_ = v_isSharedCheck_1582_;
                                                                                state = 38;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_1575_);
                                                                                lean_dec(
                                                                                    v___x_1542_,
                                                                                );
                                                                                v___x_1577_ =
                                                                                    lean_box(0);
                                                                                v_isShared_1578_ = v_isSharedCheck_1582_;
                                                                                state = 38;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v___x_1447_);
                                                                    lean_del_object(v___x_1417_);
                                                                    v___x_1583_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_1432_, v_a_1347_);
                                                                    if lean_obj_tag(v___x_1583_)
                                                                        == 0
                                                                    {
                                                                        v_a_1584_ = lean_ctor_get(
                                                                            v___x_1583_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_1615_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_1583_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_1615_
                                                                            == 0
                                                                        {
                                                                            v___x_1586_ =
                                                                                v___x_1583_;
                                                                            v_isShared_1587_ = v_isSharedCheck_1615_;
                                                                            state = 40;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_1584_);
                                                                            lean_dec(v___x_1583_);
                                                                            v___x_1586_ =
                                                                                lean_box(0);
                                                                            v_isShared_1587_ = v_isSharedCheck_1615_;
                                                                            state = 40;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_1429_);
                                                                        lean_dec_ref(v_arg_1426_);
                                                                        v_a_1616_ = lean_ctor_get(
                                                                            v___x_1583_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_1623_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_1583_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_1623_
                                                                            == 0
                                                                        {
                                                                            v___x_1618_ =
                                                                                v___x_1583_;
                                                                            v_isShared_1619_ = v_isSharedCheck_1623_;
                                                                            state = 46;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_1616_);
                                                                            lean_dec(v___x_1583_);
                                                                            v___x_1618_ =
                                                                                lean_box(0);
                                                                            v_isShared_1619_ = v_isSharedCheck_1623_;
                                                                            state = 46;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_1447_);
                                                                lean_del_object(v___x_1417_);
                                                                v___x_1624_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_1432_, v_a_1347_);
                                                                if lean_obj_tag(v___x_1624_) == 0 {
                                                                    v_a_1625_ = lean_ctor_get(
                                                                        v___x_1624_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_1656_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_1624_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_1656_ == 0 {
                                                                        v___x_1627_ = v___x_1624_;
                                                                        v_isShared_1628_ =
                                                                            v_isSharedCheck_1656_;
                                                                        state = 48;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_1625_);
                                                                        lean_dec(v___x_1624_);
                                                                        v___x_1627_ = lean_box(0);
                                                                        v_isShared_1628_ =
                                                                            v_isSharedCheck_1656_;
                                                                        state = 48;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_arg_1429_);
                                                                    lean_dec_ref(v_arg_1426_);
                                                                    v_a_1657_ = lean_ctor_get(
                                                                        v___x_1624_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_1664_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_1624_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_1664_ == 0 {
                                                                        v___x_1659_ = v___x_1624_;
                                                                        v_isShared_1660_ =
                                                                            v_isSharedCheck_1664_;
                                                                        state = 54;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_1657_);
                                                                        lean_dec(v___x_1624_);
                                                                        v___x_1659_ = lean_box(0);
                                                                        v_isShared_1660_ =
                                                                            v_isSharedCheck_1664_;
                                                                        state = 54;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref(v___x_1447_);
                                                            lean_del_object(v___x_1417_);
                                                            v___x_1665_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_1432_, v_a_1347_);
                                                            if lean_obj_tag(v___x_1665_) == 0 {
                                                                v_a_1666_ =
                                                                    lean_ctor_get(v___x_1665_, 0);
                                                                v_isSharedCheck_1727_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_1665_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_1727_ == 0 {
                                                                    v___x_1668_ = v___x_1665_;
                                                                    v_isShared_1669_ =
                                                                        v_isSharedCheck_1727_;
                                                                    state = 56;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_1666_);
                                                                    lean_dec(v___x_1665_);
                                                                    v___x_1668_ = lean_box(0);
                                                                    v_isShared_1669_ =
                                                                        v_isSharedCheck_1727_;
                                                                    state = 56;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_arg_1429_);
                                                                lean_dec_ref(v_arg_1426_);
                                                                v_a_1728_ =
                                                                    lean_ctor_get(v___x_1665_, 0);
                                                                v_isSharedCheck_1735_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_1665_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_1735_ == 0 {
                                                                    v___x_1730_ = v___x_1665_;
                                                                    v_isShared_1731_ =
                                                                        v_isSharedCheck_1735_;
                                                                    state = 69;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_1728_);
                                                                    lean_dec(v___x_1665_);
                                                                    v___x_1730_ = lean_box(0);
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
                                            lean_dec_ref(v___x_1433_);
                                            lean_dec_ref(v_arg_1432_);
                                            lean_del_object(v___x_1417_);
                                            v___x_1736_ =
                                                l_Lean_Meta_Structural_isInstNegInt___redArg(
                                                    v_arg_1429_,
                                                    v_a_1347_,
                                                );
                                            if lean_obj_tag(v___x_1736_) == 0 {
                                                v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
                                                v_isSharedCheck_1765_ =
                                                    (!lean_is_exclusive(v___x_1736_)) as u8;
                                                if v_isSharedCheck_1765_ == 0 {
                                                    v___x_1739_ = v___x_1736_;
                                                    v_isShared_1740_ = v_isSharedCheck_1765_;
                                                    state = 71;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_1737_);
                                                    lean_dec(v___x_1736_);
                                                    v___x_1739_ = lean_box(0);
                                                    v_isShared_1740_ = v_isSharedCheck_1765_;
                                                    state = 71;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_1426_);
                                                v_a_1766_ = lean_ctor_get(v___x_1736_, 0);
                                                v_isSharedCheck_1773_ =
                                                    (!lean_is_exclusive(v___x_1736_)) as u8;
                                                if v_isSharedCheck_1773_ == 0 {
                                                    v___x_1768_ = v___x_1736_;
                                                    v_isShared_1769_ = v_isSharedCheck_1773_;
                                                    state = 77;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_1766_);
                                                    lean_dec(v___x_1736_);
                                                    v___x_1768_ = lean_box(0);
                                                    v_isShared_1769_ = v_isSharedCheck_1773_;
                                                    state = 77;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_1433_);
                                        lean_dec_ref(v_arg_1432_);
                                        lean_dec_ref(v_arg_1429_);
                                        lean_dec_ref(v_arg_1426_);
                                        lean_del_object(v___x_1417_);
                                        v___x_1774_ = l_Lean_Meta_getIntValue_x3f(
                                            v_e_1340_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_,
                                        );
                                        if lean_obj_tag(v___x_1774_) == 0 {
                                            v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
                                            lean_inc(v_a_1775_);
                                            if lean_obj_tag(v_a_1775_) == 1 {
                                                lean_dec_ref_known(v_a_1775_, 1);
                                                return v___x_1774_;
                                            } else {
                                                lean_dec(v_a_1775_);
                                                v_isSharedCheck_1783_ =
                                                    (!lean_is_exclusive(v___x_1774_)) as u8;
                                                if v_isSharedCheck_1783_ == 0 {
                                                    v_unused_1784_ = lean_ctor_get(v___x_1774_, 0);
                                                    lean_dec(v_unused_1784_);
                                                    v___x_1777_ = v___x_1774_;
                                                    v_isShared_1778_ = v_isSharedCheck_1783_;
                                                    state = 79;
                                                    continue;
                                                } else {
                                                    lean_dec(v___x_1774_);
                                                    v___x_1777_ = lean_box(0);
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
                                    lean_dec_ref(v___x_1433_);
                                    lean_dec_ref(v_arg_1432_);
                                    lean_del_object(v___x_1417_);
                                    lean_dec_ref(v_e_1340_);
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
                                lean_dec_ref(v___x_1433_);
                                lean_dec_ref(v_arg_1432_);
                                lean_del_object(v___x_1417_);
                                lean_dec_ref(v_e_1340_);
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
                v___x_1420_ = lean_box(0);
                if v_isShared_1418_ == 0 {
                    lean_ctor_set(v___x_1417_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1417_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
                    v___x_1422_ = v_reuseFailAlloc_1423_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1422_;
            }
            16 => {
                v___x_1465_ = (lean_unbox(v_a_1461_) as u8);
                lean_dec(v_a_1461_);
                if v___x_1465_ == 0 {
                    lean_dec_ref(v_arg_1429_);
                    lean_dec_ref(v_arg_1426_);
                    v___x_1466_ = lean_box(0);
                    if v_isShared_1464_ == 0 {
                        lean_ctor_set(v___x_1463_, 0, v___x_1466_);
                        v___x_1468_ = v___x_1463_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
                        v___x_1468_ = v_reuseFailAlloc_1469_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1463_);
                    v___x_1470_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if lean_obj_tag(v___x_1470_) == 0 {
                        v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
                        lean_inc(v_a_1471_);
                        if lean_obj_tag(v_a_1471_) == 0 {
                            lean_dec_ref(v_arg_1426_);
                            return v___x_1470_;
                        } else {
                            lean_dec_ref_known(v___x_1470_, 1);
                            v_val_1472_ = lean_ctor_get(v_a_1471_, 0);
                            lean_inc(v_val_1472_);
                            lean_dec_ref_known(v_a_1471_, 1);
                            v___x_1473_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if lean_obj_tag(v___x_1473_) == 0 {
                                v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
                                lean_inc(v_a_1474_);
                                if lean_obj_tag(v_a_1474_) == 0 {
                                    lean_dec(v_val_1472_);
                                    return v___x_1473_;
                                } else {
                                    v_isSharedCheck_1490_ = (!lean_is_exclusive(v___x_1473_)) as u8;
                                    if v_isSharedCheck_1490_ == 0 {
                                        v_unused_1491_ = lean_ctor_get(v___x_1473_, 0);
                                        lean_dec(v_unused_1491_);
                                        v___x_1476_ = v___x_1473_;
                                        v_isShared_1477_ = v_isSharedCheck_1490_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1473_);
                                        v___x_1476_ = lean_box(0);
                                        v_isShared_1477_ = v_isSharedCheck_1490_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1472_);
                                return v___x_1473_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1426_);
                        return v___x_1470_;
                    }
                }
            }
            17 => {
                return v___x_1468_;
            }
            18 => {
                v_val_1478_ = lean_ctor_get(v_a_1474_, 0);
                v_isSharedCheck_1489_ = (!lean_is_exclusive(v_a_1474_)) as u8;
                if v_isSharedCheck_1489_ == 0 {
                    v___x_1480_ = v_a_1474_;
                    v_isShared_1481_ = v_isSharedCheck_1489_;
                    state = 19;
                    continue;
                } else {
                    lean_inc(v_val_1478_);
                    lean_dec(v_a_1474_);
                    v___x_1480_ = lean_box(0);
                    v_isShared_1481_ = v_isSharedCheck_1489_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1482_ = lean_int_add(v_val_1472_, v_val_1478_);
                lean_dec(v_val_1478_);
                lean_dec(v_val_1472_);
                if v_isShared_1481_ == 0 {
                    lean_ctor_set(v___x_1480_, 0, v___x_1482_);
                    v___x_1484_ = v___x_1480_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1482_);
                    v___x_1484_ = v_reuseFailAlloc_1488_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1477_ == 0 {
                    lean_ctor_set(v___x_1476_, 0, v___x_1484_);
                    v___x_1486_ = v___x_1476_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
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
                    v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
                    v___x_1498_ = v_reuseFailAlloc_1499_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1498_;
            }
            24 => {
                v___x_1506_ = (lean_unbox(v_a_1502_) as u8);
                lean_dec(v_a_1502_);
                if v___x_1506_ == 0 {
                    lean_dec_ref(v_arg_1429_);
                    lean_dec_ref(v_arg_1426_);
                    v___x_1507_ = lean_box(0);
                    if v_isShared_1505_ == 0 {
                        lean_ctor_set(v___x_1504_, 0, v___x_1507_);
                        v___x_1509_ = v___x_1504_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
                        v___x_1509_ = v_reuseFailAlloc_1510_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1504_);
                    v___x_1511_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if lean_obj_tag(v___x_1511_) == 0 {
                        v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
                        lean_inc(v_a_1512_);
                        if lean_obj_tag(v_a_1512_) == 0 {
                            lean_dec_ref(v_arg_1426_);
                            return v___x_1511_;
                        } else {
                            lean_dec_ref_known(v___x_1511_, 1);
                            v_val_1513_ = lean_ctor_get(v_a_1512_, 0);
                            lean_inc(v_val_1513_);
                            lean_dec_ref_known(v_a_1512_, 1);
                            v___x_1514_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if lean_obj_tag(v___x_1514_) == 0 {
                                v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
                                lean_inc(v_a_1515_);
                                if lean_obj_tag(v_a_1515_) == 0 {
                                    lean_dec(v_val_1513_);
                                    return v___x_1514_;
                                } else {
                                    v_isSharedCheck_1531_ = (!lean_is_exclusive(v___x_1514_)) as u8;
                                    if v_isSharedCheck_1531_ == 0 {
                                        v_unused_1532_ = lean_ctor_get(v___x_1514_, 0);
                                        lean_dec(v_unused_1532_);
                                        v___x_1517_ = v___x_1514_;
                                        v_isShared_1518_ = v_isSharedCheck_1531_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1514_);
                                        v___x_1517_ = lean_box(0);
                                        v_isShared_1518_ = v_isSharedCheck_1531_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1513_);
                                return v___x_1514_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1426_);
                        return v___x_1511_;
                    }
                }
            }
            25 => {
                return v___x_1509_;
            }
            26 => {
                v_val_1519_ = lean_ctor_get(v_a_1515_, 0);
                v_isSharedCheck_1530_ = (!lean_is_exclusive(v_a_1515_)) as u8;
                if v_isSharedCheck_1530_ == 0 {
                    v___x_1521_ = v_a_1515_;
                    v_isShared_1522_ = v_isSharedCheck_1530_;
                    state = 27;
                    continue;
                } else {
                    lean_inc(v_val_1519_);
                    lean_dec(v_a_1515_);
                    v___x_1521_ = lean_box(0);
                    v_isShared_1522_ = v_isSharedCheck_1530_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_1523_ = lean_int_sub(v_val_1513_, v_val_1519_);
                lean_dec(v_val_1519_);
                lean_dec(v_val_1513_);
                if v_isShared_1522_ == 0 {
                    lean_ctor_set(v___x_1521_, 0, v___x_1523_);
                    v___x_1525_ = v___x_1521_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1523_);
                    v___x_1525_ = v_reuseFailAlloc_1529_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_1518_ == 0 {
                    lean_ctor_set(v___x_1517_, 0, v___x_1525_);
                    v___x_1527_ = v___x_1517_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
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
                    v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
                    v___x_1539_ = v_reuseFailAlloc_1540_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1539_;
            }
            32 => {
                v___x_1547_ = (lean_unbox(v_a_1543_) as u8);
                lean_dec(v_a_1543_);
                if v___x_1547_ == 0 {
                    lean_dec_ref(v_arg_1429_);
                    lean_dec_ref(v_arg_1426_);
                    v___x_1548_ = lean_box(0);
                    if v_isShared_1546_ == 0 {
                        lean_ctor_set(v___x_1545_, 0, v___x_1548_);
                        v___x_1550_ = v___x_1545_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
                        v___x_1550_ = v_reuseFailAlloc_1551_;
                        state = 33;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1545_);
                    v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if lean_obj_tag(v___x_1552_) == 0 {
                        v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
                        lean_inc(v_a_1553_);
                        if lean_obj_tag(v_a_1553_) == 0 {
                            lean_dec_ref(v_arg_1426_);
                            return v___x_1552_;
                        } else {
                            lean_dec_ref_known(v___x_1552_, 1);
                            v_val_1554_ = lean_ctor_get(v_a_1553_, 0);
                            lean_inc(v_val_1554_);
                            lean_dec_ref_known(v_a_1553_, 1);
                            v___x_1555_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if lean_obj_tag(v___x_1555_) == 0 {
                                v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
                                lean_inc(v_a_1556_);
                                if lean_obj_tag(v_a_1556_) == 0 {
                                    lean_dec(v_val_1554_);
                                    return v___x_1555_;
                                } else {
                                    v_isSharedCheck_1572_ = (!lean_is_exclusive(v___x_1555_)) as u8;
                                    if v_isSharedCheck_1572_ == 0 {
                                        v_unused_1573_ = lean_ctor_get(v___x_1555_, 0);
                                        lean_dec(v_unused_1573_);
                                        v___x_1558_ = v___x_1555_;
                                        v_isShared_1559_ = v_isSharedCheck_1572_;
                                        state = 34;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1555_);
                                        v___x_1558_ = lean_box(0);
                                        v_isShared_1559_ = v_isSharedCheck_1572_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1554_);
                                return v___x_1555_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1426_);
                        return v___x_1552_;
                    }
                }
            }
            33 => {
                return v___x_1550_;
            }
            34 => {
                v_val_1560_ = lean_ctor_get(v_a_1556_, 0);
                v_isSharedCheck_1571_ = (!lean_is_exclusive(v_a_1556_)) as u8;
                if v_isSharedCheck_1571_ == 0 {
                    v___x_1562_ = v_a_1556_;
                    v_isShared_1563_ = v_isSharedCheck_1571_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_val_1560_);
                    lean_dec(v_a_1556_);
                    v___x_1562_ = lean_box(0);
                    v_isShared_1563_ = v_isSharedCheck_1571_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1564_ = lean_int_mul(v_val_1554_, v_val_1560_);
                lean_dec(v_val_1560_);
                lean_dec(v_val_1554_);
                if v_isShared_1563_ == 0 {
                    lean_ctor_set(v___x_1562_, 0, v___x_1564_);
                    v___x_1566_ = v___x_1562_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
                    v___x_1566_ = v_reuseFailAlloc_1570_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1559_ == 0 {
                    lean_ctor_set(v___x_1558_, 0, v___x_1566_);
                    v___x_1568_ = v___x_1558_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
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
                    v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1580_;
            }
            40 => {
                v___x_1588_ = (lean_unbox(v_a_1584_) as u8);
                lean_dec(v_a_1584_);
                if v___x_1588_ == 0 {
                    lean_dec_ref(v_arg_1429_);
                    lean_dec_ref(v_arg_1426_);
                    v___x_1589_ = lean_box(0);
                    if v_isShared_1587_ == 0 {
                        lean_ctor_set(v___x_1586_, 0, v___x_1589_);
                        v___x_1591_ = v___x_1586_;
                        state = 41;
                        continue;
                    } else {
                        v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
                        v___x_1591_ = v_reuseFailAlloc_1592_;
                        state = 41;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1586_);
                    v___x_1593_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if lean_obj_tag(v___x_1593_) == 0 {
                        v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
                        lean_inc(v_a_1594_);
                        if lean_obj_tag(v_a_1594_) == 0 {
                            lean_dec_ref(v_arg_1426_);
                            return v___x_1593_;
                        } else {
                            lean_dec_ref_known(v___x_1593_, 1);
                            v_val_1595_ = lean_ctor_get(v_a_1594_, 0);
                            lean_inc(v_val_1595_);
                            lean_dec_ref_known(v_a_1594_, 1);
                            v___x_1596_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if lean_obj_tag(v___x_1596_) == 0 {
                                v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
                                lean_inc(v_a_1597_);
                                if lean_obj_tag(v_a_1597_) == 0 {
                                    lean_dec(v_val_1595_);
                                    return v___x_1596_;
                                } else {
                                    v_isSharedCheck_1613_ = (!lean_is_exclusive(v___x_1596_)) as u8;
                                    if v_isSharedCheck_1613_ == 0 {
                                        v_unused_1614_ = lean_ctor_get(v___x_1596_, 0);
                                        lean_dec(v_unused_1614_);
                                        v___x_1599_ = v___x_1596_;
                                        v_isShared_1600_ = v_isSharedCheck_1613_;
                                        state = 42;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1596_);
                                        v___x_1599_ = lean_box(0);
                                        v_isShared_1600_ = v_isSharedCheck_1613_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1595_);
                                return v___x_1596_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1426_);
                        return v___x_1593_;
                    }
                }
            }
            41 => {
                return v___x_1591_;
            }
            42 => {
                v_val_1601_ = lean_ctor_get(v_a_1597_, 0);
                v_isSharedCheck_1612_ = (!lean_is_exclusive(v_a_1597_)) as u8;
                if v_isSharedCheck_1612_ == 0 {
                    v___x_1603_ = v_a_1597_;
                    v_isShared_1604_ = v_isSharedCheck_1612_;
                    state = 43;
                    continue;
                } else {
                    lean_inc(v_val_1601_);
                    lean_dec(v_a_1597_);
                    v___x_1603_ = lean_box(0);
                    v_isShared_1604_ = v_isSharedCheck_1612_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_1605_ = lean_int_ediv(v_val_1595_, v_val_1601_);
                lean_dec(v_val_1601_);
                lean_dec(v_val_1595_);
                if v_isShared_1604_ == 0 {
                    lean_ctor_set(v___x_1603_, 0, v___x_1605_);
                    v___x_1607_ = v___x_1603_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1605_);
                    v___x_1607_ = v_reuseFailAlloc_1611_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_1600_ == 0 {
                    lean_ctor_set(v___x_1599_, 0, v___x_1607_);
                    v___x_1609_ = v___x_1599_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
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
                    v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
                    v___x_1621_ = v_reuseFailAlloc_1622_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1621_;
            }
            48 => {
                v___x_1629_ = (lean_unbox(v_a_1625_) as u8);
                lean_dec(v_a_1625_);
                if v___x_1629_ == 0 {
                    lean_dec_ref(v_arg_1429_);
                    lean_dec_ref(v_arg_1426_);
                    v___x_1630_ = lean_box(0);
                    if v_isShared_1628_ == 0 {
                        lean_ctor_set(v___x_1627_, 0, v___x_1630_);
                        v___x_1632_ = v___x_1627_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
                        v___x_1632_ = v_reuseFailAlloc_1633_;
                        state = 49;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1627_);
                    v___x_1634_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if lean_obj_tag(v___x_1634_) == 0 {
                        v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
                        lean_inc(v_a_1635_);
                        if lean_obj_tag(v_a_1635_) == 0 {
                            lean_dec_ref(v_arg_1426_);
                            return v___x_1634_;
                        } else {
                            lean_dec_ref_known(v___x_1634_, 1);
                            v_val_1636_ = lean_ctor_get(v_a_1635_, 0);
                            lean_inc(v_val_1636_);
                            lean_dec_ref_known(v_a_1635_, 1);
                            v___x_1637_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if lean_obj_tag(v___x_1637_) == 0 {
                                v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
                                lean_inc(v_a_1638_);
                                if lean_obj_tag(v_a_1638_) == 0 {
                                    lean_dec(v_val_1636_);
                                    return v___x_1637_;
                                } else {
                                    v_isSharedCheck_1654_ = (!lean_is_exclusive(v___x_1637_)) as u8;
                                    if v_isSharedCheck_1654_ == 0 {
                                        v_unused_1655_ = lean_ctor_get(v___x_1637_, 0);
                                        lean_dec(v_unused_1655_);
                                        v___x_1640_ = v___x_1637_;
                                        v_isShared_1641_ = v_isSharedCheck_1654_;
                                        state = 50;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1637_);
                                        v___x_1640_ = lean_box(0);
                                        v_isShared_1641_ = v_isSharedCheck_1654_;
                                        state = 50;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1636_);
                                return v___x_1637_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1426_);
                        return v___x_1634_;
                    }
                }
            }
            49 => {
                return v___x_1632_;
            }
            50 => {
                v_val_1642_ = lean_ctor_get(v_a_1638_, 0);
                v_isSharedCheck_1653_ = (!lean_is_exclusive(v_a_1638_)) as u8;
                if v_isSharedCheck_1653_ == 0 {
                    v___x_1644_ = v_a_1638_;
                    v_isShared_1645_ = v_isSharedCheck_1653_;
                    state = 51;
                    continue;
                } else {
                    lean_inc(v_val_1642_);
                    lean_dec(v_a_1638_);
                    v___x_1644_ = lean_box(0);
                    v_isShared_1645_ = v_isSharedCheck_1653_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                v___x_1646_ = lean_int_emod(v_val_1636_, v_val_1642_);
                lean_dec(v_val_1642_);
                lean_dec(v_val_1636_);
                if v_isShared_1645_ == 0 {
                    lean_ctor_set(v___x_1644_, 0, v___x_1646_);
                    v___x_1648_ = v___x_1644_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1646_);
                    v___x_1648_ = v_reuseFailAlloc_1652_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                if v_isShared_1641_ == 0 {
                    lean_ctor_set(v___x_1640_, 0, v___x_1648_);
                    v___x_1650_ = v___x_1640_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
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
                    v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
                    v___x_1662_ = v_reuseFailAlloc_1663_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_1662_;
            }
            56 => {
                v___x_1670_ = (lean_unbox(v_a_1666_) as u8);
                lean_dec(v_a_1666_);
                if v___x_1670_ == 0 {
                    lean_dec_ref(v_arg_1429_);
                    lean_dec_ref(v_arg_1426_);
                    v___x_1671_ = lean_box(0);
                    if v_isShared_1669_ == 0 {
                        lean_ctor_set(v___x_1668_, 0, v___x_1671_);
                        v___x_1673_ = v___x_1668_;
                        state = 57;
                        continue;
                    } else {
                        v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
                        v___x_1673_ = v_reuseFailAlloc_1674_;
                        state = 57;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1668_);
                    v___x_1675_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1429_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if lean_obj_tag(v___x_1675_) == 0 {
                        v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
                        lean_inc(v_a_1676_);
                        if lean_obj_tag(v_a_1676_) == 0 {
                            lean_dec_ref(v_arg_1426_);
                            return v___x_1675_;
                        } else {
                            lean_dec_ref_known(v___x_1675_, 1);
                            v_val_1677_ = lean_ctor_get(v_a_1676_, 0);
                            lean_inc(v_val_1677_);
                            lean_dec_ref_known(v_a_1676_, 1);
                            v___x_1678_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                            if lean_obj_tag(v___x_1678_) == 0 {
                                v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
                                v_isSharedCheck_1718_ = (!lean_is_exclusive(v___x_1678_)) as u8;
                                if v_isSharedCheck_1718_ == 0 {
                                    v___x_1681_ = v___x_1678_;
                                    v_isShared_1682_ = v_isSharedCheck_1718_;
                                    state = 58;
                                    continue;
                                } else {
                                    lean_inc(v_a_1679_);
                                    lean_dec(v___x_1678_);
                                    v___x_1681_ = lean_box(0);
                                    v_isShared_1682_ = v_isSharedCheck_1718_;
                                    state = 58;
                                    continue;
                                }
                            } else {
                                lean_dec(v_val_1677_);
                                v_a_1719_ = lean_ctor_get(v___x_1678_, 0);
                                v_isSharedCheck_1726_ = (!lean_is_exclusive(v___x_1678_)) as u8;
                                if v_isSharedCheck_1726_ == 0 {
                                    v___x_1721_ = v___x_1678_;
                                    v_isShared_1722_ = v_isSharedCheck_1726_;
                                    state = 67;
                                    continue;
                                } else {
                                    lean_inc(v_a_1719_);
                                    lean_dec(v___x_1678_);
                                    v___x_1721_ = lean_box(0);
                                    v_isShared_1722_ = v_isSharedCheck_1726_;
                                    state = 67;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1426_);
                        return v___x_1675_;
                    }
                }
            }
            57 => {
                return v___x_1673_;
            }
            58 => {
                if lean_obj_tag(v_a_1679_) == 0 {
                    lean_dec(v_val_1677_);
                    v___x_1683_ = lean_box(0);
                    if v_isShared_1682_ == 0 {
                        lean_ctor_set(v___x_1681_, 0, v___x_1683_);
                        v___x_1685_ = v___x_1681_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
                        v___x_1685_ = v_reuseFailAlloc_1686_;
                        state = 59;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1681_);
                    v_val_1687_ = lean_ctor_get(v_a_1679_, 0);
                    lean_inc_n(v_val_1687_, 2);
                    lean_dec_ref_known(v_a_1679_, 1);
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
                    if lean_obj_tag(v___x_1688_) == 0 {
                        v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
                        v_isSharedCheck_1709_ = (!lean_is_exclusive(v___x_1688_)) as u8;
                        if v_isSharedCheck_1709_ == 0 {
                            v___x_1691_ = v___x_1688_;
                            v_isShared_1692_ = v_isSharedCheck_1709_;
                            state = 60;
                            continue;
                        } else {
                            lean_inc(v_a_1689_);
                            lean_dec(v___x_1688_);
                            v___x_1691_ = lean_box(0);
                            v_isShared_1692_ = v_isSharedCheck_1709_;
                            state = 60;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_1687_);
                        lean_dec(v_val_1677_);
                        v_a_1710_ = lean_ctor_get(v___x_1688_, 0);
                        v_isSharedCheck_1717_ = (!lean_is_exclusive(v___x_1688_)) as u8;
                        if v_isSharedCheck_1717_ == 0 {
                            v___x_1712_ = v___x_1688_;
                            v_isShared_1713_ = v_isSharedCheck_1717_;
                            state = 65;
                            continue;
                        } else {
                            lean_inc(v_a_1710_);
                            lean_dec(v___x_1688_);
                            v___x_1712_ = lean_box(0);
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
                if lean_obj_tag(v_a_1689_) == 0 {
                    lean_dec(v_val_1687_);
                    lean_dec(v_val_1677_);
                    v___x_1693_ = lean_box(0);
                    if v_isShared_1692_ == 0 {
                        lean_ctor_set(v___x_1691_, 0, v___x_1693_);
                        v___x_1695_ = v___x_1691_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
                        v___x_1695_ = v_reuseFailAlloc_1696_;
                        state = 61;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1707_ = (!lean_is_exclusive(v_a_1689_)) as u8;
                    if v_isSharedCheck_1707_ == 0 {
                        v_unused_1708_ = lean_ctor_get(v_a_1689_, 0);
                        lean_dec(v_unused_1708_);
                        v___x_1698_ = v_a_1689_;
                        v_isShared_1699_ = v_isSharedCheck_1707_;
                        state = 62;
                        continue;
                    } else {
                        lean_dec(v_a_1689_);
                        v___x_1698_ = lean_box(0);
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
                lean_dec(v_val_1687_);
                lean_dec(v_val_1677_);
                if v_isShared_1699_ == 0 {
                    lean_ctor_set(v___x_1698_, 0, v___x_1700_);
                    v___x_1702_ = v___x_1698_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1700_);
                    v___x_1702_ = v_reuseFailAlloc_1706_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v_isShared_1692_ == 0 {
                    lean_ctor_set(v___x_1691_, 0, v___x_1702_);
                    v___x_1704_ = v___x_1691_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
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
                    v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
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
                    v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
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
                    v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_1733_;
            }
            71 => {
                v___x_1741_ = (lean_unbox(v_a_1737_) as u8);
                lean_dec(v_a_1737_);
                if v___x_1741_ == 0 {
                    lean_dec_ref(v_arg_1426_);
                    v___x_1742_ = lean_box(0);
                    if v_isShared_1740_ == 0 {
                        lean_ctor_set(v___x_1739_, 0, v___x_1742_);
                        v___x_1744_ = v___x_1739_;
                        state = 72;
                        continue;
                    } else {
                        v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
                        v___x_1744_ = v_reuseFailAlloc_1745_;
                        state = 72;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1739_);
                    v___x_1746_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1426_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
                    if lean_obj_tag(v___x_1746_) == 0 {
                        v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
                        lean_inc(v_a_1747_);
                        if lean_obj_tag(v_a_1747_) == 0 {
                            return v___x_1746_;
                        } else {
                            v_isSharedCheck_1763_ = (!lean_is_exclusive(v___x_1746_)) as u8;
                            if v_isSharedCheck_1763_ == 0 {
                                v_unused_1764_ = lean_ctor_get(v___x_1746_, 0);
                                lean_dec(v_unused_1764_);
                                v___x_1749_ = v___x_1746_;
                                v_isShared_1750_ = v_isSharedCheck_1763_;
                                state = 73;
                                continue;
                            } else {
                                lean_dec(v___x_1746_);
                                v___x_1749_ = lean_box(0);
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
                v_val_1751_ = lean_ctor_get(v_a_1747_, 0);
                v_isSharedCheck_1762_ = (!lean_is_exclusive(v_a_1747_)) as u8;
                if v_isSharedCheck_1762_ == 0 {
                    v___x_1753_ = v_a_1747_;
                    v_isShared_1754_ = v_isSharedCheck_1762_;
                    state = 74;
                    continue;
                } else {
                    lean_inc(v_val_1751_);
                    lean_dec(v_a_1747_);
                    v___x_1753_ = lean_box(0);
                    v_isShared_1754_ = v_isSharedCheck_1762_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                v___x_1755_ = lean_int_neg(v_val_1751_);
                lean_dec(v_val_1751_);
                if v_isShared_1754_ == 0 {
                    lean_ctor_set(v___x_1753_, 0, v___x_1755_);
                    v___x_1757_ = v___x_1753_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1755_);
                    v___x_1757_ = v_reuseFailAlloc_1761_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_1750_ == 0 {
                    lean_ctor_set(v___x_1749_, 0, v___x_1757_);
                    v___x_1759_ = v___x_1749_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
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
                    v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
                    v___x_1771_ = v_reuseFailAlloc_1772_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                return v___x_1771_;
            }
            79 => {
                v___x_1779_ = lean_box(0);
                if v_isShared_1778_ == 0 {
                    lean_ctor_set(v___x_1777_, 0, v___x_1779_);
                    v___x_1781_ = v___x_1777_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
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
                    v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
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
    mut v_e_1794_: *mut LeanObject,
    mut v_a_1795_: *mut LeanObject,
    mut v_a_1796_: *mut LeanObject,
    mut v_a_1797_: *mut LeanObject,
    mut v_a_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
    mut v_a_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
    mut v_a_1802_: *mut LeanObject,
    mut v_a_1803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1812_: u8 = 0;
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: u8 = 0;
    let mut v_arg_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: u8 = 0;
    let mut v_arg_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v_arg_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: u8 = 0;
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: u8 = 0;
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1855_: u8 = 0;
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1868_: u8 = 0;
    let mut v_val_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1872_: u8 = 0;
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v_unused_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1883_: u8 = 0;
    let mut v_a_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v_val_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v_unused_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1924_: u8 = 0;
    let mut v_a_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1928_: u8 = 0;
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1950_: u8 = 0;
    let mut v_val_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1954_: u8 = 0;
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_isSharedCheck_1963_: u8 = 0;
    let mut v_unused_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_a_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v_val_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v_unused_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_a_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v_val_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut v_unused_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut v_a_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v___x_2061_: u8 = 0;
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2073_: u8 = 0;
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v_val_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v_unused_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2097_: u8 = 0;
    let mut v_a_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut v_isSharedCheck_2106_: u8 = 0;
    let mut v_a_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2114_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_unused_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v_val_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2134_: u8 = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2143_: u8 = 0;
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut v_unused_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_a_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2205_: u8 = 0;
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut v_a_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1794_);
                v___x_1808_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1794_, v_a_1801_);
                if lean_obj_tag(v___x_1808_) == 0 {
                    v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
                    v_isSharedCheck_2210_ = (!lean_is_exclusive(v___x_1808_)) as u8;
                    if v_isSharedCheck_2210_ == 0 {
                        v___x_1811_ = v___x_1808_;
                        v_isShared_1812_ = v_isSharedCheck_2210_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1809_);
                        lean_dec(v___x_1808_);
                        v___x_1811_ = lean_box(0);
                        v_isShared_1812_ = v_isSharedCheck_2210_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1794_);
                    v_a_2211_ = lean_ctor_get(v___x_1808_, 0);
                    v_isSharedCheck_2218_ = (!lean_is_exclusive(v___x_1808_)) as u8;
                    if v_isSharedCheck_2218_ == 0 {
                        v___x_2213_ = v___x_1808_;
                        v_isShared_2214_ = v_isSharedCheck_2218_;
                        state = 76;
                        continue;
                    } else {
                        lean_inc(v_a_2211_);
                        lean_dec(v___x_1808_);
                        v___x_2213_ = lean_box(0);
                        v_isShared_2214_ = v_isSharedCheck_2218_;
                        state = 76;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1806_ = lean_box(0);
                v___x_1807_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1807_, 0, v___x_1806_);
                return v___x_1807_;
            }
            2 => {
                v___x_1813_ = l_Lean_Expr_cleanupAnnotations(v_a_1809_);
                v___x_1814_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2;
                v___x_1815_ = l_Lean_Expr_isConstOf(v___x_1813_, v___x_1814_);
                if v___x_1815_ == 0 {
                    lean_del_object(v___x_1811_);
                    v___x_1816_ = l_Lean_Expr_isApp(v___x_1813_);
                    if v___x_1816_ == 0 {
                        lean_dec_ref(v___x_1813_);
                        lean_dec_ref(v_e_1794_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_1817_ = lean_ctor_get(v___x_1813_, 1);
                        lean_inc_ref(v_arg_1817_);
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
                                        lean_dec_ref(v___x_1818_);
                                        lean_dec_ref(v_arg_1817_);
                                        lean_dec_ref(v_e_1794_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_1826_ = lean_ctor_get(v___x_1818_, 1);
                                        lean_inc_ref(v_arg_1826_);
                                        v___x_1827_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_1818_);
                                        v___x_1828_ = l_Lean_Expr_isApp(v___x_1827_);
                                        if v___x_1828_ == 0 {
                                            lean_dec_ref(v___x_1827_);
                                            lean_dec_ref(v_arg_1826_);
                                            lean_dec_ref(v_arg_1817_);
                                            lean_dec_ref(v_e_1794_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_1829_ = lean_ctor_get(v___x_1827_, 1);
                                            lean_inc_ref(v_arg_1829_);
                                            v___x_1830_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_1827_);
                                            v___x_1831_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12;
                                            v___x_1832_ =
                                                l_Lean_Expr_isConstOf(v___x_1830_, v___x_1831_);
                                            if v___x_1832_ == 0 {
                                                lean_dec_ref(v_e_1794_);
                                                v___x_1833_ = l_Lean_Expr_isApp(v___x_1830_);
                                                if v___x_1833_ == 0 {
                                                    lean_dec_ref(v___x_1830_);
                                                    lean_dec_ref(v_arg_1829_);
                                                    lean_dec_ref(v_arg_1826_);
                                                    lean_dec_ref(v_arg_1817_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_1834_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1830_,
                                                    );
                                                    v___x_1835_ = l_Lean_Expr_isApp(v___x_1834_);
                                                    if v___x_1835_ == 0 {
                                                        lean_dec_ref(v___x_1834_);
                                                        lean_dec_ref(v_arg_1829_);
                                                        lean_dec_ref(v_arg_1826_);
                                                        lean_dec_ref(v_arg_1817_);
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
                                                            lean_dec_ref(v___x_1836_);
                                                            lean_dec_ref(v_arg_1829_);
                                                            lean_dec_ref(v_arg_1826_);
                                                            lean_dec_ref(v_arg_1817_);
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
                                                                                lean_dec_ref(
                                                                                    v___x_1838_,
                                                                                );
                                                                                if v___x_1850_ == 0
                                                                                {
                                                                                    lean_dec_ref(
                                                                                        v_arg_1829_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1826_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1817_,
                                                                                    );
                                                                                    state = 1;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_1851_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_1829_, v_a_1801_);
                                                                                    if lean_obj_tag(
                                                                                        v___x_1851_,
                                                                                    ) == 0
                                                                                    {
                                                                                        v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
                                                                                        v_isSharedCheck_1883_ = (!lean_is_exclusive(v___x_1851_)) as u8;
                                                                                        if v_isSharedCheck_1883_ == 0 {
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1883_;
state = 3; continue;
} else {
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1883_;
state = 3; continue;
}
                                                                                    } else {
                                                                                        lean_dec_ref(v_arg_1826_);
                                                                                        lean_dec_ref(v_arg_1817_);
                                                                                        v_a_1884_ = lean_ctor_get(v___x_1851_, 0);
                                                                                        v_isSharedCheck_1891_ = (!lean_is_exclusive(v___x_1851_)) as u8;
                                                                                        if v_isSharedCheck_1891_ == 0 {
v___x_1886_ = v___x_1851_;
v_isShared_1887_ = v_isSharedCheck_1891_;
state = 9; continue;
} else {
lean_inc(v_a_1884_);
lean_dec(v___x_1851_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
state = 9; continue;
}
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v___x_1838_,
                                                                                );
                                                                                v___x_1892_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_1829_, v_a_1801_);
                                                                                if lean_obj_tag(
                                                                                    v___x_1892_,
                                                                                ) == 0
                                                                                {
                                                                                    v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
                                                                                    v_isSharedCheck_1924_ = (!lean_is_exclusive(v___x_1892_)) as u8;
                                                                                    if v_isSharedCheck_1924_ == 0 {
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1924_;
state = 11; continue;
} else {
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1924_;
state = 11; continue;
}
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_arg_1826_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1817_,
                                                                                    );
                                                                                    v_a_1925_ = lean_ctor_get(v___x_1892_, 0);
                                                                                    v_isSharedCheck_1932_ = (!lean_is_exclusive(v___x_1892_)) as u8;
                                                                                    if v_isSharedCheck_1932_ == 0 {
v___x_1927_ = v___x_1892_;
v_isShared_1928_ = v_isSharedCheck_1932_;
state = 17; continue;
} else {
lean_inc(v_a_1925_);
lean_dec(v___x_1892_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
state = 17; continue;
}
                                                                                }
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v___x_1838_,
                                                                            );
                                                                            v___x_1933_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_1829_, v_a_1801_);
                                                                            if lean_obj_tag(
                                                                                v___x_1933_,
                                                                            ) == 0
                                                                            {
                                                                                v_a_1934_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_1933_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_1965_ = (!lean_is_exclusive(v___x_1933_)) as u8;
                                                                                if v_isSharedCheck_1965_ == 0 {
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1965_;
state = 19; continue;
} else {
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1965_;
state = 19; continue;
}
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_1826_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1817_,
                                                                                );
                                                                                v_a_1966_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_1933_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_1973_ = (!lean_is_exclusive(v___x_1933_)) as u8;
                                                                                if v_isSharedCheck_1973_ == 0 {
v___x_1968_ = v___x_1933_;
v_isShared_1969_ = v_isSharedCheck_1973_;
state = 25; continue;
} else {
lean_inc(v_a_1966_);
lean_dec(v___x_1933_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
state = 25; continue;
}
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v___x_1838_);
                                                                        v___x_1974_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_1829_, v_a_1801_);
                                                                        if lean_obj_tag(v___x_1974_)
                                                                            == 0
                                                                        {
                                                                            v_a_1975_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1974_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_2006_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_1974_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_2006_
                                                                                == 0
                                                                            {
                                                                                v___x_1977_ =
                                                                                    v___x_1974_;
                                                                                v_isShared_1978_ = v_isSharedCheck_2006_;
                                                                                state = 27;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_1975_);
                                                                                lean_dec(
                                                                                    v___x_1974_,
                                                                                );
                                                                                v___x_1977_ =
                                                                                    lean_box(0);
                                                                                v_isShared_1978_ = v_isSharedCheck_2006_;
                                                                                state = 27;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_1826_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1817_,
                                                                            );
                                                                            v_a_2007_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1974_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_2014_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_1974_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_2014_
                                                                                == 0
                                                                            {
                                                                                v___x_2009_ =
                                                                                    v___x_1974_;
                                                                                v_isShared_2010_ = v_isSharedCheck_2014_;
                                                                                state = 33;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_2007_);
                                                                                lean_dec(
                                                                                    v___x_1974_,
                                                                                );
                                                                                v___x_2009_ =
                                                                                    lean_box(0);
                                                                                v_isShared_2010_ = v_isSharedCheck_2014_;
                                                                                state = 33;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v___x_1838_);
                                                                    v___x_2015_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_1829_, v_a_1801_);
                                                                    if lean_obj_tag(v___x_2015_)
                                                                        == 0
                                                                    {
                                                                        v_a_2016_ = lean_ctor_get(
                                                                            v___x_2015_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_2047_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_2015_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_2047_
                                                                            == 0
                                                                        {
                                                                            v___x_2018_ =
                                                                                v___x_2015_;
                                                                            v_isShared_2019_ = v_isSharedCheck_2047_;
                                                                            state = 35;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_2016_);
                                                                            lean_dec(v___x_2015_);
                                                                            v___x_2018_ =
                                                                                lean_box(0);
                                                                            v_isShared_2019_ = v_isSharedCheck_2047_;
                                                                            state = 35;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_1826_);
                                                                        lean_dec_ref(v_arg_1817_);
                                                                        v_a_2048_ = lean_ctor_get(
                                                                            v___x_2015_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_2055_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_2015_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_2055_
                                                                            == 0
                                                                        {
                                                                            v___x_2050_ =
                                                                                v___x_2015_;
                                                                            v_isShared_2051_ = v_isSharedCheck_2055_;
                                                                            state = 41;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_2048_);
                                                                            lean_dec(v___x_2015_);
                                                                            v___x_2050_ =
                                                                                lean_box(0);
                                                                            v_isShared_2051_ = v_isSharedCheck_2055_;
                                                                            state = 41;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_1838_);
                                                                v___x_2056_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_1829_, v_a_1801_);
                                                                if lean_obj_tag(v___x_2056_) == 0 {
                                                                    v_a_2057_ = lean_ctor_get(
                                                                        v___x_2056_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_2106_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_2056_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_2106_ == 0 {
                                                                        v___x_2059_ = v___x_2056_;
                                                                        v_isShared_2060_ =
                                                                            v_isSharedCheck_2106_;
                                                                        state = 43;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_2057_);
                                                                        lean_dec(v___x_2056_);
                                                                        v___x_2059_ = lean_box(0);
                                                                        v_isShared_2060_ =
                                                                            v_isSharedCheck_2106_;
                                                                        state = 43;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_arg_1826_);
                                                                    lean_dec_ref(v_arg_1817_);
                                                                    v_a_2107_ = lean_ctor_get(
                                                                        v___x_2056_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_2114_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_2056_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_2114_ == 0 {
                                                                        v___x_2109_ = v___x_2056_;
                                                                        v_isShared_2110_ =
                                                                            v_isSharedCheck_2114_;
                                                                        state = 53;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_2107_);
                                                                        lean_dec(v___x_2056_);
                                                                        v___x_2109_ = lean_box(0);
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
                                                lean_dec_ref(v___x_1830_);
                                                lean_dec_ref(v_arg_1829_);
                                                lean_dec_ref(v_arg_1826_);
                                                lean_dec_ref(v_arg_1817_);
                                                v___x_2115_ = l_Lean_Meta_getNatValue_x3f(
                                                    v_e_1794_, v_a_1800_, v_a_1801_, v_a_1802_,
                                                    v_a_1803_,
                                                );
                                                lean_dec_ref(v_e_1794_);
                                                if lean_obj_tag(v___x_2115_) == 0 {
                                                    v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
                                                    lean_inc(v_a_2116_);
                                                    if lean_obj_tag(v_a_2116_) == 1 {
                                                        lean_dec_ref_known(v_a_2116_, 1);
                                                        return v___x_2115_;
                                                    } else {
                                                        lean_dec(v_a_2116_);
                                                        v_isSharedCheck_2124_ =
                                                            (!lean_is_exclusive(v___x_2115_)) as u8;
                                                        if v_isSharedCheck_2124_ == 0 {
                                                            v_unused_2125_ =
                                                                lean_ctor_get(v___x_2115_, 0);
                                                            lean_dec(v_unused_2125_);
                                                            v___x_2118_ = v___x_2115_;
                                                            v_isShared_2119_ =
                                                                v_isSharedCheck_2124_;
                                                            state = 55;
                                                            continue;
                                                        } else {
                                                            lean_dec(v___x_2115_);
                                                            v___x_2118_ = lean_box(0);
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
                                    lean_dec_ref(v___x_1818_);
                                    lean_dec_ref(v_e_1794_);
                                    v___x_2126_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                                    if lean_obj_tag(v___x_2126_) == 0 {
                                        v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
                                        lean_inc(v_a_2127_);
                                        if lean_obj_tag(v_a_2127_) == 0 {
                                            return v___x_2126_;
                                        } else {
                                            v_isSharedCheck_2144_ =
                                                (!lean_is_exclusive(v___x_2126_)) as u8;
                                            if v_isSharedCheck_2144_ == 0 {
                                                v_unused_2145_ = lean_ctor_get(v___x_2126_, 0);
                                                lean_dec(v_unused_2145_);
                                                v___x_2129_ = v___x_2126_;
                                                v_isShared_2130_ = v_isSharedCheck_2144_;
                                                state = 57;
                                                continue;
                                            } else {
                                                lean_dec(v___x_2126_);
                                                v___x_2129_ = lean_box(0);
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
                                lean_dec_ref(v___x_1818_);
                                lean_dec_ref(v_e_1794_);
                                v___x_2146_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                                if lean_obj_tag(v___x_2146_) == 0 {
                                    v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
                                    v_isSharedCheck_2167_ = (!lean_is_exclusive(v___x_2146_)) as u8;
                                    if v_isSharedCheck_2167_ == 0 {
                                        v___x_2149_ = v___x_2146_;
                                        v_isShared_2150_ = v_isSharedCheck_2167_;
                                        state = 61;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2147_);
                                        lean_dec(v___x_2146_);
                                        v___x_2149_ = lean_box(0);
                                        v_isShared_2150_ = v_isSharedCheck_2167_;
                                        state = 61;
                                        continue;
                                    }
                                } else {
                                    v_a_2168_ = lean_ctor_get(v___x_2146_, 0);
                                    v_isSharedCheck_2175_ = (!lean_is_exclusive(v___x_2146_)) as u8;
                                    if v_isSharedCheck_2175_ == 0 {
                                        v___x_2170_ = v___x_2146_;
                                        v_isShared_2171_ = v_isSharedCheck_2175_;
                                        state = 66;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2168_);
                                        lean_dec(v___x_2146_);
                                        v___x_2170_ = lean_box(0);
                                        v_isShared_2171_ = v_isSharedCheck_2175_;
                                        state = 66;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_1818_);
                            lean_dec_ref(v_e_1794_);
                            v___x_2176_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if lean_obj_tag(v___x_2176_) == 0 {
                                v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
                                v_isSharedCheck_2197_ = (!lean_is_exclusive(v___x_2176_)) as u8;
                                if v_isSharedCheck_2197_ == 0 {
                                    v___x_2179_ = v___x_2176_;
                                    v_isShared_2180_ = v_isSharedCheck_2197_;
                                    state = 68;
                                    continue;
                                } else {
                                    lean_inc(v_a_2177_);
                                    lean_dec(v___x_2176_);
                                    v___x_2179_ = lean_box(0);
                                    v_isShared_2180_ = v_isSharedCheck_2197_;
                                    state = 68;
                                    continue;
                                }
                            } else {
                                v_a_2198_ = lean_ctor_get(v___x_2176_, 0);
                                v_isSharedCheck_2205_ = (!lean_is_exclusive(v___x_2176_)) as u8;
                                if v_isSharedCheck_2205_ == 0 {
                                    v___x_2200_ = v___x_2176_;
                                    v_isShared_2201_ = v_isSharedCheck_2205_;
                                    state = 73;
                                    continue;
                                } else {
                                    lean_inc(v_a_2198_);
                                    lean_dec(v___x_2176_);
                                    v___x_2200_ = lean_box(0);
                                    v_isShared_2201_ = v_isSharedCheck_2205_;
                                    state = 73;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1813_);
                    lean_dec_ref(v_e_1794_);
                    v___x_2206_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31;
                    if v_isShared_1812_ == 0 {
                        lean_ctor_set(v___x_1811_, 0, v___x_2206_);
                        v___x_2208_ = v___x_1811_;
                        state = 75;
                        continue;
                    } else {
                        v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
                        v___x_2208_ = v_reuseFailAlloc_2209_;
                        state = 75;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1856_ = (lean_unbox(v_a_1852_) as u8);
                lean_dec(v_a_1852_);
                if v___x_1856_ == 0 {
                    lean_dec_ref(v_arg_1826_);
                    lean_dec_ref(v_arg_1817_);
                    v___x_1857_ = lean_box(0);
                    if v_isShared_1855_ == 0 {
                        lean_ctor_set(v___x_1854_, 0, v___x_1857_);
                        v___x_1859_ = v___x_1854_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
                        v___x_1859_ = v_reuseFailAlloc_1860_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1854_);
                    v___x_1861_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if lean_obj_tag(v___x_1861_) == 0 {
                        v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
                        lean_inc(v_a_1862_);
                        if lean_obj_tag(v_a_1862_) == 0 {
                            lean_dec_ref(v_arg_1817_);
                            return v___x_1861_;
                        } else {
                            lean_dec_ref_known(v___x_1861_, 1);
                            v_val_1863_ = lean_ctor_get(v_a_1862_, 0);
                            lean_inc(v_val_1863_);
                            lean_dec_ref_known(v_a_1862_, 1);
                            v___x_1864_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if lean_obj_tag(v___x_1864_) == 0 {
                                v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
                                lean_inc(v_a_1865_);
                                if lean_obj_tag(v_a_1865_) == 0 {
                                    lean_dec(v_val_1863_);
                                    return v___x_1864_;
                                } else {
                                    v_isSharedCheck_1881_ = (!lean_is_exclusive(v___x_1864_)) as u8;
                                    if v_isSharedCheck_1881_ == 0 {
                                        v_unused_1882_ = lean_ctor_get(v___x_1864_, 0);
                                        lean_dec(v_unused_1882_);
                                        v___x_1867_ = v___x_1864_;
                                        v_isShared_1868_ = v_isSharedCheck_1881_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1864_);
                                        v___x_1867_ = lean_box(0);
                                        v_isShared_1868_ = v_isSharedCheck_1881_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1863_);
                                return v___x_1864_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1817_);
                        return v___x_1861_;
                    }
                }
            }
            4 => {
                return v___x_1859_;
            }
            5 => {
                v_val_1869_ = lean_ctor_get(v_a_1865_, 0);
                v_isSharedCheck_1880_ = (!lean_is_exclusive(v_a_1865_)) as u8;
                if v_isSharedCheck_1880_ == 0 {
                    v___x_1871_ = v_a_1865_;
                    v_isShared_1872_ = v_isSharedCheck_1880_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_val_1869_);
                    lean_dec(v_a_1865_);
                    v___x_1871_ = lean_box(0);
                    v_isShared_1872_ = v_isSharedCheck_1880_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1873_ = lean_nat_add(v_val_1863_, v_val_1869_);
                lean_dec(v_val_1869_);
                lean_dec(v_val_1863_);
                if v_isShared_1872_ == 0 {
                    lean_ctor_set(v___x_1871_, 0, v___x_1873_);
                    v___x_1875_ = v___x_1871_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1873_);
                    v___x_1875_ = v_reuseFailAlloc_1879_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1868_ == 0 {
                    lean_ctor_set(v___x_1867_, 0, v___x_1875_);
                    v___x_1877_ = v___x_1867_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
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
                    v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
                    v___x_1889_ = v_reuseFailAlloc_1890_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1889_;
            }
            11 => {
                v___x_1897_ = (lean_unbox(v_a_1893_) as u8);
                lean_dec(v_a_1893_);
                if v___x_1897_ == 0 {
                    lean_dec_ref(v_arg_1826_);
                    lean_dec_ref(v_arg_1817_);
                    v___x_1898_ = lean_box(0);
                    if v_isShared_1896_ == 0 {
                        lean_ctor_set(v___x_1895_, 0, v___x_1898_);
                        v___x_1900_ = v___x_1895_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
                        v___x_1900_ = v_reuseFailAlloc_1901_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1895_);
                    v___x_1902_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if lean_obj_tag(v___x_1902_) == 0 {
                        v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
                        lean_inc(v_a_1903_);
                        if lean_obj_tag(v_a_1903_) == 0 {
                            lean_dec_ref(v_arg_1817_);
                            return v___x_1902_;
                        } else {
                            lean_dec_ref_known(v___x_1902_, 1);
                            v_val_1904_ = lean_ctor_get(v_a_1903_, 0);
                            lean_inc(v_val_1904_);
                            lean_dec_ref_known(v_a_1903_, 1);
                            v___x_1905_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if lean_obj_tag(v___x_1905_) == 0 {
                                v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
                                lean_inc(v_a_1906_);
                                if lean_obj_tag(v_a_1906_) == 0 {
                                    lean_dec(v_val_1904_);
                                    return v___x_1905_;
                                } else {
                                    v_isSharedCheck_1922_ = (!lean_is_exclusive(v___x_1905_)) as u8;
                                    if v_isSharedCheck_1922_ == 0 {
                                        v_unused_1923_ = lean_ctor_get(v___x_1905_, 0);
                                        lean_dec(v_unused_1923_);
                                        v___x_1908_ = v___x_1905_;
                                        v_isShared_1909_ = v_isSharedCheck_1922_;
                                        state = 13;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1905_);
                                        v___x_1908_ = lean_box(0);
                                        v_isShared_1909_ = v_isSharedCheck_1922_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1904_);
                                return v___x_1905_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1817_);
                        return v___x_1902_;
                    }
                }
            }
            12 => {
                return v___x_1900_;
            }
            13 => {
                v_val_1910_ = lean_ctor_get(v_a_1906_, 0);
                v_isSharedCheck_1921_ = (!lean_is_exclusive(v_a_1906_)) as u8;
                if v_isSharedCheck_1921_ == 0 {
                    v___x_1912_ = v_a_1906_;
                    v_isShared_1913_ = v_isSharedCheck_1921_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_val_1910_);
                    lean_dec(v_a_1906_);
                    v___x_1912_ = lean_box(0);
                    v_isShared_1913_ = v_isSharedCheck_1921_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1914_ = lean_nat_mul(v_val_1904_, v_val_1910_);
                lean_dec(v_val_1910_);
                lean_dec(v_val_1904_);
                if v_isShared_1913_ == 0 {
                    lean_ctor_set(v___x_1912_, 0, v___x_1914_);
                    v___x_1916_ = v___x_1912_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1914_);
                    v___x_1916_ = v_reuseFailAlloc_1920_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1909_ == 0 {
                    lean_ctor_set(v___x_1908_, 0, v___x_1916_);
                    v___x_1918_ = v___x_1908_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
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
                    v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
                    v___x_1930_ = v_reuseFailAlloc_1931_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1930_;
            }
            19 => {
                v___x_1938_ = (lean_unbox(v_a_1934_) as u8);
                lean_dec(v_a_1934_);
                if v___x_1938_ == 0 {
                    lean_dec_ref(v_arg_1826_);
                    lean_dec_ref(v_arg_1817_);
                    v___x_1939_ = lean_box(0);
                    if v_isShared_1937_ == 0 {
                        lean_ctor_set(v___x_1936_, 0, v___x_1939_);
                        v___x_1941_ = v___x_1936_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
                        v___x_1941_ = v_reuseFailAlloc_1942_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1936_);
                    v___x_1943_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if lean_obj_tag(v___x_1943_) == 0 {
                        v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
                        lean_inc(v_a_1944_);
                        if lean_obj_tag(v_a_1944_) == 0 {
                            lean_dec_ref(v_arg_1817_);
                            return v___x_1943_;
                        } else {
                            lean_dec_ref_known(v___x_1943_, 1);
                            v_val_1945_ = lean_ctor_get(v_a_1944_, 0);
                            lean_inc(v_val_1945_);
                            lean_dec_ref_known(v_a_1944_, 1);
                            v___x_1946_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if lean_obj_tag(v___x_1946_) == 0 {
                                v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
                                lean_inc(v_a_1947_);
                                if lean_obj_tag(v_a_1947_) == 0 {
                                    lean_dec(v_val_1945_);
                                    return v___x_1946_;
                                } else {
                                    v_isSharedCheck_1963_ = (!lean_is_exclusive(v___x_1946_)) as u8;
                                    if v_isSharedCheck_1963_ == 0 {
                                        v_unused_1964_ = lean_ctor_get(v___x_1946_, 0);
                                        lean_dec(v_unused_1964_);
                                        v___x_1949_ = v___x_1946_;
                                        v_isShared_1950_ = v_isSharedCheck_1963_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1946_);
                                        v___x_1949_ = lean_box(0);
                                        v_isShared_1950_ = v_isSharedCheck_1963_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1945_);
                                return v___x_1946_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1817_);
                        return v___x_1943_;
                    }
                }
            }
            20 => {
                return v___x_1941_;
            }
            21 => {
                v_val_1951_ = lean_ctor_get(v_a_1947_, 0);
                v_isSharedCheck_1962_ = (!lean_is_exclusive(v_a_1947_)) as u8;
                if v_isSharedCheck_1962_ == 0 {
                    v___x_1953_ = v_a_1947_;
                    v_isShared_1954_ = v_isSharedCheck_1962_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_val_1951_);
                    lean_dec(v_a_1947_);
                    v___x_1953_ = lean_box(0);
                    v_isShared_1954_ = v_isSharedCheck_1962_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1955_ = lean_nat_sub(v_val_1945_, v_val_1951_);
                lean_dec(v_val_1951_);
                lean_dec(v_val_1945_);
                if v_isShared_1954_ == 0 {
                    lean_ctor_set(v___x_1953_, 0, v___x_1955_);
                    v___x_1957_ = v___x_1953_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1955_);
                    v___x_1957_ = v_reuseFailAlloc_1961_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1950_ == 0 {
                    lean_ctor_set(v___x_1949_, 0, v___x_1957_);
                    v___x_1959_ = v___x_1949_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
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
                    v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1971_;
            }
            27 => {
                v___x_1979_ = (lean_unbox(v_a_1975_) as u8);
                lean_dec(v_a_1975_);
                if v___x_1979_ == 0 {
                    lean_dec_ref(v_arg_1826_);
                    lean_dec_ref(v_arg_1817_);
                    v___x_1980_ = lean_box(0);
                    if v_isShared_1978_ == 0 {
                        lean_ctor_set(v___x_1977_, 0, v___x_1980_);
                        v___x_1982_ = v___x_1977_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
                        v___x_1982_ = v_reuseFailAlloc_1983_;
                        state = 28;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1977_);
                    v___x_1984_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if lean_obj_tag(v___x_1984_) == 0 {
                        v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
                        lean_inc(v_a_1985_);
                        if lean_obj_tag(v_a_1985_) == 0 {
                            lean_dec_ref(v_arg_1817_);
                            return v___x_1984_;
                        } else {
                            lean_dec_ref_known(v___x_1984_, 1);
                            v_val_1986_ = lean_ctor_get(v_a_1985_, 0);
                            lean_inc(v_val_1986_);
                            lean_dec_ref_known(v_a_1985_, 1);
                            v___x_1987_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if lean_obj_tag(v___x_1987_) == 0 {
                                v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
                                lean_inc(v_a_1988_);
                                if lean_obj_tag(v_a_1988_) == 0 {
                                    lean_dec(v_val_1986_);
                                    return v___x_1987_;
                                } else {
                                    v_isSharedCheck_2004_ = (!lean_is_exclusive(v___x_1987_)) as u8;
                                    if v_isSharedCheck_2004_ == 0 {
                                        v_unused_2005_ = lean_ctor_get(v___x_1987_, 0);
                                        lean_dec(v_unused_2005_);
                                        v___x_1990_ = v___x_1987_;
                                        v_isShared_1991_ = v_isSharedCheck_2004_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1987_);
                                        v___x_1990_ = lean_box(0);
                                        v_isShared_1991_ = v_isSharedCheck_2004_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1986_);
                                return v___x_1987_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1817_);
                        return v___x_1984_;
                    }
                }
            }
            28 => {
                return v___x_1982_;
            }
            29 => {
                v_val_1992_ = lean_ctor_get(v_a_1988_, 0);
                v_isSharedCheck_2003_ = (!lean_is_exclusive(v_a_1988_)) as u8;
                if v_isSharedCheck_2003_ == 0 {
                    v___x_1994_ = v_a_1988_;
                    v_isShared_1995_ = v_isSharedCheck_2003_;
                    state = 30;
                    continue;
                } else {
                    lean_inc(v_val_1992_);
                    lean_dec(v_a_1988_);
                    v___x_1994_ = lean_box(0);
                    v_isShared_1995_ = v_isSharedCheck_2003_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1996_ = lean_nat_div(v_val_1986_, v_val_1992_);
                lean_dec(v_val_1992_);
                lean_dec(v_val_1986_);
                if v_isShared_1995_ == 0 {
                    lean_ctor_set(v___x_1994_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1994_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1996_);
                    v___x_1998_ = v_reuseFailAlloc_2002_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_1991_ == 0 {
                    lean_ctor_set(v___x_1990_, 0, v___x_1998_);
                    v___x_2000_ = v___x_1990_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
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
                    v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
                    v___x_2012_ = v_reuseFailAlloc_2013_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2012_;
            }
            35 => {
                v___x_2020_ = (lean_unbox(v_a_2016_) as u8);
                lean_dec(v_a_2016_);
                if v___x_2020_ == 0 {
                    lean_dec_ref(v_arg_1826_);
                    lean_dec_ref(v_arg_1817_);
                    v___x_2021_ = lean_box(0);
                    if v_isShared_2019_ == 0 {
                        lean_ctor_set(v___x_2018_, 0, v___x_2021_);
                        v___x_2023_ = v___x_2018_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
                        v___x_2023_ = v_reuseFailAlloc_2024_;
                        state = 36;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2018_);
                    v___x_2025_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if lean_obj_tag(v___x_2025_) == 0 {
                        v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
                        lean_inc(v_a_2026_);
                        if lean_obj_tag(v_a_2026_) == 0 {
                            lean_dec_ref(v_arg_1817_);
                            return v___x_2025_;
                        } else {
                            lean_dec_ref_known(v___x_2025_, 1);
                            v_val_2027_ = lean_ctor_get(v_a_2026_, 0);
                            lean_inc(v_val_2027_);
                            lean_dec_ref_known(v_a_2026_, 1);
                            v___x_2028_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                            if lean_obj_tag(v___x_2028_) == 0 {
                                v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
                                lean_inc(v_a_2029_);
                                if lean_obj_tag(v_a_2029_) == 0 {
                                    lean_dec(v_val_2027_);
                                    return v___x_2028_;
                                } else {
                                    v_isSharedCheck_2045_ = (!lean_is_exclusive(v___x_2028_)) as u8;
                                    if v_isSharedCheck_2045_ == 0 {
                                        v_unused_2046_ = lean_ctor_get(v___x_2028_, 0);
                                        lean_dec(v_unused_2046_);
                                        v___x_2031_ = v___x_2028_;
                                        v_isShared_2032_ = v_isSharedCheck_2045_;
                                        state = 37;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2028_);
                                        v___x_2031_ = lean_box(0);
                                        v_isShared_2032_ = v_isSharedCheck_2045_;
                                        state = 37;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2027_);
                                return v___x_2028_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1817_);
                        return v___x_2025_;
                    }
                }
            }
            36 => {
                return v___x_2023_;
            }
            37 => {
                v_val_2033_ = lean_ctor_get(v_a_2029_, 0);
                v_isSharedCheck_2044_ = (!lean_is_exclusive(v_a_2029_)) as u8;
                if v_isSharedCheck_2044_ == 0 {
                    v___x_2035_ = v_a_2029_;
                    v_isShared_2036_ = v_isSharedCheck_2044_;
                    state = 38;
                    continue;
                } else {
                    lean_inc(v_val_2033_);
                    lean_dec(v_a_2029_);
                    v___x_2035_ = lean_box(0);
                    v_isShared_2036_ = v_isSharedCheck_2044_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_2037_ = lean_nat_mod(v_val_2027_, v_val_2033_);
                lean_dec(v_val_2033_);
                lean_dec(v_val_2027_);
                if v_isShared_2036_ == 0 {
                    lean_ctor_set(v___x_2035_, 0, v___x_2037_);
                    v___x_2039_ = v___x_2035_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2037_);
                    v___x_2039_ = v_reuseFailAlloc_2043_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_2032_ == 0 {
                    lean_ctor_set(v___x_2031_, 0, v___x_2039_);
                    v___x_2041_ = v___x_2031_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
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
                    v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
                    v___x_2053_ = v_reuseFailAlloc_2054_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2053_;
            }
            43 => {
                v___x_2061_ = (lean_unbox(v_a_2057_) as u8);
                lean_dec(v_a_2057_);
                if v___x_2061_ == 0 {
                    lean_dec_ref(v_arg_1826_);
                    lean_dec_ref(v_arg_1817_);
                    v___x_2062_ = lean_box(0);
                    if v_isShared_2060_ == 0 {
                        lean_ctor_set(v___x_2059_, 0, v___x_2062_);
                        v___x_2064_ = v___x_2059_;
                        state = 44;
                        continue;
                    } else {
                        v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
                        v___x_2064_ = v_reuseFailAlloc_2065_;
                        state = 44;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2059_);
                    v___x_2066_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1817_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if lean_obj_tag(v___x_2066_) == 0 {
                        v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
                        lean_inc(v_a_2067_);
                        if lean_obj_tag(v_a_2067_) == 0 {
                            lean_dec_ref(v_arg_1826_);
                            return v___x_2066_;
                        } else {
                            lean_dec_ref_known(v___x_2066_, 1);
                            v_val_2068_ = lean_ctor_get(v_a_2067_, 0);
                            lean_inc_n(v_val_2068_, 2);
                            lean_dec_ref_known(v_a_2067_, 1);
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
                            if lean_obj_tag(v___x_2069_) == 0 {
                                v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
                                v_isSharedCheck_2097_ = (!lean_is_exclusive(v___x_2069_)) as u8;
                                if v_isSharedCheck_2097_ == 0 {
                                    v___x_2072_ = v___x_2069_;
                                    v_isShared_2073_ = v_isSharedCheck_2097_;
                                    state = 45;
                                    continue;
                                } else {
                                    lean_inc(v_a_2070_);
                                    lean_dec(v___x_2069_);
                                    v___x_2072_ = lean_box(0);
                                    v_isShared_2073_ = v_isSharedCheck_2097_;
                                    state = 45;
                                    continue;
                                }
                            } else {
                                lean_dec(v_val_2068_);
                                lean_dec_ref(v_arg_1826_);
                                v_a_2098_ = lean_ctor_get(v___x_2069_, 0);
                                v_isSharedCheck_2105_ = (!lean_is_exclusive(v___x_2069_)) as u8;
                                if v_isSharedCheck_2105_ == 0 {
                                    v___x_2100_ = v___x_2069_;
                                    v_isShared_2101_ = v_isSharedCheck_2105_;
                                    state = 51;
                                    continue;
                                } else {
                                    lean_inc(v_a_2098_);
                                    lean_dec(v___x_2069_);
                                    v___x_2100_ = lean_box(0);
                                    v_isShared_2101_ = v_isSharedCheck_2105_;
                                    state = 51;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_1826_);
                        return v___x_2066_;
                    }
                }
            }
            44 => {
                return v___x_2064_;
            }
            45 => {
                if lean_obj_tag(v_a_2070_) == 0 {
                    lean_dec(v_val_2068_);
                    lean_dec_ref(v_arg_1826_);
                    v___x_2074_ = lean_box(0);
                    if v_isShared_2073_ == 0 {
                        lean_ctor_set(v___x_2072_, 0, v___x_2074_);
                        v___x_2076_ = v___x_2072_;
                        state = 46;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 46;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_2070_, 1);
                    lean_del_object(v___x_2072_);
                    v___x_2078_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_1826_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
                    if lean_obj_tag(v___x_2078_) == 0 {
                        v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
                        lean_inc(v_a_2079_);
                        if lean_obj_tag(v_a_2079_) == 0 {
                            lean_dec(v_val_2068_);
                            return v___x_2078_;
                        } else {
                            v_isSharedCheck_2095_ = (!lean_is_exclusive(v___x_2078_)) as u8;
                            if v_isSharedCheck_2095_ == 0 {
                                v_unused_2096_ = lean_ctor_get(v___x_2078_, 0);
                                lean_dec(v_unused_2096_);
                                v___x_2081_ = v___x_2078_;
                                v_isShared_2082_ = v_isSharedCheck_2095_;
                                state = 47;
                                continue;
                            } else {
                                lean_dec(v___x_2078_);
                                v___x_2081_ = lean_box(0);
                                v_isShared_2082_ = v_isSharedCheck_2095_;
                                state = 47;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_2068_);
                        return v___x_2078_;
                    }
                }
            }
            46 => {
                return v___x_2076_;
            }
            47 => {
                v_val_2083_ = lean_ctor_get(v_a_2079_, 0);
                v_isSharedCheck_2094_ = (!lean_is_exclusive(v_a_2079_)) as u8;
                if v_isSharedCheck_2094_ == 0 {
                    v___x_2085_ = v_a_2079_;
                    v_isShared_2086_ = v_isSharedCheck_2094_;
                    state = 48;
                    continue;
                } else {
                    lean_inc(v_val_2083_);
                    lean_dec(v_a_2079_);
                    v___x_2085_ = lean_box(0);
                    v_isShared_2086_ = v_isSharedCheck_2094_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                v___x_2087_ = lean_nat_pow(v_val_2083_, v_val_2068_);
                lean_dec(v_val_2068_);
                lean_dec(v_val_2083_);
                if v_isShared_2086_ == 0 {
                    lean_ctor_set(v___x_2085_, 0, v___x_2087_);
                    v___x_2089_ = v___x_2085_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2087_);
                    v___x_2089_ = v_reuseFailAlloc_2093_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_2082_ == 0 {
                    lean_ctor_set(v___x_2081_, 0, v___x_2089_);
                    v___x_2091_ = v___x_2081_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
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
                    v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
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
                    v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
                    v___x_2112_ = v_reuseFailAlloc_2113_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_2112_;
            }
            55 => {
                v___x_2120_ = lean_box(0);
                if v_isShared_2119_ == 0 {
                    lean_ctor_set(v___x_2118_, 0, v___x_2120_);
                    v___x_2122_ = v___x_2118_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
                    v___x_2122_ = v_reuseFailAlloc_2123_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_2122_;
            }
            57 => {
                v_val_2131_ = lean_ctor_get(v_a_2127_, 0);
                v_isSharedCheck_2143_ = (!lean_is_exclusive(v_a_2127_)) as u8;
                if v_isSharedCheck_2143_ == 0 {
                    v___x_2133_ = v_a_2127_;
                    v_isShared_2134_ = v_isSharedCheck_2143_;
                    state = 58;
                    continue;
                } else {
                    lean_inc(v_val_2131_);
                    lean_dec(v_a_2127_);
                    v___x_2133_ = lean_box(0);
                    v_isShared_2134_ = v_isSharedCheck_2143_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_2135_ = lean_unsigned_to_nat(1);
                v___x_2136_ = lean_nat_add(v_val_2131_, v___x_2135_);
                lean_dec(v_val_2131_);
                if v_isShared_2134_ == 0 {
                    lean_ctor_set(v___x_2133_, 0, v___x_2136_);
                    v___x_2138_ = v___x_2133_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2136_);
                    v___x_2138_ = v_reuseFailAlloc_2142_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_2130_ == 0 {
                    lean_ctor_set(v___x_2129_, 0, v___x_2138_);
                    v___x_2140_ = v___x_2129_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
                    v___x_2140_ = v_reuseFailAlloc_2141_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2140_;
            }
            61 => {
                if lean_obj_tag(v_a_2147_) == 0 {
                    v___x_2151_ = lean_box(0);
                    if v_isShared_2150_ == 0 {
                        lean_ctor_set(v___x_2149_, 0, v___x_2151_);
                        v___x_2153_ = v___x_2149_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
                        v___x_2153_ = v_reuseFailAlloc_2154_;
                        state = 62;
                        continue;
                    }
                } else {
                    v_val_2155_ = lean_ctor_get(v_a_2147_, 0);
                    v_isSharedCheck_2166_ = (!lean_is_exclusive(v_a_2147_)) as u8;
                    if v_isSharedCheck_2166_ == 0 {
                        v___x_2157_ = v_a_2147_;
                        v_isShared_2158_ = v_isSharedCheck_2166_;
                        state = 63;
                        continue;
                    } else {
                        lean_inc(v_val_2155_);
                        lean_dec(v_a_2147_);
                        v___x_2157_ = lean_box(0);
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
                lean_dec(v_val_2155_);
                if v_isShared_2158_ == 0 {
                    lean_ctor_set(v___x_2157_, 0, v___x_2159_);
                    v___x_2161_ = v___x_2157_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2159_);
                    v___x_2161_ = v_reuseFailAlloc_2165_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                if v_isShared_2150_ == 0 {
                    lean_ctor_set(v___x_2149_, 0, v___x_2161_);
                    v___x_2163_ = v___x_2149_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
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
                    v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2173_;
            }
            68 => {
                if lean_obj_tag(v_a_2177_) == 0 {
                    v___x_2181_ = lean_box(0);
                    if v_isShared_2180_ == 0 {
                        lean_ctor_set(v___x_2179_, 0, v___x_2181_);
                        v___x_2183_ = v___x_2179_;
                        state = 69;
                        continue;
                    } else {
                        v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
                        v___x_2183_ = v_reuseFailAlloc_2184_;
                        state = 69;
                        continue;
                    }
                } else {
                    v_val_2185_ = lean_ctor_get(v_a_2177_, 0);
                    v_isSharedCheck_2196_ = (!lean_is_exclusive(v_a_2177_)) as u8;
                    if v_isSharedCheck_2196_ == 0 {
                        v___x_2187_ = v_a_2177_;
                        v_isShared_2188_ = v_isSharedCheck_2196_;
                        state = 70;
                        continue;
                    } else {
                        lean_inc(v_val_2185_);
                        lean_dec(v_a_2177_);
                        v___x_2187_ = lean_box(0);
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
                lean_dec(v_val_2185_);
                if v_isShared_2188_ == 0 {
                    lean_ctor_set(v___x_2187_, 0, v___x_2189_);
                    v___x_2191_ = v___x_2187_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
                    v___x_2191_ = v_reuseFailAlloc_2195_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_2180_ == 0 {
                    lean_ctor_set(v___x_2179_, 0, v___x_2191_);
                    v___x_2193_ = v___x_2179_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
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
                    v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
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
                    v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
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
    mut v_e_2219_: *mut LeanObject,
    mut v_a_2220_: *mut LeanObject,
    mut v_a_2221_: *mut LeanObject,
    mut v_a_2222_: *mut LeanObject,
    mut v_a_2223_: *mut LeanObject,
    mut v_a_2224_: *mut LeanObject,
    mut v_a_2225_: *mut LeanObject,
    mut v_a_2226_: *mut LeanObject,
    mut v_a_2227_: *mut LeanObject,
    mut v_a_2228_: *mut LeanObject,
    mut v_a_2229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2230_: *mut LeanObject = core::ptr::null_mut();
    v_res_2230_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(
            v_e_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_,
            v_a_2227_, v_a_2228_,
        );
    lean_dec(v_a_2228_);
    lean_dec_ref(v_a_2227_);
    lean_dec(v_a_2226_);
    lean_dec_ref(v_a_2225_);
    lean_dec(v_a_2224_);
    lean_dec_ref(v_a_2223_);
    lean_dec(v_a_2222_);
    lean_dec_ref(v_a_2221_);
    lean_dec(v_a_2220_);
    return v_res_2230_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(
    mut v_e_2231_: *mut LeanObject,
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
    v_res_2242_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(
            v_e_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_,
            v_a_2239_, v_a_2240_,
        );
    lean_dec(v_a_2240_);
    lean_dec_ref(v_a_2239_);
    lean_dec(v_a_2238_);
    lean_dec_ref(v_a_2237_);
    lean_dec(v_a_2236_);
    lean_dec_ref(v_a_2235_);
    lean_dec(v_a_2234_);
    lean_dec_ref(v_a_2233_);
    lean_dec(v_a_2232_);
    return v_res_2242_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(
    mut v_a_2243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    v___x_2244_ = lean_nat_to_int(v_a_2243_);
    return v___x_2244_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalNat_x3f(
    mut v_e_2245_: *mut LeanObject,
    mut v_a_2246_: *mut LeanObject,
    mut v_a_2247_: *mut LeanObject,
    mut v_a_2248_: *mut LeanObject,
    mut v_a_2249_: *mut LeanObject,
    mut v_a_2250_: *mut LeanObject,
    mut v_a_2251_: *mut LeanObject,
    mut v_a_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
    mut v_a_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    v___x_2256_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(
            v_e_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_,
            v_a_2253_, v_a_2254_,
        );
    return v___x_2256_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(
    mut v_e_2257_: *mut LeanObject,
    mut v_a_2258_: *mut LeanObject,
    mut v_a_2259_: *mut LeanObject,
    mut v_a_2260_: *mut LeanObject,
    mut v_a_2261_: *mut LeanObject,
    mut v_a_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
    mut v_a_2265_: *mut LeanObject,
    mut v_a_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2268_: *mut LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(
        v_e_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_,
        v_a_2265_, v_a_2266_,
    );
    lean_dec(v_a_2266_);
    lean_dec_ref(v_a_2265_);
    lean_dec(v_a_2264_);
    lean_dec_ref(v_a_2263_);
    lean_dec(v_a_2262_);
    lean_dec_ref(v_a_2261_);
    lean_dec(v_a_2260_);
    lean_dec_ref(v_a_2259_);
    lean_dec(v_a_2258_);
    return v_res_2268_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalInt_x3f(
    mut v_e_2269_: *mut LeanObject,
    mut v_a_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
    mut v_a_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_a_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    v___x_2280_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(
            v_e_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_,
            v_a_2277_, v_a_2278_,
        );
    return v___x_2280_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(
    mut v_e_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
    mut v_a_2289_: *mut LeanObject,
    mut v_a_2290_: *mut LeanObject,
    mut v_a_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2292_: *mut LeanObject = core::ptr::null_mut();
    v_res_2292_ = l_Lean_Meta_Grind_Arith_evalInt_x3f(
        v_e_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_,
        v_a_2289_, v_a_2290_,
    );
    lean_dec(v_a_2290_);
    lean_dec_ref(v_a_2289_);
    lean_dec(v_a_2288_);
    lean_dec_ref(v_a_2287_);
    lean_dec(v_a_2286_);
    lean_dec_ref(v_a_2285_);
    lean_dec(v_a_2284_);
    lean_dec_ref(v_a_2283_);
    lean_dec(v_a_2282_);
    return v_res_2292_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_IntInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
}
