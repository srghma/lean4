// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Init.Data.Int.OfNat Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt Lean.Meta.NatInstTesters
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isConstOf, l_Lean_Int_mkType,
    l_Lean_eagerReflBoolTrue, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkIntAdd, l_Lean_mkIntDiv, l_Lean_mkIntLit, l_Lean_mkIntMod,
    l_Lean_mkIntMul, l_Lean_mkIntNatCast, l_Lean_mkIntPowNat,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
};
use crate::r#gen::Lean::Meta::IntInstTesters::{
    l_Lean_Meta_Structural_isInstHAddInt___redArg, l_Lean_Meta_Structural_isInstHDivInt___redArg,
    l_Lean_Meta_Structural_isInstHModInt___redArg, l_Lean_Meta_Structural_isInstHMulInt___redArg,
    l_Lean_Meta_Structural_isInstHPowInt___redArg,
};
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_Structural_isInstHAddNat___redArg,
    l_Lean_Meta_Structural_isInstHDivNat___redArg, l_Lean_Meta_Structural_isInstHModNat___redArg,
    l_Lean_Meta_Structural_isInstHMulNat___redArg, l_Lean_Meta_Structural_isInstHPowNat___redArg,
    runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::ToInt::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt, l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_pushNewFact,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_le, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_lt, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::lean_grind_cutsat_assert_le;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [114, 101, 102, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13480818501600609864 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value) as *mut crate::leanh::LeanObject,18356704233129443855 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [70, 105, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [118, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value) as *mut crate::leanh::LeanObject,15815496672699636542 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value) as *mut crate::leanh::LeanObject,7912375598873795493 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value) as *mut crate::leanh::LeanObject,10422657989269798688 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value) as *mut crate::leanh::LeanObject,13744984671752750173 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value) as *mut crate::leanh::LeanObject,9682224670061807480 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value) as *mut crate::leanh::LeanObject,11858238400308895562 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value) as *mut crate::leanh::LeanObject,6100819061652633370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value) as *mut crate::leanh::LeanObject,1611444129324655608 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [84, 111, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 100, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value) as *mut crate::leanh::LeanObject,16002102443310951684 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value) as *mut crate::leanh::LeanObject,4430196350179507746 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 117, 108, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value) as *mut crate::leanh::LeanObject,16002102443310951684 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value) as *mut crate::leanh::LeanObject,15839536216052824054 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 118, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value) as *mut crate::leanh::LeanObject,16002102443310951684 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value) as *mut crate::leanh::LeanObject,4509087223409453090 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 111, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value) as *mut crate::leanh::LeanObject,16002102443310951684 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value) as *mut crate::leanh::LeanObject,12104604908731693656 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [112, 111, 119, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value) as *mut crate::leanh::LeanObject,16002102443310951684 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value) as *mut crate::leanh::LeanObject,320879003380300540 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 97, 116, 67, 97, 115, 116, 95, 111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value) as *mut crate::leanh::LeanObject,16002102443310951684 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value) as *mut crate::leanh::LeanObject,5749108402387788270 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value) as *mut crate::leanh::LeanObject,15815496672699636542 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 105, 110, 86, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value) as *mut crate::leanh::LeanObject,16002102443310951684 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value) as *mut crate::leanh::LeanObject,15401625734282208253 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 115, 76, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value) as *mut crate::leanh::LeanObject,15815496672699636542 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value) as *mut crate::leanh::LeanObject,4938441192065111774 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [78, 97, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 97, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5779414593499529281 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7063772860359172143 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        105, 110, 115, 116, 78, 97, 116, 67, 97, 115, 116, 73, 110, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value)
            as *mut crate::leanh::LeanObject,
        14240220390202531956 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1_value: crate::leanh::LeanStringObject<96> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 96, m_capacity: 96, m_length: 95, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 78, 97, 116, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 109, 107, 78, 111, 110, 110, 101, 103, 84, 104, 109, 63, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [78, 111, 110, 110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,1171494537096084699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value) as *mut crate::leanh::LeanObject,14964074225995313629 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,1171494537096084699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value) as *mut crate::leanh::LeanObject,1512800625229289490 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,1171494537096084699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value) as *mut crate::leanh::LeanObject,4353295038587246268 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,1171494537096084699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value) as *mut crate::leanh::LeanObject,11431446605223061763 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,1171494537096084699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value) as *mut crate::leanh::LeanObject,8763473902706521652 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [112, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,1171494537096084699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value) as *mut crate::leanh::LeanObject,10869537671511025243 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,1171494537096084699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value) as *mut crate::leanh::LeanObject,17115702787724233411 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 111, 80, 111, 108, 121, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,1171494537096084699 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        1027687560957691592 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_1721_: *mut crate::leanh::LeanObject,
    mut v_x_1722_: *mut crate::leanh::LeanObject,
    mut v_x_1723_: *mut crate::leanh::LeanObject,
    mut v_x_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1725_ = crate::leanh::lean_ctor_get(v_x_1721_, 0);
                v_vs_1726_ = crate::leanh::lean_ctor_get(v_x_1721_, 1);
                v_isSharedCheck_1750_ = (!crate::leanh::lean_is_exclusive(v_x_1721_)) as u8;
                if v_isSharedCheck_1750_ == 0 {
                    v___x_1728_ = v_x_1721_;
                    v_isShared_1729_ = v_isSharedCheck_1750_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1726_);
                    crate::leanh::lean_inc(v_ks_1725_);
                    crate::leanh::lean_dec(v_x_1721_);
                    v___x_1728_ = crate::leanh::lean_box(0);
                    v_isShared_1729_ = v_isSharedCheck_1750_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1730_ = lean_array_get_size(v_ks_1725_);
                v___x_1731_ = lean_nat_dec_lt(v_x_1722_, v___x_1730_);
                if v___x_1731_ == 0 {
                    crate::leanh::lean_dec(v_x_1722_);
                    v___x_1732_ = lean_array_push(v_ks_1725_, v_x_1723_);
                    v___x_1733_ = lean_array_push(v_vs_1726_, v_x_1724_);
                    if v_isShared_1729_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1728_, 1, v___x_1733_);
                        crate::leanh::lean_ctor_set(v___x_1728_, 0, v___x_1732_);
                        v___x_1735_ = v___x_1728_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1736_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1732_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1733_);
                        v___x_1735_ = v_reuseFailAlloc_1736_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1737_ = lean_array_fget_borrowed(v_ks_1725_, v_x_1722_);
                    v___x_1738_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1723_,
                            v_k_x27_1737_,
                        );
                    if v___x_1738_ == 0 {
                        if v_isShared_1729_ == 0 {
                            v___x_1740_ = v___x_1728_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1744_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_ks_1725_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_vs_1726_);
                            v___x_1740_ = v_reuseFailAlloc_1744_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1745_ = lean_array_fset(v_ks_1725_, v_x_1722_, v_x_1723_);
                        v___x_1746_ = lean_array_fset(v_vs_1726_, v_x_1722_, v_x_1724_);
                        crate::leanh::lean_dec(v_x_1722_);
                        if v_isShared_1729_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1728_, 1, v___x_1746_);
                            crate::leanh::lean_ctor_set(v___x_1728_, 0, v___x_1745_);
                            v___x_1748_ = v___x_1728_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1749_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1745_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1746_);
                            v___x_1748_ = v_reuseFailAlloc_1749_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1735_;
            }
            3 => {
                v___x_1741_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1742_ = lean_nat_add(v_x_1722_, v___x_1741_);
                crate::leanh::lean_dec(v_x_1722_);
                v_x_1721_ = v___x_1740_;
                v_x_1722_ = v___x_1742_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(
    mut v_n_1751_: *mut crate::leanh::LeanObject,
    mut v_k_1752_: *mut crate::leanh::LeanObject,
    mut v_v_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1755_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1751_, v___x_1754_, v_k_1752_, v_v_1753_);
    return v___x_1755_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_1756_: usize = 0;
    let mut v___x_1757_: usize = 0;
    let mut v___x_1758_: usize = 0;
    v___x_1756_ = 5usize;
    v___x_1757_ = 1usize;
    v___x_1758_ = lean_usize_shift_left(v___x_1757_, v___x_1756_);
    return v___x_1758_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: usize = 0;
    let mut v___x_1761_: usize = 0;
    v___x_1759_ = 1usize;
    v___x_1760_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0);
    v___x_1761_ = lean_usize_sub(v___x_1760_, v___x_1759_);
    return v___x_1761_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1762_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1762_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(
    mut v_x_1763_: *mut crate::leanh::LeanObject,
    mut v_x_1764_: usize,
    mut v_x_1765_: usize,
    mut v_x_1766_: *mut crate::leanh::LeanObject,
    mut v_x_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: usize = 0;
    let mut v___x_1770_: usize = 0;
    let mut v___x_1771_: usize = 0;
    let mut v___x_1772_: usize = 0;
    let mut v_j_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v_v_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut v_node_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1803_: u8 = 0;
    let mut v___x_1804_: usize = 0;
    let mut v___x_1805_: usize = 0;
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1823_: u8 = 0;
    let mut v_ks_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: usize = 0;
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: u8 = 0;
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1763_) == 0 {
                    v_es_1768_ = crate::leanh::lean_ctor_get(v_x_1763_, 0);
                    v___x_1769_ = 5usize;
                    v___x_1770_ = 1usize;
                    v___x_1771_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1);
                    v___x_1772_ = lean_usize_land(v_x_1764_, v___x_1771_);
                    v_j_1773_ = lean_usize_to_nat(v___x_1772_);
                    v___x_1774_ = lean_array_get_size(v_es_1768_);
                    v___x_1775_ = lean_nat_dec_lt(v_j_1773_, v___x_1774_);
                    if v___x_1775_ == 0 {
                        crate::leanh::lean_dec(v_j_1773_);
                        crate::leanh::lean_dec(v_x_1767_);
                        crate::leanh::lean_dec_ref(v_x_1766_);
                        return v_x_1763_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1768_);
                        v_isSharedCheck_1812_ = (!crate::leanh::lean_is_exclusive(v_x_1763_)) as u8;
                        if v_isSharedCheck_1812_ == 0 {
                            v_unused_1813_ = crate::leanh::lean_ctor_get(v_x_1763_, 0);
                            crate::leanh::lean_dec(v_unused_1813_);
                            v___x_1777_ = v_x_1763_;
                            v_isShared_1778_ = v_isSharedCheck_1812_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1763_);
                            v___x_1777_ = crate::leanh::lean_box(0);
                            v_isShared_1778_ = v_isSharedCheck_1812_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1814_ = crate::leanh::lean_ctor_get(v_x_1763_, 0);
                    v_vs_1815_ = crate::leanh::lean_ctor_get(v_x_1763_, 1);
                    v_isSharedCheck_1835_ = (!crate::leanh::lean_is_exclusive(v_x_1763_)) as u8;
                    if v_isSharedCheck_1835_ == 0 {
                        v___x_1817_ = v_x_1763_;
                        v_isShared_1818_ = v_isSharedCheck_1835_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1815_);
                        crate::leanh::lean_inc(v_ks_1814_);
                        crate::leanh::lean_dec(v_x_1763_);
                        v___x_1817_ = crate::leanh::lean_box(0);
                        v_isShared_1818_ = v_isSharedCheck_1835_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1779_ = lean_array_fget(v_es_1768_, v_j_1773_);
                v___x_1780_ = crate::leanh::lean_box(0);
                v_xs_x27_1781_ = lean_array_fset(v_es_1768_, v_j_1773_, v___x_1780_);
                match crate::leanh::lean_obj_tag(v_v_1779_) {
                    0 => {
                        v_key_1788_ = crate::leanh::lean_ctor_get(v_v_1779_, 0);
                        v_val_1789_ = crate::leanh::lean_ctor_get(v_v_1779_, 1);
                        v_isSharedCheck_1799_ = (!crate::leanh::lean_is_exclusive(v_v_1779_)) as u8;
                        if v_isSharedCheck_1799_ == 0 {
                            v___x_1791_ = v_v_1779_;
                            v_isShared_1792_ = v_isSharedCheck_1799_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1789_);
                            crate::leanh::lean_inc(v_key_1788_);
                            crate::leanh::lean_dec(v_v_1779_);
                            v___x_1791_ = crate::leanh::lean_box(0);
                            v_isShared_1792_ = v_isSharedCheck_1799_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1800_ = crate::leanh::lean_ctor_get(v_v_1779_, 0);
                        v_isSharedCheck_1810_ = (!crate::leanh::lean_is_exclusive(v_v_1779_)) as u8;
                        if v_isSharedCheck_1810_ == 0 {
                            v___x_1802_ = v_v_1779_;
                            v_isShared_1803_ = v_isSharedCheck_1810_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1800_);
                            crate::leanh::lean_dec(v_v_1779_);
                            v___x_1802_ = crate::leanh::lean_box(0);
                            v_isShared_1803_ = v_isSharedCheck_1810_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1811_, 0, v_x_1766_);
                        crate::leanh::lean_ctor_set(v___x_1811_, 1, v_x_1767_);
                        v___y_1783_ = v___x_1811_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1784_ = lean_array_fset(v_xs_x27_1781_, v_j_1773_, v___y_1783_);
                crate::leanh::lean_dec(v_j_1773_);
                if v_isShared_1778_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1777_, 0, v___x_1784_);
                    v___x_1786_ = v___x_1777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
                    v___x_1786_ = v_reuseFailAlloc_1787_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1786_;
            }
            4 => {
                v___x_1793_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1766_,
                        v_key_1788_,
                    );
                if v___x_1793_ == 0 {
                    crate::leanh::lean_del_object(v___x_1791_);
                    v___x_1794_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1788_,
                        v_val_1789_,
                        v_x_1766_,
                        v_x_1767_,
                    );
                    v___x_1795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1795_, 0, v___x_1794_);
                    v___y_1783_ = v___x_1795_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1789_);
                    crate::leanh::lean_dec(v_key_1788_);
                    if v_isShared_1792_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1791_, 1, v_x_1767_);
                        crate::leanh::lean_ctor_set(v___x_1791_, 0, v_x_1766_);
                        v___x_1797_ = v___x_1791_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_x_1766_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_x_1767_);
                        v___x_1797_ = v_reuseFailAlloc_1798_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1783_ = v___x_1797_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1804_ = lean_usize_shift_right(v_x_1764_, v___x_1769_);
                v___x_1805_ = lean_usize_add(v_x_1765_, v___x_1770_);
                v___x_1806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_node_1800_, v___x_1804_, v___x_1805_, v_x_1766_, v_x_1767_);
                if v_isShared_1803_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1802_, 0, v___x_1806_);
                    v___x_1808_ = v___x_1802_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
                    v___x_1808_ = v_reuseFailAlloc_1809_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1783_ = v___x_1808_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1818_ == 0 {
                    v___x_1820_ = v___x_1817_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_ks_1814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_vs_1815_);
                    v___x_1820_ = v_reuseFailAlloc_1834_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1821_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v___x_1820_, v_x_1766_, v_x_1767_);
                v___x_1829_ = 7usize;
                v___x_1830_ = lean_usize_dec_le(v___x_1829_, v_x_1765_);
                if v___x_1830_ == 0 {
                    v___x_1831_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1821_);
                    v___x_1832_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1833_ = lean_nat_dec_lt(v___x_1831_, v___x_1832_);
                    crate::leanh::lean_dec(v___x_1831_);
                    v___y_1823_ = v___x_1833_;
                    state = 10;
                    continue;
                } else {
                    v___y_1823_ = v___x_1830_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1823_ == 0 {
                    v_ks_1824_ = crate::leanh::lean_ctor_get(v_newNode_1821_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1824_);
                    v_vs_1825_ = crate::leanh::lean_ctor_get(v_newNode_1821_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1825_);
                    crate::leanh::lean_dec_ref(v_newNode_1821_);
                    v___x_1826_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2);
                    v___x_1828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_x_1765_, v_ks_1824_, v_vs_1825_, v___x_1826_, v___x_1827_);
                    crate::leanh::lean_dec_ref(v_vs_1825_);
                    crate::leanh::lean_dec_ref(v_ks_1824_);
                    return v___x_1828_;
                } else {
                    return v_newNode_1821_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(
    mut v_depth_1836_: usize,
    mut v_keys_1837_: *mut crate::leanh::LeanObject,
    mut v_vals_1838_: *mut crate::leanh::LeanObject,
    mut v_i_1839_: *mut crate::leanh::LeanObject,
    mut v_entries_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: u8 = 0;
    let mut v_k_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u64 = 0;
    let mut v_h_1846_: usize = 0;
    let mut v___x_1847_: usize = 0;
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: usize = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: usize = 0;
    let mut v_h_1852_: usize = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1841_ = lean_array_get_size(v_keys_1837_);
                v___x_1842_ = lean_nat_dec_lt(v_i_1839_, v___x_1841_);
                if v___x_1842_ == 0 {
                    crate::leanh::lean_dec(v_i_1839_);
                    return v_entries_1840_;
                } else {
                    v_k_1843_ = lean_array_fget_borrowed(v_keys_1837_, v_i_1839_);
                    v_v_1844_ = lean_array_fget_borrowed(v_vals_1838_, v_i_1839_);
                    v___x_1845_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1843_);
                    v_h_1846_ = lean_uint64_to_usize(v___x_1845_);
                    v___x_1847_ = 5usize;
                    v___x_1848_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1849_ = 1usize;
                    v___x_1850_ = lean_usize_sub(v_depth_1836_, v___x_1849_);
                    v___x_1851_ = lean_usize_mul(v___x_1847_, v___x_1850_);
                    v_h_1852_ = lean_usize_shift_right(v_h_1846_, v___x_1851_);
                    v___x_1853_ = lean_nat_add(v_i_1839_, v___x_1848_);
                    crate::leanh::lean_dec(v_i_1839_);
                    crate::leanh::lean_inc(v_v_1844_);
                    crate::leanh::lean_inc(v_k_1843_);
                    v___x_1854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_entries_1840_, v_h_1852_, v_depth_1836_, v_k_1843_, v_v_1844_);
                    v_i_1839_ = v___x_1853_;
                    v_entries_1840_ = v___x_1854_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_1856_: *mut crate::leanh::LeanObject,
    mut v_keys_1857_: *mut crate::leanh::LeanObject,
    mut v_vals_1858_: *mut crate::leanh::LeanObject,
    mut v_i_1859_: *mut crate::leanh::LeanObject,
    mut v_entries_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1861_: usize = 0;
    let mut v_res_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1861_ = crate::leanh::lean_unbox_usize(v_depth_1856_);
    crate::leanh::lean_dec(v_depth_1856_);
    v_res_1862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1861_, v_keys_1857_, v_vals_1858_, v_i_1859_, v_entries_1860_);
    crate::leanh::lean_dec_ref(v_vals_1858_);
    crate::leanh::lean_dec_ref(v_keys_1857_);
    return v_res_1862_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___boxed(
    mut v_x_1863_: *mut crate::leanh::LeanObject,
    mut v_x_1864_: *mut crate::leanh::LeanObject,
    mut v_x_1865_: *mut crate::leanh::LeanObject,
    mut v_x_1866_: *mut crate::leanh::LeanObject,
    mut v_x_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5935__boxed_1868_: usize = 0;
    let mut v_x_5936__boxed_1869_: usize = 0;
    let mut v_res_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5935__boxed_1868_ = crate::leanh::lean_unbox_usize(v_x_1864_);
    crate::leanh::lean_dec(v_x_1864_);
    v_x_5936__boxed_1869_ = crate::leanh::lean_unbox_usize(v_x_1865_);
    crate::leanh::lean_dec(v_x_1865_);
    v_res_1870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_1863_, v_x_5935__boxed_1868_, v_x_5936__boxed_1869_, v_x_1866_, v_x_1867_);
    return v_res_1870_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(
    mut v_x_1871_: *mut crate::leanh::LeanObject,
    mut v_x_1872_: *mut crate::leanh::LeanObject,
    mut v_x_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: u64 = 0;
    let mut v___x_1875_: usize = 0;
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1872_);
    v___x_1875_ = lean_uint64_to_usize(v___x_1874_);
    v___x_1876_ = 1usize;
    v___x_1877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_1871_, v___x_1875_, v___x_1876_, v_x_1872_, v_x_1873_);
    return v___x_1877_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0(
    mut v_e_1878_: *mut crate::leanh::LeanObject,
    mut v___x_1879_: *mut crate::leanh::LeanObject,
    mut v_s_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_1896_: u8 = 0;
    let mut v_conflict_x3f_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_1904_: u8 = 0;
    let mut v_nonlinearOccs_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_1881_ = crate::leanh::lean_ctor_get(v_s_1880_, 0);
                v_varMap_1882_ = crate::leanh::lean_ctor_get(v_s_1880_, 1);
                v_vars_x27_1883_ = crate::leanh::lean_ctor_get(v_s_1880_, 2);
                v_varMap_x27_1884_ = crate::leanh::lean_ctor_get(v_s_1880_, 3);
                v_natToIntMap_1885_ = crate::leanh::lean_ctor_get(v_s_1880_, 4);
                v_natDef_1886_ = crate::leanh::lean_ctor_get(v_s_1880_, 5);
                v_dvds_1887_ = crate::leanh::lean_ctor_get(v_s_1880_, 6);
                v_lowers_1888_ = crate::leanh::lean_ctor_get(v_s_1880_, 7);
                v_uppers_1889_ = crate::leanh::lean_ctor_get(v_s_1880_, 8);
                v_diseqs_1890_ = crate::leanh::lean_ctor_get(v_s_1880_, 9);
                v_elimEqs_1891_ = crate::leanh::lean_ctor_get(v_s_1880_, 10);
                v_elimStack_1892_ = crate::leanh::lean_ctor_get(v_s_1880_, 11);
                v_occurs_1893_ = crate::leanh::lean_ctor_get(v_s_1880_, 12);
                v_assignment_1894_ = crate::leanh::lean_ctor_get(v_s_1880_, 13);
                v_nextCnstrId_1895_ = crate::leanh::lean_ctor_get(v_s_1880_, 14);
                v_caseSplits_1896_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1880_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_1897_ = crate::leanh::lean_ctor_get(v_s_1880_, 15);
                v_diseqSplits_1898_ = crate::leanh::lean_ctor_get(v_s_1880_, 16);
                v_divMod_1899_ = crate::leanh::lean_ctor_get(v_s_1880_, 17);
                v_toIntIds_1900_ = crate::leanh::lean_ctor_get(v_s_1880_, 18);
                v_toIntInfos_1901_ = crate::leanh::lean_ctor_get(v_s_1880_, 19);
                v_toIntTermMap_1902_ = crate::leanh::lean_ctor_get(v_s_1880_, 20);
                v_toIntVarMap_1903_ = crate::leanh::lean_ctor_get(v_s_1880_, 21);
                v_usedCommRing_1904_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1880_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_1905_ = crate::leanh::lean_ctor_get(v_s_1880_, 22);
                v_isSharedCheck_1913_ = (!crate::leanh::lean_is_exclusive(v_s_1880_)) as u8;
                if v_isSharedCheck_1913_ == 0 {
                    v___x_1907_ = v_s_1880_;
                    v_isShared_1908_ = v_isSharedCheck_1913_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nonlinearOccs_1905_);
                    crate::leanh::lean_inc(v_toIntVarMap_1903_);
                    crate::leanh::lean_inc(v_toIntTermMap_1902_);
                    crate::leanh::lean_inc(v_toIntInfos_1901_);
                    crate::leanh::lean_inc(v_toIntIds_1900_);
                    crate::leanh::lean_inc(v_divMod_1899_);
                    crate::leanh::lean_inc(v_diseqSplits_1898_);
                    crate::leanh::lean_inc(v_conflict_x3f_1897_);
                    crate::leanh::lean_inc(v_nextCnstrId_1895_);
                    crate::leanh::lean_inc(v_assignment_1894_);
                    crate::leanh::lean_inc(v_occurs_1893_);
                    crate::leanh::lean_inc(v_elimStack_1892_);
                    crate::leanh::lean_inc(v_elimEqs_1891_);
                    crate::leanh::lean_inc(v_diseqs_1890_);
                    crate::leanh::lean_inc(v_uppers_1889_);
                    crate::leanh::lean_inc(v_lowers_1888_);
                    crate::leanh::lean_inc(v_dvds_1887_);
                    crate::leanh::lean_inc(v_natDef_1886_);
                    crate::leanh::lean_inc(v_natToIntMap_1885_);
                    crate::leanh::lean_inc(v_varMap_x27_1884_);
                    crate::leanh::lean_inc(v_vars_x27_1883_);
                    crate::leanh::lean_inc(v_varMap_1882_);
                    crate::leanh::lean_inc(v_vars_1881_);
                    crate::leanh::lean_dec(v_s_1880_);
                    v___x_1907_ = crate::leanh::lean_box(0);
                    v_isShared_1908_ = v_isSharedCheck_1913_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1909_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_natToIntMap_1885_, v_e_1878_, v___x_1879_);
                if v_isShared_1908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1907_, 4, v___x_1909_);
                    v___x_1911_ = v___x_1907_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1912_ = crate::leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_vars_1881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_varMap_1882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_vars_x27_1883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_varMap_x27_1884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 4, v___x_1909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 5, v_natDef_1886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 6, v_dvds_1887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 7, v_lowers_1888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 8, v_uppers_1889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 9, v_diseqs_1890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 10, v_elimEqs_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 11, v_elimStack_1892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 12, v_occurs_1893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 13, v_assignment_1894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 14, v_nextCnstrId_1895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 15, v_conflict_x3f_1897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 16, v_diseqSplits_1898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 17, v_divMod_1899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 18, v_toIntIds_1900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 19, v_toIntInfos_1901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 20, v_toIntTermMap_1902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 21, v_toIntVarMap_1903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 22, v_nonlinearOccs_1905_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1912_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_1896_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1912_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_1904_,
                    );
                    v___x_1911_ = v_reuseFailAlloc_1912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1914_: *mut crate::leanh::LeanObject,
    mut v_vals_1915_: *mut crate::leanh::LeanObject,
    mut v_i_1916_: *mut crate::leanh::LeanObject,
    mut v_k_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: u8 = 0;
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1918_ = lean_array_get_size(v_keys_1914_);
                v___x_1919_ = lean_nat_dec_lt(v_i_1916_, v___x_1918_);
                if v___x_1919_ == 0 {
                    crate::leanh::lean_dec(v_i_1916_);
                    v___x_1920_ = crate::leanh::lean_box(0);
                    return v___x_1920_;
                } else {
                    v_k_x27_1921_ = lean_array_fget_borrowed(v_keys_1914_, v_i_1916_);
                    v___x_1922_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1917_,
                            v_k_x27_1921_,
                        );
                    if v___x_1922_ == 0 {
                        v___x_1923_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1924_ = lean_nat_add(v_i_1916_, v___x_1923_);
                        crate::leanh::lean_dec(v_i_1916_);
                        v_i_1916_ = v___x_1924_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1926_ = lean_array_fget_borrowed(v_vals_1915_, v_i_1916_);
                        crate::leanh::lean_dec(v_i_1916_);
                        crate::leanh::lean_inc(v___x_1926_);
                        v___x_1927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1927_, 0, v___x_1926_);
                        return v___x_1927_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1928_: *mut crate::leanh::LeanObject,
    mut v_vals_1929_: *mut crate::leanh::LeanObject,
    mut v_i_1930_: *mut crate::leanh::LeanObject,
    mut v_k_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1932_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_1928_, v_vals_1929_, v_i_1930_, v_k_1931_);
    crate::leanh::lean_dec_ref(v_k_1931_);
    crate::leanh::lean_dec_ref(v_vals_1929_);
    crate::leanh::lean_dec_ref(v_keys_1928_);
    return v_res_1932_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(
    mut v_x_1933_: *mut crate::leanh::LeanObject,
    mut v_x_1934_: usize,
    mut v_x_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: usize = 0;
    let mut v___x_1940_: usize = 0;
    let mut v_j_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: usize = 0;
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1933_) == 0 {
                    v_es_1936_ = crate::leanh::lean_ctor_get(v_x_1933_, 0);
                    v___x_1937_ = crate::leanh::lean_box(2);
                    v___x_1938_ = 5usize;
                    v___x_1939_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1);
                    v___x_1940_ = lean_usize_land(v_x_1934_, v___x_1939_);
                    v_j_1941_ = lean_usize_to_nat(v___x_1940_);
                    v___x_1942_ = lean_array_get_borrowed(v___x_1937_, v_es_1936_, v_j_1941_);
                    crate::leanh::lean_dec(v_j_1941_);
                    match crate::leanh::lean_obj_tag(v___x_1942_) {
                        0 => {
                            v_key_1943_ = crate::leanh::lean_ctor_get(v___x_1942_, 0);
                            v_val_1944_ = crate::leanh::lean_ctor_get(v___x_1942_, 1);
                            v___x_1945_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1935_, v_key_1943_);
                            if v___x_1945_ == 0 {
                                v___x_1946_ = crate::leanh::lean_box(0);
                                return v___x_1946_;
                            } else {
                                crate::leanh::lean_inc(v_val_1944_);
                                v___x_1947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1947_, 0, v_val_1944_);
                                return v___x_1947_;
                            }
                        }
                        1 => {
                            v_node_1948_ = crate::leanh::lean_ctor_get(v___x_1942_, 0);
                            v___x_1949_ = lean_usize_shift_right(v_x_1934_, v___x_1938_);
                            v_x_1933_ = v_node_1948_;
                            v_x_1934_ = v___x_1949_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1951_ = crate::leanh::lean_box(0);
                            return v___x_1951_;
                        }
                    }
                } else {
                    v_ks_1952_ = crate::leanh::lean_ctor_get(v_x_1933_, 0);
                    v_vs_1953_ = crate::leanh::lean_ctor_get(v_x_1933_, 1);
                    v___x_1954_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1955_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_ks_1952_, v_vs_1953_, v___x_1954_, v_x_1935_);
                    return v___x_1955_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg___boxed(
    mut v_x_1956_: *mut crate::leanh::LeanObject,
    mut v_x_1957_: *mut crate::leanh::LeanObject,
    mut v_x_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6153__boxed_1959_: usize = 0;
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6153__boxed_1959_ = crate::leanh::lean_unbox_usize(v_x_1957_);
    crate::leanh::lean_dec(v_x_1957_);
    v_res_1960_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_1956_, v_x_6153__boxed_1959_, v_x_1958_);
    crate::leanh::lean_dec_ref(v_x_1958_);
    crate::leanh::lean_dec_ref(v_x_1956_);
    return v_res_1960_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(
    mut v_x_1961_: *mut crate::leanh::LeanObject,
    mut v_x_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1963_: u64 = 0;
    let mut v___x_1964_: usize = 0;
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1963_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1962_);
    v___x_1964_ = lean_uint64_to_usize(v___x_1963_);
    v___x_1965_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_1961_, v___x_1964_, v_x_1962_);
    return v___x_1965_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg___boxed(
    mut v_x_1966_: *mut crate::leanh::LeanObject,
    mut v_x_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1968_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_1966_, v_x_1967_);
    crate::leanh::lean_dec_ref(v_x_1967_);
    crate::leanh::lean_dec_ref(v_x_1966_);
    return v_res_1968_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1974_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1975_ = l_Lean_Level_ofNat(v___x_1974_);
    return v___x_1975_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1976_ = crate::leanh::lean_box(0);
    v___x_1977_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3,
    );
    v___x_1978_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1978_, 0, v___x_1977_);
    crate::leanh::lean_ctor_set(v___x_1978_, 1, v___x_1976_);
    return v___x_1978_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1979_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4,
    );
    v___x_1980_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2;
    v___x_1981_ = l_Lean_mkConst(v___x_1980_, v___x_1979_);
    return v___x_1981_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = l_Lean_Int_mkType;
    v___x_1983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5,
    );
    v___x_1984_ = l_Lean_Expr_app___override(v___x_1983_, v___x_1982_);
    return v___x_1984_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
    mut v_e_1985_: *mut crate::leanh::LeanObject,
    mut v_a_1986_: *mut crate::leanh::LeanObject,
    mut v_a_1987_: *mut crate::leanh::LeanObject,
    mut v_a_1988_: *mut crate::leanh::LeanObject,
    mut v_a_1989_: *mut crate::leanh::LeanObject,
    mut v_a_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: *mut crate::leanh::LeanObject,
    mut v_a_1994_: *mut crate::leanh::LeanObject,
    mut v_a_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v_natToIntMap_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_unused_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut v_a_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut v_a_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2045_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1997_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1986_, v_a_1994_);
                if crate::leanh::lean_obj_tag(v___x_1997_) == 0 {
                    v_a_1998_ = crate::leanh::lean_ctor_get(v___x_1997_, 0);
                    v_isSharedCheck_2050_ = (!crate::leanh::lean_is_exclusive(v___x_1997_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2000_ = v___x_1997_;
                        v_isShared_2001_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1998_);
                        crate::leanh::lean_dec(v___x_1997_);
                        v___x_2000_ = crate::leanh::lean_box(0);
                        v_isShared_2001_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1985_);
                    v_a_2051_ = crate::leanh::lean_ctor_get(v___x_1997_, 0);
                    v_isSharedCheck_2058_ = (!crate::leanh::lean_is_exclusive(v___x_1997_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_1997_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2051_);
                        crate::leanh::lean_dec(v___x_1997_);
                        v___x_2053_ = crate::leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_natToIntMap_2002_ = crate::leanh::lean_ctor_get(v_a_1998_, 4);
                crate::leanh::lean_inc_ref(v_natToIntMap_2002_);
                crate::leanh::lean_dec(v_a_1998_);
                v___x_2003_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_natToIntMap_2002_, v_e_1985_);
                crate::leanh::lean_dec_ref(v_natToIntMap_2002_);
                if crate::leanh::lean_obj_tag(v___x_2003_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_1985_);
                    v_val_2004_ = crate::leanh::lean_ctor_get(v___x_2003_, 0);
                    crate::leanh::lean_inc(v_val_2004_);
                    crate::leanh::lean_dec_ref_known(v___x_2003_, 1);
                    if v_isShared_2001_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2000_, 0, v_val_2004_);
                        v___x_2006_ = v___x_2000_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_val_2004_);
                        v___x_2006_ = v_reuseFailAlloc_2007_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2003_);
                    crate::leanh::lean_del_object(v___x_2000_);
                    crate::leanh::lean_inc_ref(v_e_1985_);
                    v___x_2008_ = l_Lean_mkIntNatCast(v_e_1985_);
                    v___x_2009_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_2008_, v_a_1991_);
                    if crate::leanh::lean_obj_tag(v___x_2009_) == 0 {
                        v_a_2010_ = crate::leanh::lean_ctor_get(v___x_2009_, 0);
                        crate::leanh::lean_inc_n(v_a_2010_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2009_, 1);
                        v___x_2011_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6,
                        );
                        v___x_2012_ = l_Lean_Expr_app___override(v___x_2011_, v_a_2010_);
                        v___x_2013_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2013_, 0, v_a_2010_);
                        crate::leanh::lean_ctor_set(v___x_2013_, 1, v___x_2012_);
                        crate::leanh::lean_inc_ref(v___x_2013_);
                        crate::leanh::lean_inc_ref(v_e_1985_);
                        v___f_2014_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_2014_, 0, v_e_1985_);
                        crate::leanh::lean_closure_set(v___f_2014_, 1, v___x_2013_);
                        v___x_2015_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                        v___x_2016_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2015_, v___f_2014_, v_a_1986_);
                        if crate::leanh::lean_obj_tag(v___x_2016_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2016_, 1);
                            v___x_2017_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                                v___x_2015_,
                                v_e_1985_,
                                v_a_1986_,
                                v_a_1987_,
                                v_a_1988_,
                                v_a_1989_,
                                v_a_1990_,
                                v_a_1991_,
                                v_a_1992_,
                                v_a_1993_,
                                v_a_1994_,
                                v_a_1995_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2017_) == 0 {
                                v_isSharedCheck_2024_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2017_)) as u8;
                                if v_isSharedCheck_2024_ == 0 {
                                    v_unused_2025_ = crate::leanh::lean_ctor_get(v___x_2017_, 0);
                                    crate::leanh::lean_dec(v_unused_2025_);
                                    v___x_2019_ = v___x_2017_;
                                    v_isShared_2020_ = v_isSharedCheck_2024_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2017_);
                                    v___x_2019_ = crate::leanh::lean_box(0);
                                    v_isShared_2020_ = v_isSharedCheck_2024_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2013_, 2);
                                v_a_2026_ = crate::leanh::lean_ctor_get(v___x_2017_, 0);
                                v_isSharedCheck_2033_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2017_)) as u8;
                                if v_isSharedCheck_2033_ == 0 {
                                    v___x_2028_ = v___x_2017_;
                                    v_isShared_2029_ = v_isSharedCheck_2033_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2026_);
                                    crate::leanh::lean_dec(v___x_2017_);
                                    v___x_2028_ = crate::leanh::lean_box(0);
                                    v_isShared_2029_ = v_isSharedCheck_2033_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2013_, 2);
                            crate::leanh::lean_dec_ref(v_e_1985_);
                            v_a_2034_ = crate::leanh::lean_ctor_get(v___x_2016_, 0);
                            v_isSharedCheck_2041_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2016_)) as u8;
                            if v_isSharedCheck_2041_ == 0 {
                                v___x_2036_ = v___x_2016_;
                                v_isShared_2037_ = v_isSharedCheck_2041_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2034_);
                                crate::leanh::lean_dec(v___x_2016_);
                                v___x_2036_ = crate::leanh::lean_box(0);
                                v_isShared_2037_ = v_isSharedCheck_2041_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1985_);
                        v_a_2042_ = crate::leanh::lean_ctor_get(v___x_2009_, 0);
                        v_isSharedCheck_2049_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2009_)) as u8;
                        if v_isSharedCheck_2049_ == 0 {
                            v___x_2044_ = v___x_2009_;
                            v_isShared_2045_ = v_isSharedCheck_2049_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2042_);
                            crate::leanh::lean_dec(v___x_2009_);
                            v___x_2044_ = crate::leanh::lean_box(0);
                            v_isShared_2045_ = v_isSharedCheck_2049_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2006_;
            }
            3 => {
                if v_isShared_2020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2019_, 0, v___x_2013_);
                    v___x_2022_ = v___x_2019_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2013_);
                    v___x_2022_ = v_reuseFailAlloc_2023_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2022_;
            }
            5 => {
                if v_isShared_2029_ == 0 {
                    v___x_2031_ = v___x_2028_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2032_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
                    v___x_2031_ = v_reuseFailAlloc_2032_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2031_;
            }
            7 => {
                if v_isShared_2037_ == 0 {
                    v___x_2039_ = v___x_2036_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
                    v___x_2039_ = v_reuseFailAlloc_2040_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2039_;
            }
            9 => {
                if v_isShared_2045_ == 0 {
                    v___x_2047_ = v___x_2044_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
                    v___x_2047_ = v_reuseFailAlloc_2048_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2047_;
            }
            11 => {
                if v_isShared_2054_ == 0 {
                    v___x_2056_ = v___x_2053_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___boxed(
    mut v_e_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
    mut v_a_2066_: *mut crate::leanh::LeanObject,
    mut v_a_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
    mut v_a_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2071_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
        v_e_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_,
        v_a_2067_, v_a_2068_, v_a_2069_,
    );
    crate::leanh::lean_dec(v_a_2069_);
    crate::leanh::lean_dec_ref(v_a_2068_);
    crate::leanh::lean_dec(v_a_2067_);
    crate::leanh::lean_dec_ref(v_a_2066_);
    crate::leanh::lean_dec(v_a_2065_);
    crate::leanh::lean_dec_ref(v_a_2064_);
    crate::leanh::lean_dec(v_a_2063_);
    crate::leanh::lean_dec_ref(v_a_2062_);
    crate::leanh::lean_dec(v_a_2061_);
    crate::leanh::lean_dec(v_a_2060_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(
    mut v_00_u03b2_2072_: *mut crate::leanh::LeanObject,
    mut v_x_2073_: *mut crate::leanh::LeanObject,
    mut v_x_2074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_2073_, v_x_2074_);
    return v___x_2075_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___boxed(
    mut v_00_u03b2_2076_: *mut crate::leanh::LeanObject,
    mut v_x_2077_: *mut crate::leanh::LeanObject,
    mut v_x_2078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2079_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(
            v_00_u03b2_2076_,
            v_x_2077_,
            v_x_2078_,
        );
    crate::leanh::lean_dec_ref(v_x_2078_);
    crate::leanh::lean_dec_ref(v_x_2077_);
    return v_res_2079_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1(
    mut v_00_u03b2_2080_: *mut crate::leanh::LeanObject,
    mut v_x_2081_: *mut crate::leanh::LeanObject,
    mut v_x_2082_: *mut crate::leanh::LeanObject,
    mut v_x_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_x_2081_, v_x_2082_, v_x_2083_);
    return v___x_2084_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(
    mut v_00_u03b2_2085_: *mut crate::leanh::LeanObject,
    mut v_x_2086_: *mut crate::leanh::LeanObject,
    mut v_x_2087_: usize,
    mut v_x_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_2086_, v_x_2087_, v_x_2088_);
    return v___x_2089_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_2090_: *mut crate::leanh::LeanObject,
    mut v_x_2091_: *mut crate::leanh::LeanObject,
    mut v_x_2092_: *mut crate::leanh::LeanObject,
    mut v_x_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6405__boxed_2094_: usize = 0;
    let mut v_res_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6405__boxed_2094_ = crate::leanh::lean_unbox_usize(v_x_2092_);
    crate::leanh::lean_dec(v_x_2092_);
    v_res_2095_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(v_00_u03b2_2090_, v_x_2091_, v_x_6405__boxed_2094_, v_x_2093_);
    crate::leanh::lean_dec_ref(v_x_2093_);
    crate::leanh::lean_dec_ref(v_x_2091_);
    return v_res_2095_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(
    mut v_00_u03b2_2096_: *mut crate::leanh::LeanObject,
    mut v_x_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: usize,
    mut v_x_2099_: usize,
    mut v_x_2100_: *mut crate::leanh::LeanObject,
    mut v_x_2101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_2097_, v_x_2098_, v_x_2099_, v_x_2100_, v_x_2101_);
    return v___x_2102_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___boxed(
    mut v_00_u03b2_2103_: *mut crate::leanh::LeanObject,
    mut v_x_2104_: *mut crate::leanh::LeanObject,
    mut v_x_2105_: *mut crate::leanh::LeanObject,
    mut v_x_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
    mut v_x_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6416__boxed_2109_: usize = 0;
    let mut v_x_6417__boxed_2110_: usize = 0;
    let mut v_res_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6416__boxed_2109_ = crate::leanh::lean_unbox_usize(v_x_2105_);
    crate::leanh::lean_dec(v_x_2105_);
    v_x_6417__boxed_2110_ = crate::leanh::lean_unbox_usize(v_x_2106_);
    crate::leanh::lean_dec(v_x_2106_);
    v_res_2111_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(v_00_u03b2_2103_, v_x_2104_, v_x_6416__boxed_2109_, v_x_6417__boxed_2110_, v_x_2107_, v_x_2108_);
    return v_res_2111_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2112_: *mut crate::leanh::LeanObject,
    mut v_keys_2113_: *mut crate::leanh::LeanObject,
    mut v_vals_2114_: *mut crate::leanh::LeanObject,
    mut v_heq_2115_: *mut crate::leanh::LeanObject,
    mut v_i_2116_: *mut crate::leanh::LeanObject,
    mut v_k_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_2113_, v_vals_2114_, v_i_2116_, v_k_2117_);
    return v___x_2118_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2119_: *mut crate::leanh::LeanObject,
    mut v_keys_2120_: *mut crate::leanh::LeanObject,
    mut v_vals_2121_: *mut crate::leanh::LeanObject,
    mut v_heq_2122_: *mut crate::leanh::LeanObject,
    mut v_i_2123_: *mut crate::leanh::LeanObject,
    mut v_k_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2125_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(v_00_u03b2_2119_, v_keys_2120_, v_vals_2121_, v_heq_2122_, v_i_2123_, v_k_2124_);
    crate::leanh::lean_dec_ref(v_k_2124_);
    crate::leanh::lean_dec_ref(v_vals_2121_);
    crate::leanh::lean_dec_ref(v_keys_2120_);
    return v_res_2125_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2126_: *mut crate::leanh::LeanObject,
    mut v_n_2127_: *mut crate::leanh::LeanObject,
    mut v_k_2128_: *mut crate::leanh::LeanObject,
    mut v_v_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v_n_2127_, v_k_2128_, v_v_2129_);
    return v___x_2130_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2131_: *mut crate::leanh::LeanObject,
    mut v_depth_2132_: usize,
    mut v_keys_2133_: *mut crate::leanh::LeanObject,
    mut v_vals_2134_: *mut crate::leanh::LeanObject,
    mut v_heq_2135_: *mut crate::leanh::LeanObject,
    mut v_i_2136_: *mut crate::leanh::LeanObject,
    mut v_entries_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2138_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_2132_, v_keys_2133_, v_vals_2134_, v_i_2136_, v_entries_2137_);
    return v___x_2138_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2139_: *mut crate::leanh::LeanObject,
    mut v_depth_2140_: *mut crate::leanh::LeanObject,
    mut v_keys_2141_: *mut crate::leanh::LeanObject,
    mut v_vals_2142_: *mut crate::leanh::LeanObject,
    mut v_heq_2143_: *mut crate::leanh::LeanObject,
    mut v_i_2144_: *mut crate::leanh::LeanObject,
    mut v_entries_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2146_: usize = 0;
    let mut v_res_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2146_ = crate::leanh::lean_unbox_usize(v_depth_2140_);
    crate::leanh::lean_dec(v_depth_2140_);
    v_res_2147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(v_00_u03b2_2139_, v_depth_boxed_2146_, v_keys_2141_, v_vals_2142_, v_heq_2143_, v_i_2144_, v_entries_2145_);
    crate::leanh::lean_dec_ref(v_vals_2142_);
    crate::leanh::lean_dec_ref(v_keys_2141_);
    return v_res_2147_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2148_: *mut crate::leanh::LeanObject,
    mut v_x_2149_: *mut crate::leanh::LeanObject,
    mut v_x_2150_: *mut crate::leanh::LeanObject,
    mut v_x_2151_: *mut crate::leanh::LeanObject,
    mut v_x_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2149_, v_x_2150_, v_x_2151_, v_x_2152_);
    return v___x_2153_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2157_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4,
    );
    v___x_2158_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1;
    v___x_2159_ = l_Lean_mkConst(v___x_2158_, v___x_2157_);
    return v___x_2159_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2160_ = l_Lean_Int_mkType;
    v___x_2161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2);
    v___x_2162_ = l_Lean_Expr_app___override(v___x_2161_, v___x_2160_);
    return v___x_2162_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2163_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3);
    return v___x_2163_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__0(
    mut v_a_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = lean_nat_to_int(v_a_2164_);
    return v___x_2165_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(
    mut v_keys_2166_: *mut crate::leanh::LeanObject,
    mut v_i_2167_: *mut crate::leanh::LeanObject,
    mut v_k_2168_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: u8 = 0;
    let mut v_k_x27_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: u8 = 0;
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2169_ = lean_array_get_size(v_keys_2166_);
                v___x_2170_ = lean_nat_dec_lt(v_i_2167_, v___x_2169_);
                if v___x_2170_ == 0 {
                    crate::leanh::lean_dec(v_i_2167_);
                    return v___x_2170_;
                } else {
                    v_k_x27_2171_ = lean_array_fget_borrowed(v_keys_2166_, v_i_2167_);
                    v___x_2172_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2168_,
                            v_k_x27_2171_,
                        );
                    if v___x_2172_ == 0 {
                        v___x_2173_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2174_ = lean_nat_add(v_i_2167_, v___x_2173_);
                        crate::leanh::lean_dec(v_i_2167_);
                        v_i_2167_ = v___x_2174_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_2167_);
                        return v___x_2172_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_keys_2176_: *mut crate::leanh::LeanObject,
    mut v_i_2177_: *mut crate::leanh::LeanObject,
    mut v_k_2178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2179_: u8 = 0;
    let mut v_r_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2179_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_keys_2176_, v_i_2177_, v_k_2178_);
    crate::leanh::lean_dec_ref(v_k_2178_);
    crate::leanh::lean_dec_ref(v_keys_2176_);
    v_r_2180_ = crate::leanh::lean_box((v_res_2179_) as usize);
    return v_r_2180_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(
    mut v_x_2181_: *mut crate::leanh::LeanObject,
    mut v_x_2182_: usize,
    mut v_x_2183_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: usize = 0;
    let mut v___x_2187_: usize = 0;
    let mut v___x_2188_: usize = 0;
    let mut v_j_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: u8 = 0;
    let mut v_node_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: usize = 0;
    let mut v___x_2196_: u8 = 0;
    let mut v_ks_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2181_) == 0 {
                    v_es_2184_ = crate::leanh::lean_ctor_get(v_x_2181_, 0);
                    v___x_2185_ = crate::leanh::lean_box(2);
                    v___x_2186_ = 5usize;
                    v___x_2187_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1);
                    v___x_2188_ = lean_usize_land(v_x_2182_, v___x_2187_);
                    v_j_2189_ = lean_usize_to_nat(v___x_2188_);
                    v___x_2190_ = lean_array_get_borrowed(v___x_2185_, v_es_2184_, v_j_2189_);
                    crate::leanh::lean_dec(v_j_2189_);
                    match crate::leanh::lean_obj_tag(v___x_2190_) {
                        0 => {
                            v_key_2191_ = crate::leanh::lean_ctor_get(v___x_2190_, 0);
                            v___x_2192_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2183_, v_key_2191_);
                            return v___x_2192_;
                        }
                        1 => {
                            v_node_2193_ = crate::leanh::lean_ctor_get(v___x_2190_, 0);
                            v___x_2194_ = lean_usize_shift_right(v_x_2182_, v___x_2186_);
                            v_x_2181_ = v_node_2193_;
                            v_x_2182_ = v___x_2194_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2196_ = 0;
                            return v___x_2196_;
                        }
                    }
                } else {
                    v_ks_2197_ = crate::leanh::lean_ctor_get(v_x_2181_, 0);
                    v___x_2198_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2199_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_ks_2197_, v___x_2198_, v_x_2183_);
                    return v___x_2199_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg___boxed(
    mut v_x_2200_: *mut crate::leanh::LeanObject,
    mut v_x_2201_: *mut crate::leanh::LeanObject,
    mut v_x_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_61909__boxed_2203_: usize = 0;
    let mut v_res_2204_: u8 = 0;
    let mut v_r_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_61909__boxed_2203_ = crate::leanh::lean_unbox_usize(v_x_2201_);
    crate::leanh::lean_dec(v_x_2201_);
    v_res_2204_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_2200_, v_x_61909__boxed_2203_, v_x_2202_);
    crate::leanh::lean_dec_ref(v_x_2202_);
    crate::leanh::lean_dec_ref(v_x_2200_);
    v_r_2205_ = crate::leanh::lean_box((v_res_2204_) as usize);
    return v_r_2205_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(
    mut v_x_2206_: *mut crate::leanh::LeanObject,
    mut v_x_2207_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2208_: u64 = 0;
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: u8 = 0;
    v___x_2208_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2207_);
    v___x_2209_ = lean_uint64_to_usize(v___x_2208_);
    v___x_2210_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_2206_, v___x_2209_, v_x_2207_);
    return v___x_2210_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg___boxed(
    mut v_x_2211_: *mut crate::leanh::LeanObject,
    mut v_x_2212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2213_: u8 = 0;
    let mut v_r_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_x_2211_, v_x_2212_);
    crate::leanh::lean_dec_ref(v_x_2212_);
    crate::leanh::lean_dec_ref(v_x_2211_);
    v_r_2214_ = crate::leanh::lean_box((v_res_2213_) as usize);
    return v_r_2214_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2257_ = crate::leanh::lean_box(0);
    v___x_2258_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24;
    v___x_2259_ = l_Lean_mkConst(v___x_2258_, v___x_2257_);
    return v___x_2259_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2265_ = crate::leanh::lean_box(0);
    v___x_2266_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27;
    v___x_2267_ = l_Lean_mkConst(v___x_2266_, v___x_2265_);
    return v___x_2267_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = crate::leanh::lean_box(0);
    v___x_2274_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30;
    v___x_2275_ = l_Lean_mkConst(v___x_2274_, v___x_2273_);
    return v___x_2275_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2281_ = crate::leanh::lean_box(0);
    v___x_2282_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33;
    v___x_2283_ = l_Lean_mkConst(v___x_2282_, v___x_2281_);
    return v___x_2283_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2289_ = crate::leanh::lean_box(0);
    v___x_2290_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36;
    v___x_2291_ = l_Lean_mkConst(v___x_2290_, v___x_2289_);
    return v___x_2291_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2297_ = crate::leanh::lean_box(0);
    v___x_2298_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39;
    v___x_2299_ = l_Lean_mkConst(v___x_2298_, v___x_2297_);
    return v___x_2299_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = crate::leanh::lean_box(0);
    v___x_2303_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41;
    v___x_2304_ = l_Lean_mkConst(v___x_2303_, v___x_2302_);
    return v___x_2304_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = crate::leanh::lean_box(0);
    v___x_2311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44;
    v___x_2312_ = l_Lean_mkConst(v___x_2311_, v___x_2310_);
    return v___x_2312_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2317_ = crate::leanh::lean_box(0);
    v___x_2318_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47;
    v___x_2319_ = l_Lean_mkConst(v___x_2318_, v___x_2317_);
    return v___x_2319_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(
    mut v_e_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
    mut v_a_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
    mut v_a_2324_: *mut crate::leanh::LeanObject,
    mut v_a_2325_: *mut crate::leanh::LeanObject,
    mut v_a_2326_: *mut crate::leanh::LeanObject,
    mut v_a_2327_: *mut crate::leanh::LeanObject,
    mut v_a_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u8 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: u8 = 0;
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: u8 = 0;
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v_fst_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2398_: u8 = 0;
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut v_a_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2420_: u8 = 0;
    let mut v_fst_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2425_: u8 = 0;
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2435_: u8 = 0;
    let mut v_isSharedCheck_2436_: u8 = 0;
    let mut v_a_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2444_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2457_: u8 = 0;
    let mut v_fst_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2462_: u8 = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2472_: u8 = 0;
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v_a_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2477_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: u8 = 0;
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v_fst_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut v_isSharedCheck_2510_: u8 = 0;
    let mut v_a_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: u8 = 0;
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v_fst_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut v_a_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v_val_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut v_a_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2584_: u8 = 0;
    let mut v_val_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2590_: u8 = 0;
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: u8 = 0;
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_unused_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_a_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2633_: u8 = 0;
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v_a_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2638_: u8 = 0;
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2642_: u8 = 0;
    let mut v_a_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_a_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2320_);
                v___x_2332_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2320_, v_a_2328_);
                if crate::leanh::lean_obj_tag(v___x_2332_) == 0 {
                    v_a_2333_ = crate::leanh::lean_ctor_get(v___x_2332_, 0);
                    crate::leanh::lean_inc(v_a_2333_);
                    crate::leanh::lean_dec_ref_known(v___x_2332_, 1);
                    v___x_2334_ = l_Lean_Expr_cleanupAnnotations(v_a_2333_);
                    v___x_2335_ = l_Lean_Expr_isApp(v___x_2334_);
                    if v___x_2335_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2334_);
                        v___x_2336_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                            v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_,
                            v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_,
                        );
                        return v___x_2336_;
                    } else {
                        v_arg_2337_ = crate::leanh::lean_ctor_get(v___x_2334_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2337_);
                        v___x_2338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2334_);
                        v___x_2339_ = l_Lean_Expr_isApp(v___x_2338_);
                        if v___x_2339_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2338_);
                            crate::leanh::lean_dec_ref(v_arg_2337_);
                            v___x_2340_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                                v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_,
                                v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_,
                            );
                            return v___x_2340_;
                        } else {
                            v_arg_2341_ = crate::leanh::lean_ctor_get(v___x_2338_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2341_);
                            v___x_2342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2338_);
                            v___x_2343_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2;
                            v___x_2344_ = l_Lean_Expr_isConstOf(v___x_2342_, v___x_2343_);
                            if v___x_2344_ == 0 {
                                v___x_2345_ = l_Lean_Expr_isApp(v___x_2342_);
                                if v___x_2345_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2342_);
                                    crate::leanh::lean_dec_ref(v_arg_2341_);
                                    crate::leanh::lean_dec_ref(v_arg_2337_);
                                    v___x_2346_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                                        v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_,
                                        v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_,
                                        v_a_2330_,
                                    );
                                    return v___x_2346_;
                                } else {
                                    v_arg_2347_ = crate::leanh::lean_ctor_get(v___x_2342_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2347_);
                                    v___x_2348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2342_);
                                    v___x_2349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5;
                                    v___x_2350_ = l_Lean_Expr_isConstOf(v___x_2348_, v___x_2349_);
                                    if v___x_2350_ == 0 {
                                        v___x_2351_ = l_Lean_Expr_isApp(v___x_2348_);
                                        if v___x_2351_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_2348_);
                                            crate::leanh::lean_dec_ref(v_arg_2347_);
                                            crate::leanh::lean_dec_ref(v_arg_2341_);
                                            crate::leanh::lean_dec_ref(v_arg_2337_);
                                            v___x_2352_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                                                v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_,
                                                v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_,
                                                v_a_2328_, v_a_2329_, v_a_2330_,
                                            );
                                            return v___x_2352_;
                                        } else {
                                            v___x_2353_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2348_);
                                            v___x_2354_ = l_Lean_Expr_isApp(v___x_2353_);
                                            if v___x_2354_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_2353_);
                                                crate::leanh::lean_dec_ref(v_arg_2347_);
                                                crate::leanh::lean_dec_ref(v_arg_2341_);
                                                crate::leanh::lean_dec_ref(v_arg_2337_);
                                                v___x_2355_ =
                                                    l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                                                        v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_,
                                                        v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_,
                                                        v_a_2328_, v_a_2329_, v_a_2330_,
                                                    );
                                                return v___x_2355_;
                                            } else {
                                                v___x_2356_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_2353_);
                                                v___x_2357_ = l_Lean_Expr_isApp(v___x_2356_);
                                                if v___x_2357_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_2356_);
                                                    crate::leanh::lean_dec_ref(v_arg_2347_);
                                                    crate::leanh::lean_dec_ref(v_arg_2341_);
                                                    crate::leanh::lean_dec_ref(v_arg_2337_);
                                                    v___x_2358_ =
                                                        l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                                                            v_e_2320_, v_a_2321_, v_a_2322_,
                                                            v_a_2323_, v_a_2324_, v_a_2325_,
                                                            v_a_2326_, v_a_2327_, v_a_2328_,
                                                            v_a_2329_, v_a_2330_,
                                                        );
                                                    return v___x_2358_;
                                                } else {
                                                    v___x_2359_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_2356_,
                                                    );
                                                    v___x_2360_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8;
                                                    v___x_2361_ = l_Lean_Expr_isConstOf(
                                                        v___x_2359_,
                                                        v___x_2360_,
                                                    );
                                                    if v___x_2361_ == 0 {
                                                        v___x_2362_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11;
                                                        v___x_2363_ = l_Lean_Expr_isConstOf(
                                                            v___x_2359_,
                                                            v___x_2362_,
                                                        );
                                                        if v___x_2363_ == 0 {
                                                            v___x_2364_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14;
                                                            v___x_2365_ = l_Lean_Expr_isConstOf(
                                                                v___x_2359_,
                                                                v___x_2364_,
                                                            );
                                                            if v___x_2365_ == 0 {
                                                                v___x_2366_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17;
                                                                v___x_2367_ = l_Lean_Expr_isConstOf(
                                                                    v___x_2359_,
                                                                    v___x_2366_,
                                                                );
                                                                if v___x_2367_ == 0 {
                                                                    v___x_2368_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20;
                                                                    v___x_2369_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_2359_,
                                                                            v___x_2368_,
                                                                        );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_2359_,
                                                                    );
                                                                    if v___x_2369_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2347_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2341_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2337_,
                                                                        );
                                                                        v___x_2370_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                        return v___x_2370_;
                                                                    } else {
                                                                        v___x_2371_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_2347_, v_a_2328_);
                                                                        if crate::leanh::lean_obj_tag(v___x_2371_) == 0 {
v_a_2372_ = crate::leanh::lean_ctor_get(v___x_2371_, 0);
crate::leanh::lean_inc(v_a_2372_);
crate::leanh::lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = (crate::leanh::lean_unbox(v_a_2372_) as u8);
crate::leanh::lean_dec(v_a_2372_);
if v___x_2373_ == 0 {
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
v___x_2374_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2374_;
} else {
crate::leanh::lean_dec_ref(v_e_2320_);
crate::leanh::lean_inc_ref(v_arg_2341_);
v___x_2375_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2341_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if crate::leanh::lean_obj_tag(v___x_2375_) == 0 {
v_a_2376_ = crate::leanh::lean_ctor_get(v___x_2375_, 0);
crate::leanh::lean_inc(v_a_2376_);
crate::leanh::lean_dec_ref_known(v___x_2375_, 1);
v_fst_2377_ = crate::leanh::lean_ctor_get(v_a_2376_, 0);
crate::leanh::lean_inc(v_fst_2377_);
v_snd_2378_ = crate::leanh::lean_ctor_get(v_a_2376_, 1);
crate::leanh::lean_inc(v_snd_2378_);
crate::leanh::lean_dec(v_a_2376_);
crate::leanh::lean_inc_ref(v_arg_2337_);
v___x_2379_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2337_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if crate::leanh::lean_obj_tag(v___x_2379_) == 0 {
v_a_2380_ = crate::leanh::lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2399_ = (!crate::leanh::lean_is_exclusive(v___x_2379_)) as u8;
if v_isSharedCheck_2399_ == 0 {
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2399_;
state = 1; continue;
} else {
crate::leanh::lean_inc(v_a_2380_);
crate::leanh::lean_dec(v___x_2379_);
v___x_2382_ = crate::leanh::lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2399_;
state = 1; continue;
}
} else {
crate::leanh::lean_dec(v_snd_2378_);
crate::leanh::lean_dec(v_fst_2377_);
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
return v___x_2379_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
return v___x_2375_;
}
}
} else {
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
crate::leanh::lean_dec_ref(v_e_2320_);
v_a_2400_ = crate::leanh::lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2407_ = (!crate::leanh::lean_is_exclusive(v___x_2371_)) as u8;
if v_isSharedCheck_2407_ == 0 {
v___x_2402_ = v___x_2371_;
v_isShared_2403_ = v_isSharedCheck_2407_;
state = 5; continue;
} else {
crate::leanh::lean_inc(v_a_2400_);
crate::leanh::lean_dec(v___x_2371_);
v___x_2402_ = crate::leanh::lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
state = 5; continue;
}
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_2359_,
                                                                    );
                                                                    v___x_2408_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_2347_, v_a_2328_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_2408_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_2409_ = crate::leanh::lean_ctor_get(v___x_2408_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2409_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_2408_, 1);
                                                                        v___x_2410_ = (crate::leanh::lean_unbox(v_a_2409_) as u8);
                                                                        crate::leanh::lean_dec(
                                                                            v_a_2409_,
                                                                        );
                                                                        if v___x_2410_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_2341_);
                                                                            crate::leanh::lean_dec_ref(v_arg_2337_);
                                                                            v___x_2411_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                            return v___x_2411_;
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v_e_2320_);
                                                                            crate::leanh::lean_inc_ref(v_arg_2341_);
                                                                            v___x_2412_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2341_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                            if crate::leanh::lean_obj_tag(v___x_2412_) == 0 {
v_a_2413_ = crate::leanh::lean_ctor_get(v___x_2412_, 0);
crate::leanh::lean_inc(v_a_2413_);
crate::leanh::lean_dec_ref_known(v___x_2412_, 1);
v_fst_2414_ = crate::leanh::lean_ctor_get(v_a_2413_, 0);
crate::leanh::lean_inc(v_fst_2414_);
v_snd_2415_ = crate::leanh::lean_ctor_get(v_a_2413_, 1);
crate::leanh::lean_inc(v_snd_2415_);
crate::leanh::lean_dec(v_a_2413_);
crate::leanh::lean_inc_ref(v_arg_2337_);
v___x_2416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2337_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if crate::leanh::lean_obj_tag(v___x_2416_) == 0 {
v_a_2417_ = crate::leanh::lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2436_ = (!crate::leanh::lean_is_exclusive(v___x_2416_)) as u8;
if v_isSharedCheck_2436_ == 0 {
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2436_;
state = 7; continue;
} else {
crate::leanh::lean_inc(v_a_2417_);
crate::leanh::lean_dec(v___x_2416_);
v___x_2419_ = crate::leanh::lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2436_;
state = 7; continue;
}
} else {
crate::leanh::lean_dec(v_snd_2415_);
crate::leanh::lean_dec(v_fst_2414_);
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
return v___x_2416_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
return v___x_2412_;
}
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2341_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2337_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_2320_,
                                                                        );
                                                                        v_a_2437_ = crate::leanh::lean_ctor_get(v___x_2408_, 0);
                                                                        v_isSharedCheck_2444_ = (!crate::leanh::lean_is_exclusive(v___x_2408_)) as u8;
                                                                        if v_isSharedCheck_2444_
                                                                            == 0
                                                                        {
                                                                            v___x_2439_ =
                                                                                v___x_2408_;
                                                                            v_isShared_2440_ = v_isSharedCheck_2444_;
                                                                            state = 11;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_2437_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_2408_,
                                                                            );
                                                                            v___x_2439_ = crate::leanh::lean_box(0);
                                                                            v_isShared_2440_ = v_isSharedCheck_2444_;
                                                                            state = 11;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2359_,
                                                                );
                                                                v___x_2445_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_2347_, v_a_2328_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_2445_,
                                                                ) == 0
                                                                {
                                                                    v_a_2446_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_2445_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_2446_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_2445_, 1);
                                                                    v___x_2447_ =
                                                                        (crate::leanh::lean_unbox(
                                                                            v_a_2446_,
                                                                        )
                                                                            as u8);
                                                                    crate::leanh::lean_dec(
                                                                        v_a_2446_,
                                                                    );
                                                                    if v___x_2447_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2341_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2337_,
                                                                        );
                                                                        v___x_2448_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                        return v___x_2448_;
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_2320_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_2341_,
                                                                        );
                                                                        v___x_2449_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2341_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                        if crate::leanh::lean_obj_tag(v___x_2449_) == 0 {
v_a_2450_ = crate::leanh::lean_ctor_get(v___x_2449_, 0);
crate::leanh::lean_inc(v_a_2450_);
crate::leanh::lean_dec_ref_known(v___x_2449_, 1);
v_fst_2451_ = crate::leanh::lean_ctor_get(v_a_2450_, 0);
crate::leanh::lean_inc(v_fst_2451_);
v_snd_2452_ = crate::leanh::lean_ctor_get(v_a_2450_, 1);
crate::leanh::lean_inc(v_snd_2452_);
crate::leanh::lean_dec(v_a_2450_);
crate::leanh::lean_inc_ref(v_arg_2337_);
v___x_2453_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2337_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if crate::leanh::lean_obj_tag(v___x_2453_) == 0 {
v_a_2454_ = crate::leanh::lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2473_ = (!crate::leanh::lean_is_exclusive(v___x_2453_)) as u8;
if v_isSharedCheck_2473_ == 0 {
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2473_;
state = 13; continue;
} else {
crate::leanh::lean_inc(v_a_2454_);
crate::leanh::lean_dec(v___x_2453_);
v___x_2456_ = crate::leanh::lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2473_;
state = 13; continue;
}
} else {
crate::leanh::lean_dec(v_snd_2452_);
crate::leanh::lean_dec(v_fst_2451_);
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
return v___x_2453_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
return v___x_2449_;
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2341_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2337_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_2320_,
                                                                    );
                                                                    v_a_2474_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_2445_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_2481_ = (!crate::leanh::lean_is_exclusive(v___x_2445_)) as u8;
                                                                    if v_isSharedCheck_2481_ == 0 {
                                                                        v___x_2476_ = v___x_2445_;
                                                                        v_isShared_2477_ =
                                                                            v_isSharedCheck_2481_;
                                                                        state = 17;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2474_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_2445_,
                                                                        );
                                                                        v___x_2476_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_2477_ =
                                                                            v_isSharedCheck_2481_;
                                                                        state = 17;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_2359_);
                                                            v___x_2482_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_2347_, v_a_2328_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_2482_,
                                                            ) == 0
                                                            {
                                                                v_a_2483_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_2482_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_2483_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_2482_,
                                                                    1,
                                                                );
                                                                v___x_2484_ =
                                                                    (crate::leanh::lean_unbox(
                                                                        v_a_2483_,
                                                                    )
                                                                        as u8);
                                                                crate::leanh::lean_dec(v_a_2483_);
                                                                if v___x_2484_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2341_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2337_,
                                                                    );
                                                                    v___x_2485_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                    return v___x_2485_;
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_2320_,
                                                                    );
                                                                    crate::leanh::lean_inc_ref(
                                                                        v_arg_2341_,
                                                                    );
                                                                    v___x_2486_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2341_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_2486_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_2487_ = crate::leanh::lean_ctor_get(v___x_2486_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2487_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_2486_, 1);
                                                                        v_fst_2488_ = crate::leanh::lean_ctor_get(v_a_2487_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_fst_2488_,
                                                                        );
                                                                        v_snd_2489_ = crate::leanh::lean_ctor_get(v_a_2487_, 1);
                                                                        crate::leanh::lean_inc(
                                                                            v_snd_2489_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_2487_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_2337_,
                                                                        );
                                                                        v___x_2490_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2337_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                        if crate::leanh::lean_obj_tag(v___x_2490_) == 0 {
v_a_2491_ = crate::leanh::lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2510_ = (!crate::leanh::lean_is_exclusive(v___x_2490_)) as u8;
if v_isSharedCheck_2510_ == 0 {
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2510_;
state = 19; continue;
} else {
crate::leanh::lean_inc(v_a_2491_);
crate::leanh::lean_dec(v___x_2490_);
v___x_2493_ = crate::leanh::lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2510_;
state = 19; continue;
}
} else {
crate::leanh::lean_dec(v_snd_2489_);
crate::leanh::lean_dec(v_fst_2488_);
crate::leanh::lean_dec_ref(v_arg_2341_);
crate::leanh::lean_dec_ref(v_arg_2337_);
return v___x_2490_;
}
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2341_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2337_,
                                                                        );
                                                                        return v___x_2486_;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2341_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2337_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_2320_,
                                                                );
                                                                v_a_2511_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_2482_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_2518_ = (!crate::leanh::lean_is_exclusive(v___x_2482_)) as u8;
                                                                if v_isSharedCheck_2518_ == 0 {
                                                                    v___x_2513_ = v___x_2482_;
                                                                    v_isShared_2514_ =
                                                                        v_isSharedCheck_2518_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_2511_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_2482_,
                                                                    );
                                                                    v___x_2513_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_2514_ =
                                                                        v_isSharedCheck_2518_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_2359_);
                                                        v___x_2519_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_2347_, v_a_2328_);
                                                        if crate::leanh::lean_obj_tag(v___x_2519_)
                                                            == 0
                                                        {
                                                            v_a_2520_ = crate::leanh::lean_ctor_get(
                                                                v___x_2519_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_2520_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_2519_,
                                                                1,
                                                            );
                                                            v___x_2521_ = (crate::leanh::lean_unbox(
                                                                v_a_2520_,
                                                            )
                                                                as u8);
                                                            crate::leanh::lean_dec(v_a_2520_);
                                                            if v___x_2521_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2341_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2337_,
                                                                );
                                                                v___x_2522_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                return v___x_2522_;
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_2320_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_arg_2341_,
                                                                );
                                                                v___x_2523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_2341_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_2523_,
                                                                ) == 0
                                                                {
                                                                    v_a_2524_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_2523_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_2543_ = (!crate::leanh::lean_is_exclusive(v___x_2523_)) as u8;
                                                                    if v_isSharedCheck_2543_ == 0 {
                                                                        v___x_2526_ = v___x_2523_;
                                                                        v_isShared_2527_ =
                                                                            v_isSharedCheck_2543_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2524_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_2523_,
                                                                        );
                                                                        v___x_2526_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_2527_ =
                                                                            v_isSharedCheck_2543_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2341_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2337_,
                                                                    );
                                                                    return v___x_2523_;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_2341_);
                                                            crate::leanh::lean_dec_ref(v_arg_2337_);
                                                            crate::leanh::lean_dec_ref(v_e_2320_);
                                                            v_a_2544_ = crate::leanh::lean_ctor_get(
                                                                v___x_2519_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2551_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2519_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2551_ == 0 {
                                                                v___x_2546_ = v___x_2519_;
                                                                v_isShared_2547_ =
                                                                    v_isSharedCheck_2551_;
                                                                state = 29;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2544_);
                                                                crate::leanh::lean_dec(v___x_2519_);
                                                                v___x_2546_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2547_ =
                                                                    v_isSharedCheck_2551_;
                                                                state = 29;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_2348_);
                                        crate::leanh::lean_dec_ref(v_arg_2347_);
                                        crate::leanh::lean_dec_ref(v_arg_2341_);
                                        crate::leanh::lean_dec_ref(v_arg_2337_);
                                        v___x_2552_ = l_Lean_Meta_getNatValue_x3f(
                                            v_e_2320_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2552_) == 0 {
                                            v_a_2553_ = crate::leanh::lean_ctor_get(v___x_2552_, 0);
                                            v_isSharedCheck_2567_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2552_))
                                                    as u8;
                                            if v_isSharedCheck_2567_ == 0 {
                                                v___x_2555_ = v___x_2552_;
                                                v_isShared_2556_ = v_isSharedCheck_2567_;
                                                state = 31;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2553_);
                                                crate::leanh::lean_dec(v___x_2552_);
                                                v___x_2555_ = crate::leanh::lean_box(0);
                                                v_isShared_2556_ = v_isSharedCheck_2567_;
                                                state = 31;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_e_2320_);
                                            v_a_2568_ = crate::leanh::lean_ctor_get(v___x_2552_, 0);
                                            v_isSharedCheck_2575_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2552_))
                                                    as u8;
                                            if v_isSharedCheck_2575_ == 0 {
                                                v___x_2570_ = v___x_2552_;
                                                v_isShared_2571_ = v_isSharedCheck_2575_;
                                                state = 33;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2568_);
                                                crate::leanh::lean_dec(v___x_2552_);
                                                v___x_2570_ = crate::leanh::lean_box(0);
                                                v_isShared_2571_ = v_isSharedCheck_2575_;
                                                state = 33;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2342_);
                                v___x_2576_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42);
                                crate::leanh::lean_inc_ref(v_arg_2341_);
                                v___x_2577_ = l_Lean_Expr_app___override(v___x_2576_, v_arg_2341_);
                                v___x_2578_ =
                                    l_Lean_Meta_Sym_shareCommon___redArg(v___x_2577_, v_a_2326_);
                                if crate::leanh::lean_obj_tag(v___x_2578_) == 0 {
                                    v_a_2579_ = crate::leanh::lean_ctor_get(v___x_2578_, 0);
                                    crate::leanh::lean_inc(v_a_2579_);
                                    crate::leanh::lean_dec_ref_known(v___x_2578_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2337_);
                                    v___x_2580_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(
                                        v_arg_2337_,
                                        v_a_2579_,
                                        v_a_2321_,
                                        v_a_2322_,
                                        v_a_2323_,
                                        v_a_2324_,
                                        v_a_2325_,
                                        v_a_2326_,
                                        v_a_2327_,
                                        v_a_2328_,
                                        v_a_2329_,
                                        v_a_2330_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2580_) == 0 {
                                        v_a_2581_ = crate::leanh::lean_ctor_get(v___x_2580_, 0);
                                        v_isSharedCheck_2634_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2580_)) as u8;
                                        if v_isSharedCheck_2634_ == 0 {
                                            v___x_2583_ = v___x_2580_;
                                            v_isShared_2584_ = v_isSharedCheck_2634_;
                                            state = 35;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2581_);
                                            crate::leanh::lean_dec(v___x_2580_);
                                            v___x_2583_ = crate::leanh::lean_box(0);
                                            v_isShared_2584_ = v_isSharedCheck_2634_;
                                            state = 35;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_2341_);
                                        crate::leanh::lean_dec_ref(v_arg_2337_);
                                        crate::leanh::lean_dec_ref(v_e_2320_);
                                        v_a_2635_ = crate::leanh::lean_ctor_get(v___x_2580_, 0);
                                        v_isSharedCheck_2642_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2580_)) as u8;
                                        if v_isSharedCheck_2642_ == 0 {
                                            v___x_2637_ = v___x_2580_;
                                            v_isShared_2638_ = v_isSharedCheck_2642_;
                                            state = 45;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2635_);
                                            crate::leanh::lean_dec(v___x_2580_);
                                            v___x_2637_ = crate::leanh::lean_box(0);
                                            v_isShared_2638_ = v_isSharedCheck_2642_;
                                            state = 45;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_2341_);
                                    crate::leanh::lean_dec_ref(v_arg_2337_);
                                    crate::leanh::lean_dec_ref(v_e_2320_);
                                    v_a_2643_ = crate::leanh::lean_ctor_get(v___x_2578_, 0);
                                    v_isSharedCheck_2650_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2578_)) as u8;
                                    if v_isSharedCheck_2650_ == 0 {
                                        v___x_2645_ = v___x_2578_;
                                        v_isShared_2646_ = v_isSharedCheck_2650_;
                                        state = 47;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2643_);
                                        crate::leanh::lean_dec(v___x_2578_);
                                        v___x_2645_ = crate::leanh::lean_box(0);
                                        v_isShared_2646_ = v_isSharedCheck_2650_;
                                        state = 47;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2320_);
                    v_a_2651_ = crate::leanh::lean_ctor_get(v___x_2332_, 0);
                    v_isSharedCheck_2658_ = (!crate::leanh::lean_is_exclusive(v___x_2332_)) as u8;
                    if v_isSharedCheck_2658_ == 0 {
                        v___x_2653_ = v___x_2332_;
                        v_isShared_2654_ = v_isSharedCheck_2658_;
                        state = 49;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2651_);
                        crate::leanh::lean_dec(v___x_2332_);
                        v___x_2653_ = crate::leanh::lean_box(0);
                        v_isShared_2654_ = v_isSharedCheck_2658_;
                        state = 49;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2384_ = crate::leanh::lean_ctor_get(v_a_2380_, 0);
                v_snd_2385_ = crate::leanh::lean_ctor_get(v_a_2380_, 1);
                v_isSharedCheck_2398_ = (!crate::leanh::lean_is_exclusive(v_a_2380_)) as u8;
                if v_isSharedCheck_2398_ == 0 {
                    v___x_2387_ = v_a_2380_;
                    v_isShared_2388_ = v_isSharedCheck_2398_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2385_);
                    crate::leanh::lean_inc(v_fst_2384_);
                    crate::leanh::lean_dec(v_a_2380_);
                    v___x_2387_ = crate::leanh::lean_box(0);
                    v_isShared_2388_ = v_isSharedCheck_2398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2389_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25);
                crate::leanh::lean_inc(v_fst_2384_);
                crate::leanh::lean_inc(v_fst_2377_);
                v___x_2390_ = l_Lean_mkApp6(
                    v___x_2389_,
                    v_arg_2341_,
                    v_arg_2337_,
                    v_fst_2377_,
                    v_fst_2384_,
                    v_snd_2378_,
                    v_snd_2385_,
                );
                v___x_2391_ = l_Lean_mkIntAdd(v_fst_2377_, v_fst_2384_);
                if v_isShared_2388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2387_, 1, v___x_2390_);
                    crate::leanh::lean_ctor_set(v___x_2387_, 0, v___x_2391_);
                    v___x_2393_ = v___x_2387_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2390_);
                    v___x_2393_ = v_reuseFailAlloc_2397_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2382_, 0, v___x_2393_);
                    v___x_2395_ = v___x_2382_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
                    v___x_2395_ = v_reuseFailAlloc_2396_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2395_;
            }
            5 => {
                if v_isShared_2403_ == 0 {
                    v___x_2405_ = v___x_2402_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
                    v___x_2405_ = v_reuseFailAlloc_2406_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2405_;
            }
            7 => {
                v_fst_2421_ = crate::leanh::lean_ctor_get(v_a_2417_, 0);
                v_snd_2422_ = crate::leanh::lean_ctor_get(v_a_2417_, 1);
                v_isSharedCheck_2435_ = (!crate::leanh::lean_is_exclusive(v_a_2417_)) as u8;
                if v_isSharedCheck_2435_ == 0 {
                    v___x_2424_ = v_a_2417_;
                    v_isShared_2425_ = v_isSharedCheck_2435_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2422_);
                    crate::leanh::lean_inc(v_fst_2421_);
                    crate::leanh::lean_dec(v_a_2417_);
                    v___x_2424_ = crate::leanh::lean_box(0);
                    v_isShared_2425_ = v_isSharedCheck_2435_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2426_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28);
                crate::leanh::lean_inc(v_fst_2421_);
                crate::leanh::lean_inc(v_fst_2414_);
                v___x_2427_ = l_Lean_mkApp6(
                    v___x_2426_,
                    v_arg_2341_,
                    v_arg_2337_,
                    v_fst_2414_,
                    v_fst_2421_,
                    v_snd_2415_,
                    v_snd_2422_,
                );
                v___x_2428_ = l_Lean_mkIntMul(v_fst_2414_, v_fst_2421_);
                if v_isShared_2425_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2424_, 1, v___x_2427_);
                    crate::leanh::lean_ctor_set(v___x_2424_, 0, v___x_2428_);
                    v___x_2430_ = v___x_2424_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2427_);
                    v___x_2430_ = v_reuseFailAlloc_2434_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2420_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2419_, 0, v___x_2430_);
                    v___x_2432_ = v___x_2419_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
                    v___x_2432_ = v_reuseFailAlloc_2433_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2432_;
            }
            11 => {
                if v_isShared_2440_ == 0 {
                    v___x_2442_ = v___x_2439_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
                    v___x_2442_ = v_reuseFailAlloc_2443_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2442_;
            }
            13 => {
                v_fst_2458_ = crate::leanh::lean_ctor_get(v_a_2454_, 0);
                v_snd_2459_ = crate::leanh::lean_ctor_get(v_a_2454_, 1);
                v_isSharedCheck_2472_ = (!crate::leanh::lean_is_exclusive(v_a_2454_)) as u8;
                if v_isSharedCheck_2472_ == 0 {
                    v___x_2461_ = v_a_2454_;
                    v_isShared_2462_ = v_isSharedCheck_2472_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2459_);
                    crate::leanh::lean_inc(v_fst_2458_);
                    crate::leanh::lean_dec(v_a_2454_);
                    v___x_2461_ = crate::leanh::lean_box(0);
                    v_isShared_2462_ = v_isSharedCheck_2472_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2463_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31);
                crate::leanh::lean_inc(v_fst_2458_);
                crate::leanh::lean_inc(v_fst_2451_);
                v___x_2464_ = l_Lean_mkApp6(
                    v___x_2463_,
                    v_arg_2341_,
                    v_arg_2337_,
                    v_fst_2451_,
                    v_fst_2458_,
                    v_snd_2452_,
                    v_snd_2459_,
                );
                v___x_2465_ = l_Lean_mkIntDiv(v_fst_2451_, v_fst_2458_);
                if v_isShared_2462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2461_, 1, v___x_2464_);
                    crate::leanh::lean_ctor_set(v___x_2461_, 0, v___x_2465_);
                    v___x_2467_ = v___x_2461_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2471_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2464_);
                    v___x_2467_ = v_reuseFailAlloc_2471_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2456_, 0, v___x_2467_);
                    v___x_2469_ = v___x_2456_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
                    v___x_2469_ = v_reuseFailAlloc_2470_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2469_;
            }
            17 => {
                if v_isShared_2477_ == 0 {
                    v___x_2479_ = v___x_2476_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
                    v___x_2479_ = v_reuseFailAlloc_2480_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2479_;
            }
            19 => {
                v_fst_2495_ = crate::leanh::lean_ctor_get(v_a_2491_, 0);
                v_snd_2496_ = crate::leanh::lean_ctor_get(v_a_2491_, 1);
                v_isSharedCheck_2509_ = (!crate::leanh::lean_is_exclusive(v_a_2491_)) as u8;
                if v_isSharedCheck_2509_ == 0 {
                    v___x_2498_ = v_a_2491_;
                    v_isShared_2499_ = v_isSharedCheck_2509_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2496_);
                    crate::leanh::lean_inc(v_fst_2495_);
                    crate::leanh::lean_dec(v_a_2491_);
                    v___x_2498_ = crate::leanh::lean_box(0);
                    v_isShared_2499_ = v_isSharedCheck_2509_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_2500_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34);
                crate::leanh::lean_inc(v_fst_2495_);
                crate::leanh::lean_inc(v_fst_2488_);
                v___x_2501_ = l_Lean_mkApp6(
                    v___x_2500_,
                    v_arg_2341_,
                    v_arg_2337_,
                    v_fst_2488_,
                    v_fst_2495_,
                    v_snd_2489_,
                    v_snd_2496_,
                );
                v___x_2502_ = l_Lean_mkIntMod(v_fst_2488_, v_fst_2495_);
                if v_isShared_2499_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2498_, 1, v___x_2501_);
                    crate::leanh::lean_ctor_set(v___x_2498_, 0, v___x_2502_);
                    v___x_2504_ = v___x_2498_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2508_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2501_);
                    v___x_2504_ = v_reuseFailAlloc_2508_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_2494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2504_);
                    v___x_2506_ = v___x_2493_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
                    v___x_2506_ = v_reuseFailAlloc_2507_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2506_;
            }
            23 => {
                if v_isShared_2514_ == 0 {
                    v___x_2516_ = v___x_2513_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
                    v___x_2516_ = v_reuseFailAlloc_2517_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2516_;
            }
            25 => {
                v_fst_2528_ = crate::leanh::lean_ctor_get(v_a_2524_, 0);
                v_snd_2529_ = crate::leanh::lean_ctor_get(v_a_2524_, 1);
                v_isSharedCheck_2542_ = (!crate::leanh::lean_is_exclusive(v_a_2524_)) as u8;
                if v_isSharedCheck_2542_ == 0 {
                    v___x_2531_ = v_a_2524_;
                    v_isShared_2532_ = v_isSharedCheck_2542_;
                    state = 26;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2529_);
                    crate::leanh::lean_inc(v_fst_2528_);
                    crate::leanh::lean_dec(v_a_2524_);
                    v___x_2531_ = crate::leanh::lean_box(0);
                    v_isShared_2532_ = v_isSharedCheck_2542_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2533_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37);
                crate::leanh::lean_inc(v_fst_2528_);
                crate::leanh::lean_inc_ref(v_arg_2337_);
                v___x_2534_ = l_Lean_mkApp4(
                    v___x_2533_,
                    v_arg_2341_,
                    v_arg_2337_,
                    v_fst_2528_,
                    v_snd_2529_,
                );
                v___x_2535_ = l_Lean_mkIntPowNat(v_fst_2528_, v_arg_2337_);
                if v_isShared_2532_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2531_, 1, v___x_2534_);
                    crate::leanh::lean_ctor_set(v___x_2531_, 0, v___x_2535_);
                    v___x_2537_ = v___x_2531_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2534_);
                    v___x_2537_ = v_reuseFailAlloc_2541_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2527_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2537_);
                    v___x_2539_ = v___x_2526_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
                    v___x_2539_ = v_reuseFailAlloc_2540_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2539_;
            }
            29 => {
                if v_isShared_2547_ == 0 {
                    v___x_2549_ = v___x_2546_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
                    v___x_2549_ = v_reuseFailAlloc_2550_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2549_;
            }
            31 => {
                if crate::leanh::lean_obj_tag(v_a_2553_) == 1 {
                    v_val_2557_ = crate::leanh::lean_ctor_get(v_a_2553_, 0);
                    crate::leanh::lean_inc(v_val_2557_);
                    crate::leanh::lean_dec_ref_known(v_a_2553_, 1);
                    v___x_2558_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40);
                    v___x_2559_ = l_Lean_Expr_app___override(v___x_2558_, v_e_2320_);
                    v___x_2560_ = lean_nat_to_int(v_val_2557_);
                    v___x_2561_ = l_Lean_mkIntLit(v___x_2560_);
                    crate::leanh::lean_dec(v___x_2560_);
                    v___x_2562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2562_, 0, v___x_2561_);
                    crate::leanh::lean_ctor_set(v___x_2562_, 1, v___x_2559_);
                    if v_isShared_2556_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2555_, 0, v___x_2562_);
                        v___x_2564_ = v___x_2555_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_2565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
                        v___x_2564_ = v_reuseFailAlloc_2565_;
                        state = 32;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2555_);
                    crate::leanh::lean_dec(v_a_2553_);
                    v___x_2566_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                        v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_,
                        v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_,
                    );
                    return v___x_2566_;
                }
            }
            32 => {
                return v___x_2564_;
            }
            33 => {
                if v_isShared_2571_ == 0 {
                    v___x_2573_ = v___x_2570_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
                    v___x_2573_ = v_reuseFailAlloc_2574_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2573_;
            }
            35 => {
                if crate::leanh::lean_obj_tag(v_a_2581_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_2320_);
                    v_val_2585_ = crate::leanh::lean_ctor_get(v_a_2581_, 0);
                    crate::leanh::lean_inc(v_val_2585_);
                    crate::leanh::lean_dec_ref_known(v_a_2581_, 1);
                    v_fst_2586_ = crate::leanh::lean_ctor_get(v_val_2585_, 0);
                    v_snd_2587_ = crate::leanh::lean_ctor_get(v_val_2585_, 1);
                    v_isSharedCheck_2599_ = (!crate::leanh::lean_is_exclusive(v_val_2585_)) as u8;
                    if v_isSharedCheck_2599_ == 0 {
                        v___x_2589_ = v_val_2585_;
                        v_isShared_2590_ = v_isSharedCheck_2599_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2587_);
                        crate::leanh::lean_inc(v_fst_2586_);
                        crate::leanh::lean_dec(v_val_2585_);
                        v___x_2589_ = crate::leanh::lean_box(0);
                        v_isShared_2590_ = v_isSharedCheck_2599_;
                        state = 36;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2583_);
                    crate::leanh::lean_dec(v_a_2581_);
                    v___x_2600_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2321_, v_a_2329_);
                    if crate::leanh::lean_obj_tag(v___x_2600_) == 0 {
                        v_a_2601_ = crate::leanh::lean_ctor_get(v___x_2600_, 0);
                        crate::leanh::lean_inc(v_a_2601_);
                        crate::leanh::lean_dec_ref_known(v___x_2600_, 1);
                        crate::leanh::lean_inc_ref(v_e_2320_);
                        v___x_2602_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                            v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_,
                            v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2602_) == 0 {
                            v_a_2603_ = crate::leanh::lean_ctor_get(v___x_2602_, 0);
                            crate::leanh::lean_inc(v_a_2603_);
                            v_natToIntMap_2604_ = crate::leanh::lean_ctor_get(v_a_2601_, 4);
                            crate::leanh::lean_inc_ref(v_natToIntMap_2604_);
                            crate::leanh::lean_dec(v_a_2601_);
                            v___x_2605_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natToIntMap_2604_, v_e_2320_);
                            crate::leanh::lean_dec_ref(v_e_2320_);
                            crate::leanh::lean_dec_ref(v_natToIntMap_2604_);
                            if v___x_2605_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2602_, 1);
                                v___x_2606_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48);
                                v___x_2607_ = l_Lean_mkAppB(v___x_2606_, v_arg_2341_, v_arg_2337_);
                                v___x_2608_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_2609_ = l_Lean_Meta_Grind_pushNewFact(
                                    v___x_2607_,
                                    v___x_2608_,
                                    v_a_2321_,
                                    v_a_2322_,
                                    v_a_2323_,
                                    v_a_2324_,
                                    v_a_2325_,
                                    v_a_2326_,
                                    v_a_2327_,
                                    v_a_2328_,
                                    v_a_2329_,
                                    v_a_2330_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2609_) == 0 {
                                    v_isSharedCheck_2616_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2609_)) as u8;
                                    if v_isSharedCheck_2616_ == 0 {
                                        v_unused_2617_ =
                                            crate::leanh::lean_ctor_get(v___x_2609_, 0);
                                        crate::leanh::lean_dec(v_unused_2617_);
                                        v___x_2611_ = v___x_2609_;
                                        v_isShared_2612_ = v_isSharedCheck_2616_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_2609_);
                                        v___x_2611_ = crate::leanh::lean_box(0);
                                        v_isShared_2612_ = v_isSharedCheck_2616_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2603_);
                                    v_a_2618_ = crate::leanh::lean_ctor_get(v___x_2609_, 0);
                                    v_isSharedCheck_2625_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2609_)) as u8;
                                    if v_isSharedCheck_2625_ == 0 {
                                        v___x_2620_ = v___x_2609_;
                                        v_isShared_2621_ = v_isSharedCheck_2625_;
                                        state = 41;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2618_);
                                        crate::leanh::lean_dec(v___x_2609_);
                                        v___x_2620_ = crate::leanh::lean_box(0);
                                        v_isShared_2621_ = v_isSharedCheck_2625_;
                                        state = 41;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2603_);
                                crate::leanh::lean_dec_ref(v_arg_2341_);
                                crate::leanh::lean_dec_ref(v_arg_2337_);
                                return v___x_2602_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2601_);
                            crate::leanh::lean_dec_ref(v_arg_2341_);
                            crate::leanh::lean_dec_ref(v_arg_2337_);
                            crate::leanh::lean_dec_ref(v_e_2320_);
                            return v___x_2602_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2341_);
                        crate::leanh::lean_dec_ref(v_arg_2337_);
                        crate::leanh::lean_dec_ref(v_e_2320_);
                        v_a_2626_ = crate::leanh::lean_ctor_get(v___x_2600_, 0);
                        v_isSharedCheck_2633_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2600_)) as u8;
                        if v_isSharedCheck_2633_ == 0 {
                            v___x_2628_ = v___x_2600_;
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2626_);
                            crate::leanh::lean_dec(v___x_2600_);
                            v___x_2628_ = crate::leanh::lean_box(0);
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 43;
                            continue;
                        }
                    }
                }
            }
            36 => {
                v___x_2591_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45);
                crate::leanh::lean_inc(v_fst_2586_);
                v___x_2592_ = l_Lean_mkApp4(
                    v___x_2591_,
                    v_arg_2341_,
                    v_arg_2337_,
                    v_fst_2586_,
                    v_snd_2587_,
                );
                if v_isShared_2590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2589_, 1, v___x_2592_);
                    v___x_2594_ = v___x_2589_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_fst_2586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2592_);
                    v___x_2594_ = v_reuseFailAlloc_2598_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2584_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2583_, 0, v___x_2594_);
                    v___x_2596_ = v___x_2583_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
                    v___x_2596_ = v_reuseFailAlloc_2597_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2596_;
            }
            39 => {
                if v_isShared_2612_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2611_, 0, v_a_2603_);
                    v___x_2614_ = v___x_2611_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2603_);
                    v___x_2614_ = v_reuseFailAlloc_2615_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2614_;
            }
            41 => {
                if v_isShared_2621_ == 0 {
                    v___x_2623_ = v___x_2620_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
                    v___x_2623_ = v_reuseFailAlloc_2624_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2623_;
            }
            43 => {
                if v_isShared_2629_ == 0 {
                    v___x_2631_ = v___x_2628_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
                    v___x_2631_ = v_reuseFailAlloc_2632_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_2631_;
            }
            45 => {
                if v_isShared_2638_ == 0 {
                    v___x_2640_ = v___x_2637_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2641_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
                    v___x_2640_ = v_reuseFailAlloc_2641_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2640_;
            }
            47 => {
                if v_isShared_2646_ == 0 {
                    v___x_2648_ = v___x_2645_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
                    v___x_2648_ = v_reuseFailAlloc_2649_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2648_;
            }
            49 => {
                if v_isShared_2654_ == 0 {
                    v___x_2656_ = v___x_2653_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
                    v___x_2656_ = v_reuseFailAlloc_2657_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_2656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___boxed(
    mut v_e_2659_: *mut crate::leanh::LeanObject,
    mut v_a_2660_: *mut crate::leanh::LeanObject,
    mut v_a_2661_: *mut crate::leanh::LeanObject,
    mut v_a_2662_: *mut crate::leanh::LeanObject,
    mut v_a_2663_: *mut crate::leanh::LeanObject,
    mut v_a_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
    mut v_a_2669_: *mut crate::leanh::LeanObject,
    mut v_a_2670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2671_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_e_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
    crate::leanh::lean_dec(v_a_2669_);
    crate::leanh::lean_dec_ref(v_a_2668_);
    crate::leanh::lean_dec(v_a_2667_);
    crate::leanh::lean_dec_ref(v_a_2666_);
    crate::leanh::lean_dec(v_a_2665_);
    crate::leanh::lean_dec_ref(v_a_2664_);
    crate::leanh::lean_dec(v_a_2663_);
    crate::leanh::lean_dec_ref(v_a_2662_);
    crate::leanh::lean_dec(v_a_2661_);
    crate::leanh::lean_dec(v_a_2660_);
    return v_res_2671_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(
    mut v_00_u03b2_2672_: *mut crate::leanh::LeanObject,
    mut v_x_2673_: *mut crate::leanh::LeanObject,
    mut v_x_2674_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2675_: u8 = 0;
    v___x_2675_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_x_2673_, v_x_2674_);
    return v___x_2675_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___boxed(
    mut v_00_u03b2_2676_: *mut crate::leanh::LeanObject,
    mut v_x_2677_: *mut crate::leanh::LeanObject,
    mut v_x_2678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2679_: u8 = 0;
    let mut v_r_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(v_00_u03b2_2676_, v_x_2677_, v_x_2678_);
    crate::leanh::lean_dec_ref(v_x_2678_);
    crate::leanh::lean_dec_ref(v_x_2677_);
    v_r_2680_ = crate::leanh::lean_box((v_res_2679_) as usize);
    return v_r_2680_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(
    mut v_00_u03b2_2681_: *mut crate::leanh::LeanObject,
    mut v_x_2682_: *mut crate::leanh::LeanObject,
    mut v_x_2683_: usize,
    mut v_x_2684_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2685_: u8 = 0;
    v___x_2685_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_2682_, v_x_2683_, v_x_2684_);
    return v___x_2685_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___boxed(
    mut v_00_u03b2_2686_: *mut crate::leanh::LeanObject,
    mut v_x_2687_: *mut crate::leanh::LeanObject,
    mut v_x_2688_: *mut crate::leanh::LeanObject,
    mut v_x_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_62968__boxed_2690_: usize = 0;
    let mut v_res_2691_: u8 = 0;
    let mut v_r_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_62968__boxed_2690_ = crate::leanh::lean_unbox_usize(v_x_2688_);
    crate::leanh::lean_dec(v_x_2688_);
    v_res_2691_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(v_00_u03b2_2686_, v_x_2687_, v_x_62968__boxed_2690_, v_x_2689_);
    crate::leanh::lean_dec_ref(v_x_2689_);
    crate::leanh::lean_dec_ref(v_x_2687_);
    v_r_2692_ = crate::leanh::lean_box((v_res_2691_) as usize);
    return v_r_2692_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(
    mut v_00_u03b2_2693_: *mut crate::leanh::LeanObject,
    mut v_keys_2694_: *mut crate::leanh::LeanObject,
    mut v_vals_2695_: *mut crate::leanh::LeanObject,
    mut v_heq_2696_: *mut crate::leanh::LeanObject,
    mut v_i_2697_: *mut crate::leanh::LeanObject,
    mut v_k_2698_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2699_: u8 = 0;
    v___x_2699_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_keys_2694_, v_i_2697_, v_k_2698_);
    return v___x_2699_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_2700_: *mut crate::leanh::LeanObject,
    mut v_keys_2701_: *mut crate::leanh::LeanObject,
    mut v_vals_2702_: *mut crate::leanh::LeanObject,
    mut v_heq_2703_: *mut crate::leanh::LeanObject,
    mut v_i_2704_: *mut crate::leanh::LeanObject,
    mut v_k_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2706_: u8 = 0;
    let mut v_r_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2706_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(v_00_u03b2_2700_, v_keys_2701_, v_vals_2702_, v_heq_2703_, v_i_2704_, v_k_2705_);
    crate::leanh::lean_dec_ref(v_k_2705_);
    crate::leanh::lean_dec_ref(v_vals_2702_);
    crate::leanh::lean_dec_ref(v_keys_2701_);
    v_r_2707_ = crate::leanh::lean_box((v_res_2706_) as usize);
    return v_r_2707_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_natToInt(
    mut v_a_2708_: *mut crate::leanh::LeanObject,
    mut v_a_2709_: *mut crate::leanh::LeanObject,
    mut v_a_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2726_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2731_: u8 = 0;
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_a_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_isSharedCheck_2747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
                if crate::leanh::lean_obj_tag(v___x_2720_) == 0 {
                    v_a_2721_ = crate::leanh::lean_ctor_get(v___x_2720_, 0);
                    crate::leanh::lean_inc(v_a_2721_);
                    crate::leanh::lean_dec_ref_known(v___x_2720_, 1);
                    v_fst_2722_ = crate::leanh::lean_ctor_get(v_a_2721_, 0);
                    v_snd_2723_ = crate::leanh::lean_ctor_get(v_a_2721_, 1);
                    v_isSharedCheck_2747_ = (!crate::leanh::lean_is_exclusive(v_a_2721_)) as u8;
                    if v_isSharedCheck_2747_ == 0 {
                        v___x_2725_ = v_a_2721_;
                        v_isShared_2726_ = v_isSharedCheck_2747_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2723_);
                        crate::leanh::lean_inc(v_fst_2722_);
                        crate::leanh::lean_dec(v_a_2721_);
                        v___x_2725_ = crate::leanh::lean_box(0);
                        v_isShared_2726_ = v_isSharedCheck_2747_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2720_;
                }
            }
            1 => {
                v___x_2727_ = l_Lean_Meta_Sym_shareCommon___redArg(v_fst_2722_, v_a_2714_);
                if crate::leanh::lean_obj_tag(v___x_2727_) == 0 {
                    v_a_2728_ = crate::leanh::lean_ctor_get(v___x_2727_, 0);
                    v_isSharedCheck_2738_ = (!crate::leanh::lean_is_exclusive(v___x_2727_)) as u8;
                    if v_isSharedCheck_2738_ == 0 {
                        v___x_2730_ = v___x_2727_;
                        v_isShared_2731_ = v_isSharedCheck_2738_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2728_);
                        crate::leanh::lean_dec(v___x_2727_);
                        v___x_2730_ = crate::leanh::lean_box(0);
                        v_isShared_2731_ = v_isSharedCheck_2738_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2725_);
                    crate::leanh::lean_dec(v_snd_2723_);
                    v_a_2739_ = crate::leanh::lean_ctor_get(v___x_2727_, 0);
                    v_isSharedCheck_2746_ = (!crate::leanh::lean_is_exclusive(v___x_2727_)) as u8;
                    if v_isSharedCheck_2746_ == 0 {
                        v___x_2741_ = v___x_2727_;
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2739_);
                        crate::leanh::lean_dec(v___x_2727_);
                        v___x_2741_ = crate::leanh::lean_box(0);
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2726_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2725_, 0, v_a_2728_);
                    v___x_2733_ = v___x_2725_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2737_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_snd_2723_);
                    v___x_2733_ = v_reuseFailAlloc_2737_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2731_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2733_);
                    v___x_2735_ = v___x_2730_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
                    v___x_2735_ = v_reuseFailAlloc_2736_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2735_;
            }
            5 => {
                if v_isShared_2742_ == 0 {
                    v___x_2744_ = v___x_2741_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
                    v___x_2744_ = v_reuseFailAlloc_2745_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_natToInt___boxed(
    mut v_a_2748_: *mut crate::leanh::LeanObject,
    mut v_a_2749_: *mut crate::leanh::LeanObject,
    mut v_a_2750_: *mut crate::leanh::LeanObject,
    mut v_a_2751_: *mut crate::leanh::LeanObject,
    mut v_a_2752_: *mut crate::leanh::LeanObject,
    mut v_a_2753_: *mut crate::leanh::LeanObject,
    mut v_a_2754_: *mut crate::leanh::LeanObject,
    mut v_a_2755_: *mut crate::leanh::LeanObject,
    mut v_a_2756_: *mut crate::leanh::LeanObject,
    mut v_a_2757_: *mut crate::leanh::LeanObject,
    mut v_a_2758_: *mut crate::leanh::LeanObject,
    mut v_a_2759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2760_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(
        v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_,
        v_a_2756_, v_a_2757_, v_a_2758_,
    );
    crate::leanh::lean_dec(v_a_2758_);
    crate::leanh::lean_dec_ref(v_a_2757_);
    crate::leanh::lean_dec(v_a_2756_);
    crate::leanh::lean_dec_ref(v_a_2755_);
    crate::leanh::lean_dec(v_a_2754_);
    crate::leanh::lean_dec_ref(v_a_2753_);
    crate::leanh::lean_dec(v_a_2752_);
    crate::leanh::lean_dec_ref(v_a_2751_);
    crate::leanh::lean_dec(v_a_2750_);
    crate::leanh::lean_dec(v_a_2749_);
    return v_res_2760_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2769_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2770_ = lean_nat_to_int(v___x_2769_);
    return v___x_2770_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2771_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5,
    );
    v___x_2772_ = lean_int_neg(v___x_2771_);
    return v___x_2772_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2773_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2774_ = lean_nat_to_int(v___x_2773_);
    return v___x_2774_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2775_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7,
    );
    v___x_2776_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2776_, 0, v___x_2775_);
    return v___x_2776_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(
    mut v_e_2777_: *mut crate::leanh::LeanObject,
    mut v_x_2778_: *mut crate::leanh::LeanObject,
    mut v_a_2779_: *mut crate::leanh::LeanObject,
    mut v_a_2780_: *mut crate::leanh::LeanObject,
    mut v_a_2781_: *mut crate::leanh::LeanObject,
    mut v_a_2782_: *mut crate::leanh::LeanObject,
    mut v_a_2783_: *mut crate::leanh::LeanObject,
    mut v_a_2784_: *mut crate::leanh::LeanObject,
    mut v_a_2785_: *mut crate::leanh::LeanObject,
    mut v_a_2786_: *mut crate::leanh::LeanObject,
    mut v_a_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v_arg_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut v_arg_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: u8 = 0;
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: u8 = 0;
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v_natDef_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u8 = 0;
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2828_: u8 = 0;
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2837_: u8 = 0;
    let mut v_a_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2841_: u8 = 0;
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2845_: u8 = 0;
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2793_ = l_Lean_Expr_cleanupAnnotations(v_e_2777_);
                v___x_2794_ = l_Lean_Expr_isApp(v___x_2793_);
                if v___x_2794_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2793_);
                    crate::leanh::lean_dec(v_x_2778_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2795_ = crate::leanh::lean_ctor_get(v___x_2793_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2795_);
                    v___x_2796_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2793_);
                    v___x_2797_ = l_Lean_Expr_isApp(v___x_2796_);
                    if v___x_2797_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2796_);
                        crate::leanh::lean_dec_ref(v_arg_2795_);
                        crate::leanh::lean_dec(v_x_2778_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2798_ = crate::leanh::lean_ctor_get(v___x_2796_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2798_);
                        v___x_2799_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2796_);
                        v___x_2800_ = l_Lean_Expr_isApp(v___x_2799_);
                        if v___x_2800_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2799_);
                            crate::leanh::lean_dec_ref(v_arg_2798_);
                            crate::leanh::lean_dec_ref(v_arg_2795_);
                            crate::leanh::lean_dec(v_x_2778_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2801_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2799_);
                            v___x_2802_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
                            v___x_2803_ = l_Lean_Expr_isConstOf(v___x_2801_, v___x_2802_);
                            crate::leanh::lean_dec_ref(v___x_2801_);
                            if v___x_2803_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2798_);
                                crate::leanh::lean_dec_ref(v_arg_2795_);
                                crate::leanh::lean_dec(v_x_2778_);
                                state = 1;
                                continue;
                            } else {
                                v___x_2804_ = l_Lean_Expr_cleanupAnnotations(v_arg_2798_);
                                v___x_2805_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4;
                                v___x_2806_ = l_Lean_Expr_isConstOf(v___x_2804_, v___x_2805_);
                                crate::leanh::lean_dec_ref(v___x_2804_);
                                if v___x_2806_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_2795_);
                                    crate::leanh::lean_dec(v_x_2778_);
                                    v___x_2807_ = crate::leanh::lean_box(0);
                                    v___x_2808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2808_, 0, v___x_2807_);
                                    return v___x_2808_;
                                } else {
                                    v___x_2809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5;
                                    v___x_2810_ = l_Lean_Expr_isAppOf(v_arg_2795_, v___x_2809_);
                                    if v___x_2810_ == 0 {
                                        v___x_2811_ =
                                            l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(
                                                v_a_2779_, v_a_2787_,
                                            );
                                        if crate::leanh::lean_obj_tag(v___x_2811_) == 0 {
                                            v_a_2812_ = crate::leanh::lean_ctor_get(v___x_2811_, 0);
                                            v_isSharedCheck_2837_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2811_))
                                                    as u8;
                                            if v_isSharedCheck_2837_ == 0 {
                                                v___x_2814_ = v___x_2811_;
                                                v_isShared_2815_ = v_isSharedCheck_2837_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2812_);
                                                crate::leanh::lean_dec(v___x_2811_);
                                                v___x_2814_ = crate::leanh::lean_box(0);
                                                v_isShared_2815_ = v_isSharedCheck_2837_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_arg_2795_);
                                            crate::leanh::lean_dec(v_x_2778_);
                                            v_a_2838_ = crate::leanh::lean_ctor_get(v___x_2811_, 0);
                                            v_isSharedCheck_2845_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2811_))
                                                    as u8;
                                            if v_isSharedCheck_2845_ == 0 {
                                                v___x_2840_ = v___x_2811_;
                                                v_isShared_2841_ = v_isSharedCheck_2845_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2838_);
                                                crate::leanh::lean_dec(v___x_2811_);
                                                v___x_2840_ = crate::leanh::lean_box(0);
                                                v_isShared_2841_ = v_isSharedCheck_2845_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_2795_);
                                        crate::leanh::lean_dec(v_x_2778_);
                                        v___x_2846_ = crate::leanh::lean_box(0);
                                        v___x_2847_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2847_, 0, v___x_2846_);
                                        return v___x_2847_;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2791_ = crate::leanh::lean_box(0);
                v___x_2792_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2792_, 0, v___x_2791_);
                return v___x_2792_;
            }
            2 => {
                v_natDef_2816_ = crate::leanh::lean_ctor_get(v_a_2812_, 5);
                crate::leanh::lean_inc_ref(v_natDef_2816_);
                crate::leanh::lean_dec(v_a_2812_);
                v___x_2817_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natDef_2816_, v_arg_2795_);
                crate::leanh::lean_dec_ref(v_natDef_2816_);
                if v___x_2817_ == 0 {
                    crate::leanh::lean_del_object(v___x_2814_);
                    crate::leanh::lean_inc_ref(v_arg_2795_);
                    v___x_2818_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(
                        v_arg_2795_,
                        v_a_2779_,
                        v_a_2780_,
                        v_a_2781_,
                        v_a_2782_,
                        v_a_2783_,
                        v_a_2784_,
                        v_a_2785_,
                        v_a_2786_,
                        v_a_2787_,
                        v_a_2788_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2818_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2818_, 1);
                        v___x_2819_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6,
                        );
                        v___x_2820_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8,
                        );
                        v___x_2821_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2819_);
                        crate::leanh::lean_ctor_set(v___x_2821_, 1, v_x_2778_);
                        crate::leanh::lean_ctor_set(v___x_2821_, 2, v___x_2820_);
                        v___x_2822_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2822_, 0, v_arg_2795_);
                        v___x_2823_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2823_, 0, v___x_2821_);
                        crate::leanh::lean_ctor_set(v___x_2823_, 1, v___x_2822_);
                        crate::leanh::lean_inc(v_a_2788_);
                        crate::leanh::lean_inc_ref(v_a_2787_);
                        crate::leanh::lean_inc(v_a_2786_);
                        crate::leanh::lean_inc_ref(v_a_2785_);
                        crate::leanh::lean_inc(v_a_2784_);
                        crate::leanh::lean_inc_ref(v_a_2783_);
                        crate::leanh::lean_inc(v_a_2782_);
                        crate::leanh::lean_inc_ref(v_a_2781_);
                        crate::leanh::lean_inc(v_a_2780_);
                        crate::leanh::lean_inc(v_a_2779_);
                        v___x_2824_ = lean_grind_cutsat_assert_le(
                            v___x_2823_,
                            v_a_2779_,
                            v_a_2780_,
                            v_a_2781_,
                            v_a_2782_,
                            v_a_2783_,
                            v_a_2784_,
                            v_a_2785_,
                            v_a_2786_,
                            v_a_2787_,
                            v_a_2788_,
                        );
                        return v___x_2824_;
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2795_);
                        crate::leanh::lean_dec(v_x_2778_);
                        v_a_2825_ = crate::leanh::lean_ctor_get(v___x_2818_, 0);
                        v_isSharedCheck_2832_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2818_)) as u8;
                        if v_isSharedCheck_2832_ == 0 {
                            v___x_2827_ = v___x_2818_;
                            v_isShared_2828_ = v_isSharedCheck_2832_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2825_);
                            crate::leanh::lean_dec(v___x_2818_);
                            v___x_2827_ = crate::leanh::lean_box(0);
                            v_isShared_2828_ = v_isSharedCheck_2832_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_2795_);
                    crate::leanh::lean_dec(v_x_2778_);
                    v___x_2833_ = crate::leanh::lean_box(0);
                    if v_isShared_2815_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2833_);
                        v___x_2835_ = v___x_2814_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2836_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
                        v___x_2835_ = v_reuseFailAlloc_2836_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2828_ == 0 {
                    v___x_2830_ = v___x_2827_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
                    v___x_2830_ = v_reuseFailAlloc_2831_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2830_;
            }
            5 => {
                return v___x_2835_;
            }
            6 => {
                if v_isShared_2841_ == 0 {
                    v___x_2843_ = v___x_2840_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
                    v___x_2843_ = v_reuseFailAlloc_2844_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___boxed(
    mut v_e_2848_: *mut crate::leanh::LeanObject,
    mut v_x_2849_: *mut crate::leanh::LeanObject,
    mut v_a_2850_: *mut crate::leanh::LeanObject,
    mut v_a_2851_: *mut crate::leanh::LeanObject,
    mut v_a_2852_: *mut crate::leanh::LeanObject,
    mut v_a_2853_: *mut crate::leanh::LeanObject,
    mut v_a_2854_: *mut crate::leanh::LeanObject,
    mut v_a_2855_: *mut crate::leanh::LeanObject,
    mut v_a_2856_: *mut crate::leanh::LeanObject,
    mut v_a_2857_: *mut crate::leanh::LeanObject,
    mut v_a_2858_: *mut crate::leanh::LeanObject,
    mut v_a_2859_: *mut crate::leanh::LeanObject,
    mut v_a_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2861_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(
        v_e_2848_, v_x_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_,
        v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_,
    );
    crate::leanh::lean_dec(v_a_2859_);
    crate::leanh::lean_dec_ref(v_a_2858_);
    crate::leanh::lean_dec(v_a_2857_);
    crate::leanh::lean_dec_ref(v_a_2856_);
    crate::leanh::lean_dec(v_a_2855_);
    crate::leanh::lean_dec_ref(v_a_2854_);
    crate::leanh::lean_dec(v_a_2853_);
    crate::leanh::lean_dec_ref(v_a_2852_);
    crate::leanh::lean_dec(v_a_2851_);
    crate::leanh::lean_dec(v_a_2850_);
    return v_res_2861_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(
    mut v_e_2862_: *mut crate::leanh::LeanObject,
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2870_: u8 = 0;
    let mut v_natToIntMap_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: u8 = 0;
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2877_: u8 = 0;
    let mut v_a_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2866_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2863_, v_a_2864_);
                if crate::leanh::lean_obj_tag(v___x_2866_) == 0 {
                    v_a_2867_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                    v_isSharedCheck_2877_ = (!crate::leanh::lean_is_exclusive(v___x_2866_)) as u8;
                    if v_isSharedCheck_2877_ == 0 {
                        v___x_2869_ = v___x_2866_;
                        v_isShared_2870_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2867_);
                        crate::leanh::lean_dec(v___x_2866_);
                        v___x_2869_ = crate::leanh::lean_box(0);
                        v_isShared_2870_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2878_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                    v_isSharedCheck_2885_ = (!crate::leanh::lean_is_exclusive(v___x_2866_)) as u8;
                    if v_isSharedCheck_2885_ == 0 {
                        v___x_2880_ = v___x_2866_;
                        v_isShared_2881_ = v_isSharedCheck_2885_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2878_);
                        crate::leanh::lean_dec(v___x_2866_);
                        v___x_2880_ = crate::leanh::lean_box(0);
                        v_isShared_2881_ = v_isSharedCheck_2885_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_natToIntMap_2871_ = crate::leanh::lean_ctor_get(v_a_2867_, 4);
                crate::leanh::lean_inc_ref(v_natToIntMap_2871_);
                crate::leanh::lean_dec(v_a_2867_);
                v___x_2872_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natToIntMap_2871_, v_e_2862_);
                crate::leanh::lean_dec_ref(v_natToIntMap_2871_);
                v___x_2873_ = crate::leanh::lean_box((v___x_2872_) as usize);
                if v_isShared_2870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2869_, 0, v___x_2873_);
                    v___x_2875_ = v___x_2869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
                    v___x_2875_ = v_reuseFailAlloc_2876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2875_;
            }
            3 => {
                if v_isShared_2881_ == 0 {
                    v___x_2883_ = v___x_2880_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
                    v___x_2883_ = v_reuseFailAlloc_2884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(
    mut v_e_2886_: *mut crate::leanh::LeanObject,
    mut v_a_2887_: *mut crate::leanh::LeanObject,
    mut v_a_2888_: *mut crate::leanh::LeanObject,
    mut v_a_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ =
        l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_2886_, v_a_2887_, v_a_2888_);
    crate::leanh::lean_dec_ref(v_a_2888_);
    crate::leanh::lean_dec(v_a_2887_);
    crate::leanh::lean_dec_ref(v_e_2886_);
    return v_res_2890_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(
    mut v_e_2891_: *mut crate::leanh::LeanObject,
    mut v_a_2892_: *mut crate::leanh::LeanObject,
    mut v_a_2893_: *mut crate::leanh::LeanObject,
    mut v_a_2894_: *mut crate::leanh::LeanObject,
    mut v_a_2895_: *mut crate::leanh::LeanObject,
    mut v_a_2896_: *mut crate::leanh::LeanObject,
    mut v_a_2897_: *mut crate::leanh::LeanObject,
    mut v_a_2898_: *mut crate::leanh::LeanObject,
    mut v_a_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
    mut v_a_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2903_ =
        l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_2891_, v_a_2892_, v_a_2900_);
    return v___x_2903_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(
    mut v_e_2904_: *mut crate::leanh::LeanObject,
    mut v_a_2905_: *mut crate::leanh::LeanObject,
    mut v_a_2906_: *mut crate::leanh::LeanObject,
    mut v_a_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
    mut v_a_2914_: *mut crate::leanh::LeanObject,
    mut v_a_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2916_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(
        v_e_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_,
        v_a_2912_, v_a_2913_, v_a_2914_,
    );
    crate::leanh::lean_dec(v_a_2914_);
    crate::leanh::lean_dec_ref(v_a_2913_);
    crate::leanh::lean_dec(v_a_2912_);
    crate::leanh::lean_dec_ref(v_a_2911_);
    crate::leanh::lean_dec(v_a_2910_);
    crate::leanh::lean_dec_ref(v_a_2909_);
    crate::leanh::lean_dec(v_a_2908_);
    crate::leanh::lean_dec_ref(v_a_2907_);
    crate::leanh::lean_dec(v_a_2906_);
    crate::leanh::lean_dec(v_a_2905_);
    crate::leanh::lean_dec_ref(v_e_2904_);
    return v_res_2916_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(
    mut v_e_2917_: *mut crate::leanh::LeanObject,
    mut v_a_2918_: *mut crate::leanh::LeanObject,
    mut v_a_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2935_: u8 = 0;
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: u8 = 0;
    let mut v_arg_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: u8 = 0;
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: u8 = 0;
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2953_: u8 = 0;
    let mut v_a_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: u8 = 0;
    let mut v_arg_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v_arg_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: u8 = 0;
    let mut v_arg_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: u8 = 0;
    let mut v___x_2974_: u8 = 0;
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u8 = 0;
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: u8 = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: u8 = 0;
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: u8 = 0;
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: u8 = 0;
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: u8 = 0;
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v_val_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: u8 = 0;
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut v_a_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3040_: u8 = 0;
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v_a_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3048_: u8 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2917_);
                v___x_2927_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2917_, v_a_2919_);
                if crate::leanh::lean_obj_tag(v___x_2927_) == 0 {
                    v_a_2928_ = crate::leanh::lean_ctor_get(v___x_2927_, 0);
                    crate::leanh::lean_inc(v_a_2928_);
                    crate::leanh::lean_dec_ref_known(v___x_2927_, 1);
                    v___x_2962_ = l_Lean_Expr_cleanupAnnotations(v_a_2928_);
                    v___x_2963_ = l_Lean_Expr_isApp(v___x_2962_);
                    if v___x_2963_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2962_);
                        v___y_2930_ = v_a_2919_;
                        state = 2;
                        continue;
                    } else {
                        v_arg_2964_ = crate::leanh::lean_ctor_get(v___x_2962_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2964_);
                        v___x_2965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2962_);
                        v___x_2966_ = l_Lean_Expr_isApp(v___x_2965_);
                        if v___x_2966_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2965_);
                            crate::leanh::lean_dec_ref(v_arg_2964_);
                            v___y_2930_ = v_a_2919_;
                            state = 2;
                            continue;
                        } else {
                            v_arg_2967_ = crate::leanh::lean_ctor_get(v___x_2965_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2967_);
                            v___x_2968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2965_);
                            v___x_2969_ = l_Lean_Expr_isApp(v___x_2968_);
                            if v___x_2969_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2968_);
                                crate::leanh::lean_dec_ref(v_arg_2967_);
                                crate::leanh::lean_dec_ref(v_arg_2964_);
                                v___y_2930_ = v_a_2919_;
                                state = 2;
                                continue;
                            } else {
                                v_arg_2970_ = crate::leanh::lean_ctor_get(v___x_2968_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2970_);
                                v___x_2971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2968_);
                                v___x_2972_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5;
                                v___x_2973_ = l_Lean_Expr_isConstOf(v___x_2971_, v___x_2972_);
                                if v___x_2973_ == 0 {
                                    v___x_2974_ = l_Lean_Expr_isApp(v___x_2971_);
                                    if v___x_2974_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2971_);
                                        crate::leanh::lean_dec_ref(v_arg_2970_);
                                        crate::leanh::lean_dec_ref(v_arg_2967_);
                                        crate::leanh::lean_dec_ref(v_arg_2964_);
                                        v___y_2930_ = v_a_2919_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_2975_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2971_);
                                        v___x_2976_ = l_Lean_Expr_isApp(v___x_2975_);
                                        if v___x_2976_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_2975_);
                                            crate::leanh::lean_dec_ref(v_arg_2970_);
                                            crate::leanh::lean_dec_ref(v_arg_2967_);
                                            crate::leanh::lean_dec_ref(v_arg_2964_);
                                            v___y_2930_ = v_a_2919_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_2977_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2975_);
                                            v___x_2978_ = l_Lean_Expr_isApp(v___x_2977_);
                                            if v___x_2978_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_2977_);
                                                crate::leanh::lean_dec_ref(v_arg_2970_);
                                                crate::leanh::lean_dec_ref(v_arg_2967_);
                                                crate::leanh::lean_dec_ref(v_arg_2964_);
                                                v___y_2930_ = v_a_2919_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_2979_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_2977_);
                                                v___x_2980_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8;
                                                v___x_2981_ =
                                                    l_Lean_Expr_isConstOf(v___x_2979_, v___x_2980_);
                                                if v___x_2981_ == 0 {
                                                    v___x_2982_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11;
                                                    v___x_2983_ = l_Lean_Expr_isConstOf(
                                                        v___x_2979_,
                                                        v___x_2982_,
                                                    );
                                                    if v___x_2983_ == 0 {
                                                        v___x_2984_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14;
                                                        v___x_2985_ = l_Lean_Expr_isConstOf(
                                                            v___x_2979_,
                                                            v___x_2984_,
                                                        );
                                                        if v___x_2985_ == 0 {
                                                            v___x_2986_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17;
                                                            v___x_2987_ = l_Lean_Expr_isConstOf(
                                                                v___x_2979_,
                                                                v___x_2986_,
                                                            );
                                                            if v___x_2987_ == 0 {
                                                                v___x_2988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20;
                                                                v___x_2989_ = l_Lean_Expr_isConstOf(
                                                                    v___x_2979_,
                                                                    v___x_2988_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2979_,
                                                                );
                                                                if v___x_2989_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2970_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2967_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2964_,
                                                                    );
                                                                    v___y_2930_ = v_a_2919_;
                                                                    state = 2;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_2917_,
                                                                    );
                                                                    v___x_2990_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_2970_, v_a_2919_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_2990_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_2991_ = crate::leanh::lean_ctor_get(v___x_2990_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2991_,
                                                                        );
                                                                        v___x_2992_ = (crate::leanh::lean_unbox(v_a_2991_) as u8);
                                                                        crate::leanh::lean_dec(
                                                                            v_a_2991_,
                                                                        );
                                                                        if v___x_2992_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_2967_);
                                                                            crate::leanh::lean_dec_ref(v_arg_2964_);
                                                                            return v___x_2990_;
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref_known(v___x_2990_, 1);
                                                                            v___x_2993_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_2967_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
                                                                            if crate::leanh::lean_obj_tag(v___x_2993_) == 0 {
v_a_2994_ = crate::leanh::lean_ctor_get(v___x_2993_, 0);
crate::leanh::lean_inc(v_a_2994_);
v___x_2995_ = (crate::leanh::lean_unbox(v_a_2994_) as u8);
crate::leanh::lean_dec(v_a_2994_);
if v___x_2995_ == 0 {
crate::leanh::lean_dec_ref(v_arg_2964_);
return v___x_2993_;
} else {
crate::leanh::lean_dec_ref_known(v___x_2993_, 1);
v_e_2917_ = v_arg_2964_;
state = 0; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_2964_);
return v___x_2993_;
}
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2967_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2964_,
                                                                        );
                                                                        return v___x_2990_;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2979_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_2917_,
                                                                );
                                                                v___x_2997_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_2970_, v_a_2919_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_2997_,
                                                                ) == 0
                                                                {
                                                                    v_a_2998_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_2997_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_2998_,
                                                                    );
                                                                    v___x_2999_ =
                                                                        (crate::leanh::lean_unbox(
                                                                            v_a_2998_,
                                                                        )
                                                                            as u8);
                                                                    crate::leanh::lean_dec(
                                                                        v_a_2998_,
                                                                    );
                                                                    if v___x_2999_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2967_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2964_,
                                                                        );
                                                                        return v___x_2997_;
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref_known(v___x_2997_, 1);
                                                                        v___x_3000_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_2967_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
                                                                        if crate::leanh::lean_obj_tag(v___x_3000_) == 0 {
v_a_3001_ = crate::leanh::lean_ctor_get(v___x_3000_, 0);
crate::leanh::lean_inc(v_a_3001_);
v___x_3002_ = (crate::leanh::lean_unbox(v_a_3001_) as u8);
crate::leanh::lean_dec(v_a_3001_);
if v___x_3002_ == 0 {
crate::leanh::lean_dec_ref(v_arg_2964_);
return v___x_3000_;
} else {
crate::leanh::lean_dec_ref_known(v___x_3000_, 1);
v_e_2917_ = v_arg_2964_;
state = 0; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_2964_);
return v___x_3000_;
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2967_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2964_,
                                                                    );
                                                                    return v___x_2997_;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_2979_);
                                                            crate::leanh::lean_dec_ref(v_e_2917_);
                                                            v___x_3004_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_2970_, v_a_2919_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3004_,
                                                            ) == 0
                                                            {
                                                                v_a_3005_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3004_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_3005_);
                                                                v___x_3006_ =
                                                                    (crate::leanh::lean_unbox(
                                                                        v_a_3005_,
                                                                    )
                                                                        as u8);
                                                                crate::leanh::lean_dec(v_a_3005_);
                                                                if v___x_3006_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2967_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2964_,
                                                                    );
                                                                    return v___x_3004_;
                                                                } else {
                                                                    crate::leanh::lean_dec_ref_known(v___x_3004_, 1);
                                                                    v___x_3007_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_2967_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_3007_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_3008_ = crate::leanh::lean_ctor_get(v___x_3007_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_3008_,
                                                                        );
                                                                        v___x_3009_ = (crate::leanh::lean_unbox(v_a_3008_) as u8);
                                                                        crate::leanh::lean_dec(
                                                                            v_a_3008_,
                                                                        );
                                                                        if v___x_3009_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_2964_);
                                                                            return v___x_3007_;
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref_known(v___x_3007_, 1);
                                                                            v_e_2917_ = v_arg_2964_;
                                                                            state = 0;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2964_,
                                                                        );
                                                                        return v___x_3007_;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2967_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2964_,
                                                                );
                                                                return v___x_3004_;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_2979_);
                                                        crate::leanh::lean_dec_ref(v_arg_2964_);
                                                        crate::leanh::lean_dec_ref(v_e_2917_);
                                                        v___x_3011_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_2970_, v_a_2919_);
                                                        if crate::leanh::lean_obj_tag(v___x_3011_)
                                                            == 0
                                                        {
                                                            v_a_3012_ = crate::leanh::lean_ctor_get(
                                                                v___x_3011_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_3012_);
                                                            v___x_3013_ = (crate::leanh::lean_unbox(
                                                                v_a_3012_,
                                                            )
                                                                as u8);
                                                            crate::leanh::lean_dec(v_a_3012_);
                                                            if v___x_3013_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2967_,
                                                                );
                                                                return v___x_3011_;
                                                            } else {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_3011_,
                                                                    1,
                                                                );
                                                                v_e_2917_ = v_arg_2967_;
                                                                state = 0;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_2967_);
                                                            return v___x_3011_;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_2979_);
                                                    crate::leanh::lean_dec_ref(v_arg_2964_);
                                                    crate::leanh::lean_dec_ref(v_e_2917_);
                                                    v___x_3015_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_2970_, v_a_2919_);
                                                    if crate::leanh::lean_obj_tag(v___x_3015_) == 0
                                                    {
                                                        v_a_3016_ = crate::leanh::lean_ctor_get(
                                                            v___x_3015_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_3016_);
                                                        v___x_3017_ =
                                                            (crate::leanh::lean_unbox(v_a_3016_)
                                                                as u8);
                                                        crate::leanh::lean_dec(v_a_3016_);
                                                        if v___x_3017_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_arg_2967_);
                                                            return v___x_3015_;
                                                        } else {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_3015_,
                                                                1,
                                                            );
                                                            v_e_2917_ = v_arg_2967_;
                                                            state = 0;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_arg_2967_);
                                                        return v___x_3015_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2971_);
                                    crate::leanh::lean_dec_ref(v_arg_2970_);
                                    crate::leanh::lean_dec_ref(v_arg_2967_);
                                    crate::leanh::lean_dec_ref(v_arg_2964_);
                                    v___x_3019_ = l_Lean_Meta_getIntValue_x3f(
                                        v_e_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3019_) == 0 {
                                        v_a_3020_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                                        v_isSharedCheck_3036_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3019_)) as u8;
                                        if v_isSharedCheck_3036_ == 0 {
                                            v___x_3022_ = v___x_3019_;
                                            v_isShared_3023_ = v_isSharedCheck_3036_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3020_);
                                            crate::leanh::lean_dec(v___x_3019_);
                                            v___x_3022_ = crate::leanh::lean_box(0);
                                            v_isShared_3023_ = v_isSharedCheck_3036_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_a_3037_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                                        v_isSharedCheck_3044_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3019_)) as u8;
                                        if v_isSharedCheck_3044_ == 0 {
                                            v___x_3039_ = v___x_3019_;
                                            v_isShared_3040_ = v_isSharedCheck_3044_;
                                            state = 10;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3037_);
                                            crate::leanh::lean_dec(v___x_3019_);
                                            v___x_3039_ = crate::leanh::lean_box(0);
                                            v_isShared_3040_ = v_isSharedCheck_3044_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2917_);
                    v_a_3045_ = crate::leanh::lean_ctor_get(v___x_2927_, 0);
                    v_isSharedCheck_3052_ = (!crate::leanh::lean_is_exclusive(v___x_2927_)) as u8;
                    if v_isSharedCheck_3052_ == 0 {
                        v___x_3047_ = v___x_2927_;
                        v_isShared_3048_ = v_isSharedCheck_3052_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3045_);
                        crate::leanh::lean_dec(v___x_2927_);
                        v___x_3047_ = crate::leanh::lean_box(0);
                        v_isShared_3048_ = v_isSharedCheck_3052_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2924_ = 0;
                v___x_2925_ = crate::leanh::lean_box((v___x_2924_) as usize);
                v___x_2926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2926_, 0, v___x_2925_);
                return v___x_2926_;
            }
            2 => {
                v___x_2931_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2917_, v___y_2930_);
                if crate::leanh::lean_obj_tag(v___x_2931_) == 0 {
                    v_a_2932_ = crate::leanh::lean_ctor_get(v___x_2931_, 0);
                    v_isSharedCheck_2953_ = (!crate::leanh::lean_is_exclusive(v___x_2931_)) as u8;
                    if v_isSharedCheck_2953_ == 0 {
                        v___x_2934_ = v___x_2931_;
                        v_isShared_2935_ = v_isSharedCheck_2953_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2932_);
                        crate::leanh::lean_dec(v___x_2931_);
                        v___x_2934_ = crate::leanh::lean_box(0);
                        v_isShared_2935_ = v_isSharedCheck_2953_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2954_ = crate::leanh::lean_ctor_get(v___x_2931_, 0);
                    v_isSharedCheck_2961_ = (!crate::leanh::lean_is_exclusive(v___x_2931_)) as u8;
                    if v_isSharedCheck_2961_ == 0 {
                        v___x_2956_ = v___x_2931_;
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2954_);
                        crate::leanh::lean_dec(v___x_2931_);
                        v___x_2956_ = crate::leanh::lean_box(0);
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2936_ = l_Lean_Expr_cleanupAnnotations(v_a_2932_);
                v___x_2937_ = l_Lean_Expr_isApp(v___x_2936_);
                if v___x_2937_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2936_);
                    crate::leanh::lean_del_object(v___x_2934_);
                    state = 1;
                    continue;
                } else {
                    v___x_2938_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2936_);
                    v___x_2939_ = l_Lean_Expr_isApp(v___x_2938_);
                    if v___x_2939_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2938_);
                        crate::leanh::lean_del_object(v___x_2934_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2940_ = crate::leanh::lean_ctor_get(v___x_2938_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2940_);
                        v___x_2941_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2938_);
                        v___x_2942_ = l_Lean_Expr_isApp(v___x_2941_);
                        if v___x_2942_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2941_);
                            crate::leanh::lean_dec_ref(v_arg_2940_);
                            crate::leanh::lean_del_object(v___x_2934_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2943_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2941_);
                            v___x_2944_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
                            v___x_2945_ = l_Lean_Expr_isConstOf(v___x_2943_, v___x_2944_);
                            crate::leanh::lean_dec_ref(v___x_2943_);
                            if v___x_2945_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2940_);
                                crate::leanh::lean_del_object(v___x_2934_);
                                state = 1;
                                continue;
                            } else {
                                v___x_2946_ = l_Lean_Expr_cleanupAnnotations(v_arg_2940_);
                                v___x_2947_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4;
                                v___x_2948_ = l_Lean_Expr_isConstOf(v___x_2946_, v___x_2947_);
                                crate::leanh::lean_dec_ref(v___x_2946_);
                                v___x_2949_ = crate::leanh::lean_box((v___x_2948_) as usize);
                                if v_isShared_2935_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2934_, 0, v___x_2949_);
                                    v___x_2951_ = v___x_2934_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2952_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2952_,
                                        0,
                                        v___x_2949_,
                                    );
                                    v___x_2951_ = v_reuseFailAlloc_2952_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                return v___x_2951_;
            }
            5 => {
                if v_isShared_2957_ == 0 {
                    v___x_2959_ = v___x_2956_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
                    v___x_2959_ = v_reuseFailAlloc_2960_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2959_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_3020_) == 1 {
                    v_val_3024_ = crate::leanh::lean_ctor_get(v_a_3020_, 0);
                    crate::leanh::lean_inc(v_val_3024_);
                    crate::leanh::lean_dec_ref_known(v_a_3020_, 1);
                    v___x_3025_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7,
                    );
                    v___x_3026_ = lean_int_dec_le(v___x_3025_, v_val_3024_);
                    crate::leanh::lean_dec(v_val_3024_);
                    v___x_3027_ = crate::leanh::lean_box((v___x_3026_) as usize);
                    if v_isShared_3023_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3022_, 0, v___x_3027_);
                        v___x_3029_ = v___x_3022_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3030_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
                        v___x_3029_ = v_reuseFailAlloc_3030_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3020_);
                    v___x_3031_ = 0;
                    v___x_3032_ = crate::leanh::lean_box((v___x_3031_) as usize);
                    if v_isShared_3023_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3022_, 0, v___x_3032_);
                        v___x_3034_ = v___x_3022_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
                        v___x_3034_ = v_reuseFailAlloc_3035_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_3029_;
            }
            9 => {
                return v___x_3034_;
            }
            10 => {
                if v_isShared_3040_ == 0 {
                    v___x_3042_ = v___x_3039_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
                    v___x_3042_ = v_reuseFailAlloc_3043_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3042_;
            }
            12 => {
                if v_isShared_3048_ == 0 {
                    v___x_3050_ = v___x_3047_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
                    v___x_3050_ = v_reuseFailAlloc_3051_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg___boxed(
    mut v_e_3053_: *mut crate::leanh::LeanObject,
    mut v_a_3054_: *mut crate::leanh::LeanObject,
    mut v_a_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_a_3057_: *mut crate::leanh::LeanObject,
    mut v_a_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
    crate::leanh::lean_dec(v_a_3057_);
    crate::leanh::lean_dec_ref(v_a_3056_);
    crate::leanh::lean_dec(v_a_3055_);
    crate::leanh::lean_dec_ref(v_a_3054_);
    return v_res_3059_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(
    mut v_msg_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805__overap_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3067_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0;
    v___x_5805__overap_3068_ = lean_panic_fn_borrowed(v___f_3067_, v_msg_3061_);
    crate::leanh::lean_inc(v___y_3065_);
    crate::leanh::lean_inc_ref(v___y_3064_);
    crate::leanh::lean_inc(v___y_3063_);
    crate::leanh::lean_inc_ref(v___y_3062_);
    v___x_3069_ = crate::leanh::lean_apply_5(
        v___x_5805__overap_3068_,
        v___y_3062_,
        v___y_3063_,
        v___y_3064_,
        v___y_3065_,
        crate::leanh::lean_box(0),
    );
    return v___x_3069_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___boxed(
    mut v_msg_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
    mut v___y_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3076_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v_msg_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
    crate::leanh::lean_dec(v___y_3074_);
    crate::leanh::lean_dec_ref(v___y_3073_);
    crate::leanh::lean_dec(v___y_3072_);
    crate::leanh::lean_dec_ref(v___y_3071_);
    return v_res_3076_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3080_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2;
    v___x_3081_ = crate::leanh::lean_unsigned_to_nat(43);
    v___x_3082_ = crate::leanh::lean_unsigned_to_nat(154);
    v___x_3083_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1;
    v___x_3084_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0;
    v___x_3085_ = l_mkPanicMessageWithDecl(
        v___x_3084_,
        v___x_3083_,
        v___x_3082_,
        v___x_3081_,
        v___x_3080_,
    );
    return v___x_3085_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3092_ = crate::leanh::lean_box(0);
    v___x_3093_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6;
    v___x_3094_ = l_Lean_mkConst(v___x_3093_, v___x_3092_);
    return v___x_3094_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3100_ = crate::leanh::lean_box(0);
    v___x_3101_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9;
    v___x_3102_ = l_Lean_mkConst(v___x_3101_, v___x_3100_);
    return v___x_3102_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3108_ = crate::leanh::lean_box(0);
    v___x_3109_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12;
    v___x_3110_ = l_Lean_mkConst(v___x_3109_, v___x_3108_);
    return v___x_3110_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ = crate::leanh::lean_box(0);
    v___x_3117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15;
    v___x_3118_ = l_Lean_mkConst(v___x_3117_, v___x_3116_);
    return v___x_3118_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3124_ = crate::leanh::lean_box(0);
    v___x_3125_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18;
    v___x_3126_ = l_Lean_mkConst(v___x_3125_, v___x_3124_);
    return v___x_3126_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = crate::leanh::lean_box(0);
    v___x_3133_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21;
    v___x_3134_ = l_Lean_mkConst(v___x_3133_, v___x_3132_);
    return v___x_3134_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3140_ = crate::leanh::lean_box(0);
    v___x_3141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24;
    v___x_3142_ = l_Lean_mkConst(v___x_3141_, v___x_3140_);
    return v___x_3142_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(
    mut v_e_3143_: *mut crate::leanh::LeanObject,
    mut v_a_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_a_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___y_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    let mut v_arg_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: u8 = 0;
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: u8 = 0;
    let mut v_arg_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    let mut v_arg_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: u8 = 0;
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: u8 = 0;
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: u8 = 0;
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3246_: u8 = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3257_: u8 = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3274_: u8 = 0;
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3143_);
                v___x_3156_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3143_, v_a_3145_);
                if crate::leanh::lean_obj_tag(v___x_3156_) == 0 {
                    v_a_3157_ = crate::leanh::lean_ctor_get(v___x_3156_, 0);
                    v_isSharedCheck_3281_ = (!crate::leanh::lean_is_exclusive(v___x_3156_)) as u8;
                    if v_isSharedCheck_3281_ == 0 {
                        v___x_3159_ = v___x_3156_;
                        v_isShared_3160_ = v_isSharedCheck_3281_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3157_);
                        crate::leanh::lean_dec(v___x_3156_);
                        v___x_3159_ = crate::leanh::lean_box(0);
                        v_isShared_3160_ = v_isSharedCheck_3281_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3143_);
                    return v___x_3156_;
                }
            }
            1 => {
                v___x_3154_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3);
                v___x_3155_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v___x_3154_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
                return v___x_3155_;
            }
            2 => {
                v___x_3187_ = l_Lean_Expr_cleanupAnnotations(v_a_3157_);
                v___x_3188_ = l_Lean_Expr_isApp(v___x_3187_);
                if v___x_3188_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3187_);
                    crate::leanh::lean_del_object(v___x_3159_);
                    v___y_3162_ = v_a_3144_;
                    v___y_3163_ = v_a_3145_;
                    v___y_3164_ = v_a_3146_;
                    v___y_3165_ = v_a_3147_;
                    state = 3;
                    continue;
                } else {
                    v_arg_3189_ = crate::leanh::lean_ctor_get(v___x_3187_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3189_);
                    v___x_3190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3187_);
                    v___x_3191_ = l_Lean_Expr_isApp(v___x_3190_);
                    if v___x_3191_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3190_);
                        crate::leanh::lean_dec_ref(v_arg_3189_);
                        crate::leanh::lean_del_object(v___x_3159_);
                        v___y_3162_ = v_a_3144_;
                        v___y_3163_ = v_a_3145_;
                        v___y_3164_ = v_a_3146_;
                        v___y_3165_ = v_a_3147_;
                        state = 3;
                        continue;
                    } else {
                        v_arg_3192_ = crate::leanh::lean_ctor_get(v___x_3190_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3192_);
                        v___x_3193_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3190_);
                        v___x_3194_ = l_Lean_Expr_isApp(v___x_3193_);
                        if v___x_3194_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3193_);
                            crate::leanh::lean_dec_ref(v_arg_3192_);
                            crate::leanh::lean_dec_ref(v_arg_3189_);
                            crate::leanh::lean_del_object(v___x_3159_);
                            v___y_3162_ = v_a_3144_;
                            v___y_3163_ = v_a_3145_;
                            v___y_3164_ = v_a_3146_;
                            v___y_3165_ = v_a_3147_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3195_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3193_);
                            v___x_3196_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5;
                            v___x_3197_ = l_Lean_Expr_isConstOf(v___x_3195_, v___x_3196_);
                            if v___x_3197_ == 0 {
                                crate::leanh::lean_del_object(v___x_3159_);
                                v___x_3198_ = l_Lean_Expr_isApp(v___x_3195_);
                                if v___x_3198_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_3195_);
                                    crate::leanh::lean_dec_ref(v_arg_3192_);
                                    crate::leanh::lean_dec_ref(v_arg_3189_);
                                    v___y_3162_ = v_a_3144_;
                                    v___y_3163_ = v_a_3145_;
                                    v___y_3164_ = v_a_3146_;
                                    v___y_3165_ = v_a_3147_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3199_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3195_);
                                    v___x_3200_ = l_Lean_Expr_isApp(v___x_3199_);
                                    if v___x_3200_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_3199_);
                                        crate::leanh::lean_dec_ref(v_arg_3192_);
                                        crate::leanh::lean_dec_ref(v_arg_3189_);
                                        v___y_3162_ = v_a_3144_;
                                        v___y_3163_ = v_a_3145_;
                                        v___y_3164_ = v_a_3146_;
                                        v___y_3165_ = v_a_3147_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3201_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3199_);
                                        v___x_3202_ = l_Lean_Expr_isApp(v___x_3201_);
                                        if v___x_3202_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_3201_);
                                            crate::leanh::lean_dec_ref(v_arg_3192_);
                                            crate::leanh::lean_dec_ref(v_arg_3189_);
                                            v___y_3162_ = v_a_3144_;
                                            v___y_3163_ = v_a_3145_;
                                            v___y_3164_ = v_a_3146_;
                                            v___y_3165_ = v_a_3147_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_3203_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3201_);
                                            v___x_3204_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8;
                                            v___x_3205_ =
                                                l_Lean_Expr_isConstOf(v___x_3203_, v___x_3204_);
                                            if v___x_3205_ == 0 {
                                                v___x_3206_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11;
                                                v___x_3207_ =
                                                    l_Lean_Expr_isConstOf(v___x_3203_, v___x_3206_);
                                                if v___x_3207_ == 0 {
                                                    v___x_3208_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14;
                                                    v___x_3209_ = l_Lean_Expr_isConstOf(
                                                        v___x_3203_,
                                                        v___x_3208_,
                                                    );
                                                    if v___x_3209_ == 0 {
                                                        v___x_3210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17;
                                                        v___x_3211_ = l_Lean_Expr_isConstOf(
                                                            v___x_3203_,
                                                            v___x_3210_,
                                                        );
                                                        if v___x_3211_ == 0 {
                                                            v___x_3212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20;
                                                            v___x_3213_ = l_Lean_Expr_isConstOf(
                                                                v___x_3203_,
                                                                v___x_3212_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v___x_3203_);
                                                            if v___x_3213_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3192_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3189_,
                                                                );
                                                                v___y_3162_ = v_a_3144_;
                                                                v___y_3163_ = v_a_3145_;
                                                                v___y_3164_ = v_a_3146_;
                                                                v___y_3165_ = v_a_3147_;
                                                                state = 3;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_3143_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_arg_3192_,
                                                                );
                                                                v___x_3214_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_3192_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_3214_,
                                                                ) == 0
                                                                {
                                                                    v_a_3215_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3214_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_3215_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_3214_, 1);
                                                                    crate::leanh::lean_inc_ref(
                                                                        v_arg_3189_,
                                                                    );
                                                                    v___x_3216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_3189_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_3216_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_3217_ = crate::leanh::lean_ctor_get(v___x_3216_, 0);
                                                                        v_isSharedCheck_3226_ = (!crate::leanh::lean_is_exclusive(v___x_3216_)) as u8;
                                                                        if v_isSharedCheck_3226_
                                                                            == 0
                                                                        {
                                                                            v___x_3219_ =
                                                                                v___x_3216_;
                                                                            v_isShared_3220_ = v_isSharedCheck_3226_;
                                                                            state = 6;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_3217_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_3216_,
                                                                            );
                                                                            v___x_3219_ = crate::leanh::lean_box(0);
                                                                            v_isShared_3220_ = v_isSharedCheck_3226_;
                                                                            state = 6;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_3215_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3192_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_3189_,
                                                                        );
                                                                        return v___x_3216_;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3192_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3189_,
                                                                    );
                                                                    return v___x_3214_;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_3203_);
                                                            crate::leanh::lean_dec_ref(v_e_3143_);
                                                            crate::leanh::lean_inc_ref(v_arg_3192_);
                                                            v___x_3227_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_3192_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3227_,
                                                            ) == 0
                                                            {
                                                                v_a_3228_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3227_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_3228_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_3227_,
                                                                    1,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_arg_3189_,
                                                                );
                                                                v___x_3229_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_3189_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_3229_,
                                                                ) == 0
                                                                {
                                                                    v_a_3230_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3229_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3239_ = (!crate::leanh::lean_is_exclusive(v___x_3229_)) as u8;
                                                                    if v_isSharedCheck_3239_ == 0 {
                                                                        v___x_3232_ = v___x_3229_;
                                                                        v_isShared_3233_ =
                                                                            v_isSharedCheck_3239_;
                                                                        state = 8;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_3230_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_3229_,
                                                                        );
                                                                        v___x_3232_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3233_ =
                                                                            v_isSharedCheck_3239_;
                                                                        state = 8;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_a_3228_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3192_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_3189_,
                                                                    );
                                                                    return v___x_3229_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3192_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3189_,
                                                                );
                                                                return v___x_3227_;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_3203_);
                                                        crate::leanh::lean_dec_ref(v_e_3143_);
                                                        crate::leanh::lean_inc_ref(v_arg_3192_);
                                                        v___x_3240_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_3192_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                                                        if crate::leanh::lean_obj_tag(v___x_3240_)
                                                            == 0
                                                        {
                                                            v_a_3241_ = crate::leanh::lean_ctor_get(
                                                                v___x_3240_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_3241_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_3240_,
                                                                1,
                                                            );
                                                            crate::leanh::lean_inc_ref(v_arg_3189_);
                                                            v___x_3242_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_3189_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3242_,
                                                            ) == 0
                                                            {
                                                                v_a_3243_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3242_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3252_ = (!crate::leanh::lean_is_exclusive(v___x_3242_)) as u8;
                                                                if v_isSharedCheck_3252_ == 0 {
                                                                    v___x_3245_ = v___x_3242_;
                                                                    v_isShared_3246_ =
                                                                        v_isSharedCheck_3252_;
                                                                    state = 10;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_3243_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3242_,
                                                                    );
                                                                    v___x_3245_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3246_ =
                                                                        v_isSharedCheck_3252_;
                                                                    state = 10;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_3241_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3192_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3189_,
                                                                );
                                                                return v___x_3242_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_3192_);
                                                            crate::leanh::lean_dec_ref(v_arg_3189_);
                                                            return v___x_3240_;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_3203_);
                                                    crate::leanh::lean_dec_ref(v_e_3143_);
                                                    crate::leanh::lean_inc_ref(v_arg_3192_);
                                                    v___x_3253_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_3192_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                                                    if crate::leanh::lean_obj_tag(v___x_3253_) == 0
                                                    {
                                                        v_a_3254_ = crate::leanh::lean_ctor_get(
                                                            v___x_3253_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3263_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_3253_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3263_ == 0 {
                                                            v___x_3256_ = v___x_3253_;
                                                            v_isShared_3257_ =
                                                                v_isSharedCheck_3263_;
                                                            state = 12;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_3254_);
                                                            crate::leanh::lean_dec(v___x_3253_);
                                                            v___x_3256_ = crate::leanh::lean_box(0);
                                                            v_isShared_3257_ =
                                                                v_isSharedCheck_3263_;
                                                            state = 12;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_arg_3192_);
                                                        crate::leanh::lean_dec_ref(v_arg_3189_);
                                                        return v___x_3253_;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3203_);
                                                crate::leanh::lean_dec_ref(v_e_3143_);
                                                crate::leanh::lean_inc_ref(v_arg_3192_);
                                                v___x_3264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_3192_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                                                if crate::leanh::lean_obj_tag(v___x_3264_) == 0 {
                                                    v_a_3265_ =
                                                        crate::leanh::lean_ctor_get(v___x_3264_, 0);
                                                    v_isSharedCheck_3274_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_3264_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3274_ == 0 {
                                                        v___x_3267_ = v___x_3264_;
                                                        v_isShared_3268_ = v_isSharedCheck_3274_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_3265_);
                                                        crate::leanh::lean_dec(v___x_3264_);
                                                        v___x_3267_ = crate::leanh::lean_box(0);
                                                        v_isShared_3268_ = v_isSharedCheck_3274_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_arg_3192_);
                                                    crate::leanh::lean_dec_ref(v_arg_3189_);
                                                    return v___x_3264_;
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3195_);
                                crate::leanh::lean_dec_ref(v_arg_3192_);
                                crate::leanh::lean_dec_ref(v_arg_3189_);
                                v___x_3275_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25);
                                v___x_3276_ = l_Lean_eagerReflBoolTrue;
                                v___x_3277_ = l_Lean_mkAppB(v___x_3275_, v_e_3143_, v___x_3276_);
                                if v_isShared_3160_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3159_, 0, v___x_3277_);
                                    v___x_3279_ = v___x_3159_;
                                    state = 16;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3280_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3280_,
                                        0,
                                        v___x_3277_,
                                    );
                                    v___x_3279_ = v_reuseFailAlloc_3280_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_3166_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3143_, v___y_3163_);
                if crate::leanh::lean_obj_tag(v___x_3166_) == 0 {
                    v_a_3167_ = crate::leanh::lean_ctor_get(v___x_3166_, 0);
                    v_isSharedCheck_3186_ = (!crate::leanh::lean_is_exclusive(v___x_3166_)) as u8;
                    if v_isSharedCheck_3186_ == 0 {
                        v___x_3169_ = v___x_3166_;
                        v_isShared_3170_ = v_isSharedCheck_3186_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3167_);
                        crate::leanh::lean_dec(v___x_3166_);
                        v___x_3169_ = crate::leanh::lean_box(0);
                        v_isShared_3170_ = v_isSharedCheck_3186_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___x_3166_;
                }
            }
            4 => {
                v___x_3171_ = l_Lean_Expr_cleanupAnnotations(v_a_3167_);
                v___x_3172_ = l_Lean_Expr_isApp(v___x_3171_);
                if v___x_3172_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3171_);
                    crate::leanh::lean_del_object(v___x_3169_);
                    v___y_3150_ = v___y_3162_;
                    v___y_3151_ = v___y_3163_;
                    v___y_3152_ = v___y_3164_;
                    v___y_3153_ = v___y_3165_;
                    state = 1;
                    continue;
                } else {
                    v_arg_3173_ = crate::leanh::lean_ctor_get(v___x_3171_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3173_);
                    v___x_3174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3171_);
                    v___x_3175_ = l_Lean_Expr_isApp(v___x_3174_);
                    if v___x_3175_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3174_);
                        crate::leanh::lean_dec_ref(v_arg_3173_);
                        crate::leanh::lean_del_object(v___x_3169_);
                        v___y_3150_ = v___y_3162_;
                        v___y_3151_ = v___y_3163_;
                        v___y_3152_ = v___y_3164_;
                        v___y_3153_ = v___y_3165_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3174_);
                        v___x_3177_ = l_Lean_Expr_isApp(v___x_3176_);
                        if v___x_3177_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3176_);
                            crate::leanh::lean_dec_ref(v_arg_3173_);
                            crate::leanh::lean_del_object(v___x_3169_);
                            v___y_3150_ = v___y_3162_;
                            v___y_3151_ = v___y_3163_;
                            v___y_3152_ = v___y_3164_;
                            v___y_3153_ = v___y_3165_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3178_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3176_);
                            v___x_3179_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
                            v___x_3180_ = l_Lean_Expr_isConstOf(v___x_3178_, v___x_3179_);
                            crate::leanh::lean_dec_ref(v___x_3178_);
                            if v___x_3180_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_3173_);
                                crate::leanh::lean_del_object(v___x_3169_);
                                v___y_3150_ = v___y_3162_;
                                v___y_3151_ = v___y_3163_;
                                v___y_3152_ = v___y_3164_;
                                v___y_3153_ = v___y_3165_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3181_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7);
                                v___x_3182_ = l_Lean_Expr_app___override(v___x_3181_, v_arg_3173_);
                                if v_isShared_3170_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3169_, 0, v___x_3182_);
                                    v___x_3184_ = v___x_3169_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3185_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3185_,
                                        0,
                                        v___x_3182_,
                                    );
                                    v___x_3184_ = v_reuseFailAlloc_3185_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            5 => {
                return v___x_3184_;
            }
            6 => {
                v___x_3221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10);
                v___x_3222_ =
                    l_Lean_mkApp4(v___x_3221_, v_arg_3192_, v_arg_3189_, v_a_3215_, v_a_3217_);
                if v_isShared_3220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3219_, 0, v___x_3222_);
                    v___x_3224_ = v___x_3219_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
                    v___x_3224_ = v_reuseFailAlloc_3225_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3224_;
            }
            8 => {
                v___x_3234_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13);
                v___x_3235_ =
                    l_Lean_mkApp4(v___x_3234_, v_arg_3192_, v_arg_3189_, v_a_3228_, v_a_3230_);
                if v_isShared_3233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3232_, 0, v___x_3235_);
                    v___x_3237_ = v___x_3232_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
                    v___x_3237_ = v_reuseFailAlloc_3238_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3237_;
            }
            10 => {
                v___x_3247_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16);
                v___x_3248_ =
                    l_Lean_mkApp4(v___x_3247_, v_arg_3192_, v_arg_3189_, v_a_3241_, v_a_3243_);
                if v_isShared_3246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3245_, 0, v___x_3248_);
                    v___x_3250_ = v___x_3245_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3250_;
            }
            12 => {
                v___x_3258_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19);
                v___x_3259_ = l_Lean_mkApp3(v___x_3258_, v_arg_3192_, v_arg_3189_, v_a_3254_);
                if v_isShared_3257_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3256_, 0, v___x_3259_);
                    v___x_3261_ = v___x_3256_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3261_;
            }
            14 => {
                v___x_3269_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22);
                v___x_3270_ = l_Lean_mkApp3(v___x_3269_, v_arg_3192_, v_arg_3189_, v_a_3265_);
                if v_isShared_3268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3267_, 0, v___x_3270_);
                    v___x_3272_ = v___x_3267_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
                    v___x_3272_ = v_reuseFailAlloc_3273_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3272_;
            }
            16 => {
                return v___x_3279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___boxed(
    mut v_e_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_3284_: *mut crate::leanh::LeanObject,
    mut v_a_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
    mut v_a_3287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3288_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
    crate::leanh::lean_dec(v_a_3286_);
    crate::leanh::lean_dec_ref(v_a_3285_);
    crate::leanh::lean_dec(v_a_3284_);
    crate::leanh::lean_dec_ref(v_a_3283_);
    return v_res_3288_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(
    mut v_e_3289_: *mut crate::leanh::LeanObject,
    mut v_a_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
    mut v_a_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3300_: u8 = 0;
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3309_: u8 = 0;
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3314_: u8 = 0;
    let mut v_a_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3318_: u8 = 0;
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut v_isSharedCheck_3323_: u8 = 0;
    let mut v_a_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3289_);
                v___x_3295_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
                if crate::leanh::lean_obj_tag(v___x_3295_) == 0 {
                    v_a_3296_ = crate::leanh::lean_ctor_get(v___x_3295_, 0);
                    v_isSharedCheck_3323_ = (!crate::leanh::lean_is_exclusive(v___x_3295_)) as u8;
                    if v_isSharedCheck_3323_ == 0 {
                        v___x_3298_ = v___x_3295_;
                        v_isShared_3299_ = v_isSharedCheck_3323_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3296_);
                        crate::leanh::lean_dec(v___x_3295_);
                        v___x_3298_ = crate::leanh::lean_box(0);
                        v_isShared_3299_ = v_isSharedCheck_3323_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3289_);
                    v_a_3324_ = crate::leanh::lean_ctor_get(v___x_3295_, 0);
                    v_isSharedCheck_3331_ = (!crate::leanh::lean_is_exclusive(v___x_3295_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v___x_3326_ = v___x_3295_;
                        v_isShared_3327_ = v_isSharedCheck_3331_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3324_);
                        crate::leanh::lean_dec(v___x_3295_);
                        v___x_3326_ = crate::leanh::lean_box(0);
                        v_isShared_3327_ = v_isSharedCheck_3331_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3300_ = (crate::leanh::lean_unbox(v_a_3296_) as u8);
                crate::leanh::lean_dec(v_a_3296_);
                if v___x_3300_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3289_);
                    v___x_3301_ = crate::leanh::lean_box(0);
                    if v_isShared_3299_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3298_, 0, v___x_3301_);
                        v___x_3303_ = v___x_3298_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
                        v___x_3303_ = v_reuseFailAlloc_3304_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3298_);
                    v___x_3305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
                    if crate::leanh::lean_obj_tag(v___x_3305_) == 0 {
                        v_a_3306_ = crate::leanh::lean_ctor_get(v___x_3305_, 0);
                        v_isSharedCheck_3314_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3305_)) as u8;
                        if v_isSharedCheck_3314_ == 0 {
                            v___x_3308_ = v___x_3305_;
                            v_isShared_3309_ = v_isSharedCheck_3314_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3306_);
                            crate::leanh::lean_dec(v___x_3305_);
                            v___x_3308_ = crate::leanh::lean_box(0);
                            v_isShared_3309_ = v_isSharedCheck_3314_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3315_ = crate::leanh::lean_ctor_get(v___x_3305_, 0);
                        v_isSharedCheck_3322_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3305_)) as u8;
                        if v_isSharedCheck_3322_ == 0 {
                            v___x_3317_ = v___x_3305_;
                            v_isShared_3318_ = v_isSharedCheck_3322_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3315_);
                            crate::leanh::lean_dec(v___x_3305_);
                            v___x_3317_ = crate::leanh::lean_box(0);
                            v_isShared_3318_ = v_isSharedCheck_3322_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3303_;
            }
            3 => {
                v___x_3310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3310_, 0, v_a_3306_);
                if v_isShared_3309_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3308_, 0, v___x_3310_);
                    v___x_3312_ = v___x_3308_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
                    v___x_3312_ = v_reuseFailAlloc_3313_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3312_;
            }
            5 => {
                if v_isShared_3318_ == 0 {
                    v___x_3320_ = v___x_3317_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3321_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
                    v___x_3320_ = v_reuseFailAlloc_3321_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3320_;
            }
            7 => {
                if v_isShared_3327_ == 0 {
                    v___x_3329_ = v___x_3326_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
                    v___x_3329_ = v_reuseFailAlloc_3330_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg___boxed(
    mut v_e_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3338_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(
        v_e_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_,
    );
    crate::leanh::lean_dec(v_a_3336_);
    crate::leanh::lean_dec_ref(v_a_3335_);
    crate::leanh::lean_dec(v_a_3334_);
    crate::leanh::lean_dec_ref(v_a_3333_);
    return v_res_3338_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(
    mut v_e_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(
        v_e_3339_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_,
    );
    return v___x_3351_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___boxed(
    mut v_e_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3364_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(
        v_e_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_,
        v_a_3360_, v_a_3361_, v_a_3362_,
    );
    crate::leanh::lean_dec(v_a_3362_);
    crate::leanh::lean_dec_ref(v_a_3361_);
    crate::leanh::lean_dec(v_a_3360_);
    crate::leanh::lean_dec_ref(v_a_3359_);
    crate::leanh::lean_dec(v_a_3358_);
    crate::leanh::lean_dec_ref(v_a_3357_);
    crate::leanh::lean_dec(v_a_3356_);
    crate::leanh::lean_dec_ref(v_a_3355_);
    crate::leanh::lean_dec(v_a_3354_);
    crate::leanh::lean_dec(v_a_3353_);
    return v_res_3364_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3370_ = crate::leanh::lean_box(0);
    v___x_3371_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1;
    v___x_3372_ = l_Lean_mkConst(v___x_3371_, v___x_3370_);
    return v___x_3372_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(
    mut v_e_3373_: *mut crate::leanh::LeanObject,
    mut v_x_3374_: *mut crate::leanh::LeanObject,
    mut v_a_3375_: *mut crate::leanh::LeanObject,
    mut v_a_3376_: *mut crate::leanh::LeanObject,
    mut v_a_3377_: *mut crate::leanh::LeanObject,
    mut v_a_3378_: *mut crate::leanh::LeanObject,
    mut v_a_3379_: *mut crate::leanh::LeanObject,
    mut v_a_3380_: *mut crate::leanh::LeanObject,
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_a_3382_: *mut crate::leanh::LeanObject,
    mut v_a_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: u8 = 0;
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3394_: u8 = 0;
    let mut v_val_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3398_: u8 = 0;
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3409_: u8 = 0;
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut v_a_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3418_: u8 = 0;
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3422_: u8 = 0;
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3386_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
                v___x_3387_ = l_Lean_Expr_isAppOf(v_e_3373_, v___x_3386_);
                if v___x_3387_ == 0 {
                    v___x_3388_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5;
                    v___x_3389_ = l_Lean_Expr_isAppOf(v_e_3373_, v___x_3388_);
                    if v___x_3389_ == 0 {
                        crate::leanh::lean_inc_ref(v_e_3373_);
                        v___x_3390_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(
                            v_e_3373_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3390_) == 0 {
                            v_a_3391_ = crate::leanh::lean_ctor_get(v___x_3390_, 0);
                            v_isSharedCheck_3414_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3390_)) as u8;
                            if v_isSharedCheck_3414_ == 0 {
                                v___x_3393_ = v___x_3390_;
                                v_isShared_3394_ = v_isSharedCheck_3414_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3391_);
                                crate::leanh::lean_dec(v___x_3390_);
                                v___x_3393_ = crate::leanh::lean_box(0);
                                v_isShared_3394_ = v_isSharedCheck_3414_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_x_3374_);
                            crate::leanh::lean_dec_ref(v_e_3373_);
                            v_a_3415_ = crate::leanh::lean_ctor_get(v___x_3390_, 0);
                            v_isSharedCheck_3422_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3390_)) as u8;
                            if v_isSharedCheck_3422_ == 0 {
                                v___x_3417_ = v___x_3390_;
                                v_isShared_3418_ = v_isSharedCheck_3422_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3415_);
                                crate::leanh::lean_dec(v___x_3390_);
                                v___x_3417_ = crate::leanh::lean_box(0);
                                v_isShared_3418_ = v_isSharedCheck_3422_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_3374_);
                        crate::leanh::lean_dec_ref(v_e_3373_);
                        v___x_3423_ = crate::leanh::lean_box(0);
                        v___x_3424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3424_, 0, v___x_3423_);
                        return v___x_3424_;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3374_);
                    crate::leanh::lean_dec_ref(v_e_3373_);
                    v___x_3425_ = crate::leanh::lean_box(0);
                    v___x_3426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3426_, 0, v___x_3425_);
                    return v___x_3426_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3391_) == 1 {
                    crate::leanh::lean_del_object(v___x_3393_);
                    v_val_3395_ = crate::leanh::lean_ctor_get(v_a_3391_, 0);
                    v_isSharedCheck_3409_ = (!crate::leanh::lean_is_exclusive(v_a_3391_)) as u8;
                    if v_isSharedCheck_3409_ == 0 {
                        v___x_3397_ = v_a_3391_;
                        v_isShared_3398_ = v_isSharedCheck_3409_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3395_);
                        crate::leanh::lean_dec(v_a_3391_);
                        v___x_3397_ = crate::leanh::lean_box(0);
                        v_isShared_3398_ = v_isSharedCheck_3409_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3391_);
                    crate::leanh::lean_dec(v_x_3374_);
                    crate::leanh::lean_dec_ref(v_e_3373_);
                    v___x_3410_ = crate::leanh::lean_box(0);
                    if v_isShared_3394_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3393_, 0, v___x_3410_);
                        v___x_3412_ = v___x_3393_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3413_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
                        v___x_3412_ = v_reuseFailAlloc_3413_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3399_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2,
                );
                v___x_3400_ = l_Lean_mkAppB(v___x_3399_, v_e_3373_, v_val_3395_);
                v___x_3401_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6,
                );
                v___x_3402_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8,
                );
                v___x_3403_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3403_, 0, v___x_3401_);
                crate::leanh::lean_ctor_set(v___x_3403_, 1, v_x_3374_);
                crate::leanh::lean_ctor_set(v___x_3403_, 2, v___x_3402_);
                if v_isShared_3398_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3397_, 4);
                    crate::leanh::lean_ctor_set(v___x_3397_, 0, v___x_3400_);
                    v___x_3405_ = v___x_3397_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3408_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3400_);
                    v___x_3405_ = v_reuseFailAlloc_3408_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3406_, 0, v___x_3403_);
                crate::leanh::lean_ctor_set(v___x_3406_, 1, v___x_3405_);
                crate::leanh::lean_inc(v_a_3384_);
                crate::leanh::lean_inc_ref(v_a_3383_);
                crate::leanh::lean_inc(v_a_3382_);
                crate::leanh::lean_inc_ref(v_a_3381_);
                crate::leanh::lean_inc(v_a_3380_);
                crate::leanh::lean_inc_ref(v_a_3379_);
                crate::leanh::lean_inc(v_a_3378_);
                crate::leanh::lean_inc_ref(v_a_3377_);
                crate::leanh::lean_inc(v_a_3376_);
                crate::leanh::lean_inc(v_a_3375_);
                v___x_3407_ = lean_grind_cutsat_assert_le(
                    v___x_3406_,
                    v_a_3375_,
                    v_a_3376_,
                    v_a_3377_,
                    v_a_3378_,
                    v_a_3379_,
                    v_a_3380_,
                    v_a_3381_,
                    v_a_3382_,
                    v_a_3383_,
                    v_a_3384_,
                );
                return v___x_3407_;
            }
            4 => {
                return v___x_3412_;
            }
            5 => {
                if v_isShared_3418_ == 0 {
                    v___x_3420_ = v___x_3417_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
                    v___x_3420_ = v_reuseFailAlloc_3421_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___boxed(
    mut v_e_3427_: *mut crate::leanh::LeanObject,
    mut v_x_3428_: *mut crate::leanh::LeanObject,
    mut v_a_3429_: *mut crate::leanh::LeanObject,
    mut v_a_3430_: *mut crate::leanh::LeanObject,
    mut v_a_3431_: *mut crate::leanh::LeanObject,
    mut v_a_3432_: *mut crate::leanh::LeanObject,
    mut v_a_3433_: *mut crate::leanh::LeanObject,
    mut v_a_3434_: *mut crate::leanh::LeanObject,
    mut v_a_3435_: *mut crate::leanh::LeanObject,
    mut v_a_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
    mut v_a_3438_: *mut crate::leanh::LeanObject,
    mut v_a_3439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3440_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(
        v_e_3427_, v_x_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_,
        v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_,
    );
    crate::leanh::lean_dec(v_a_3438_);
    crate::leanh::lean_dec_ref(v_a_3437_);
    crate::leanh::lean_dec(v_a_3436_);
    crate::leanh::lean_dec_ref(v_a_3435_);
    crate::leanh::lean_dec(v_a_3434_);
    crate::leanh::lean_dec_ref(v_a_3433_);
    crate::leanh::lean_dec(v_a_3432_);
    crate::leanh::lean_dec_ref(v_a_3431_);
    crate::leanh::lean_dec(v_a_3430_);
    crate::leanh::lean_dec(v_a_3429_);
    return v_res_3440_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
}
