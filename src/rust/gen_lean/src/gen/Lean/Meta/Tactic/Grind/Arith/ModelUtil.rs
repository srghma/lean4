// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.ModelUtil
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Arith.Util Init.Grind.Module.Envelope
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_expr_lt,
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_mk_array, lean_nat_abs, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_shiftr,
    lean_nat_sub, lean_nat_to_int, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_append, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_ofInt, l_instDecidableEqRat_decEq};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Grind::Module::Envelope::{
    initialize_Init_Grind_Module_Envelope, runtime_initialize_Init_Grind_Module_Envelope,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hash,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Util, l_Lean_Meta_Grind_Arith_isIntNum,
    l_Lean_Meta_Grind_Arith_isNatNum, l_Lean_Meta_Grind_Arith_quoteIfArithTerm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_ENode_isRoot,
    l_Lean_Meta_Grind_Goal_getENode, l_Lean_Meta_Grind_Goal_getEqc,
    l_Lean_Meta_Grind_Goal_getGeneration, l_Lean_Meta_Grind_Goal_getRoot_x3f,
    l_Lean_Meta_Grind_ParentSet_elems, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Util::Recognizers::{l_Lean_Expr_isDIte, l_Lean_Expr_isIte};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject,907667957179513571 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10680564408669940870 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value)
            as *mut crate::leanh::LeanObject,
        1611444129324655608 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value:
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
    m_data: [72, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value:
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
    m_data: [104, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value)
            as *mut crate::leanh::LeanObject,
        16856108565602861689 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value)
            as *mut crate::leanh::LeanObject,
        4187025665268973031 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [72, 83, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [104, 83, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value)
            as *mut crate::leanh::LeanObject,
        15703084674812832738 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value)
            as *mut crate::leanh::LeanObject,
        13609749952674037527 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value)
            as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value)
            as *mut crate::leanh::LeanObject,
        17185717442815859305 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value:
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
    m_data: [72, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value:
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
    m_data: [104, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value)
            as *mut crate::leanh::LeanObject,
        11858238400308895562 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value)
            as *mut crate::leanh::LeanObject,
        6100819061652633370 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value:
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
    m_data: [72, 77, 111, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value:
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
    m_data: [104, 77, 111, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value)
            as *mut crate::leanh::LeanObject,
        13744984671752750173 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value)
            as *mut crate::leanh::LeanObject,
        9682224670061807480 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [79, 110, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [111, 110, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value)
            as *mut crate::leanh::LeanObject,
        1389984430658442515 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value)
            as *mut crate::leanh::LeanObject,
        9294582609080780319 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value:
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
    m_data: [90, 101, 114, 111, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value:
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
    m_data: [122, 101, 114, 111, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value)
            as *mut crate::leanh::LeanObject,
        18263865437487147968 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value)
            as *mut crate::leanh::LeanObject,
        2651253468108498348 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value)
            as *mut crate::leanh::LeanObject,
        1412621069384631438 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value)
            as *mut crate::leanh::LeanObject,
        10171450186735820607 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value:
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value:
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value)
            as *mut crate::leanh::LeanObject,
        5779414593499529281 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value)
            as *mut crate::leanh::LeanObject,
        7063772860359172143 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [79, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value)
            as *mut crate::leanh::LeanObject,
        17636616155771105671 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value)
            as *mut crate::leanh::LeanObject,
        15578568367168711682 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [84, 111, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 111, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value)
            as *mut crate::leanh::LeanObject,
        16822059798527729847 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value)
            as *mut crate::leanh::LeanObject,
        2495166364501146107 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [70, 105, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [118, 97, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value)
            as *mut crate::leanh::LeanObject,
        15815496672699636542 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value)
            as *mut crate::leanh::LeanObject,
        7912375598873795493 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [73, 110, 116, 77, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 102, 78, 97, 116, 77, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [116, 111, 81, 0],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value)
            as *mut crate::leanh::LeanObject,
        7605204649477761179 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value)
            as *mut crate::leanh::LeanObject,
        11314908490917688650 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value)
            as *mut crate::leanh::LeanObject,
        6592053806809043044 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_finalizeModel___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Grind_Arith_finalizeModel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_traceModel___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_traceModel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_traceModel___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_traceModel___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_traceModel___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_traceModel___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_traceModel___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__1(
    mut v_a_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Rat_ofInt(v_a_2095_);
    return v___x_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(
    mut v_a_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2098_) == 0 {
                    v___x_2099_ = crate::leanh::lean_box(0);
                    return v___x_2099_;
                } else {
                    v_key_2100_ = crate::leanh::lean_ctor_get(v_x_2098_, 0);
                    v_value_2101_ = crate::leanh::lean_ctor_get(v_x_2098_, 1);
                    v_tail_2102_ = crate::leanh::lean_ctor_get(v_x_2098_, 2);
                    v___x_2103_ = lean_expr_eqv(v_key_2100_, v_a_2097_);
                    if v___x_2103_ == 0 {
                        v_x_2098_ = v_tail_2102_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2101_);
                        v___x_2105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2105_, 0, v_value_2101_);
                        return v___x_2105_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg___boxed(
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_2106_, v_x_2107_);
    crate::leanh::lean_dec(v_x_2107_);
    crate::leanh::lean_dec_ref(v_a_2106_);
    return v_res_2108_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(
    mut v_m_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: u64 = 0;
    let mut v___x_2114_: u64 = 0;
    let mut v___x_2115_: u64 = 0;
    let mut v_fold_2116_: u64 = 0;
    let mut v___x_2117_: u64 = 0;
    let mut v___x_2118_: u64 = 0;
    let mut v___x_2119_: u64 = 0;
    let mut v___x_2120_: usize = 0;
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: usize = 0;
    let mut v___x_2123_: usize = 0;
    let mut v___x_2124_: usize = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2111_ = crate::leanh::lean_ctor_get(v_m_2109_, 1);
    v___x_2112_ = lean_array_get_size(v_buckets_2111_);
    v___x_2113_ = l_Lean_Expr_hash(v_a_2110_);
    v___x_2114_ = 32u64;
    v___x_2115_ = lean_uint64_shift_right(v___x_2113_, v___x_2114_);
    v_fold_2116_ = lean_uint64_xor(v___x_2113_, v___x_2115_);
    v___x_2117_ = 16u64;
    v___x_2118_ = lean_uint64_shift_right(v_fold_2116_, v___x_2117_);
    v___x_2119_ = lean_uint64_xor(v_fold_2116_, v___x_2118_);
    v___x_2120_ = lean_uint64_to_usize(v___x_2119_);
    v___x_2121_ = lean_usize_of_nat(v___x_2112_);
    v___x_2122_ = 1usize;
    v___x_2123_ = lean_usize_sub(v___x_2121_, v___x_2122_);
    v___x_2124_ = lean_usize_land(v___x_2120_, v___x_2123_);
    v___x_2125_ = lean_array_uget_borrowed(v_buckets_2111_, v___x_2124_);
    v___x_2126_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_2110_, v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg___boxed(
    mut v_m_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_2127_, v_a_2128_);
    crate::leanh::lean_dec_ref(v_a_2128_);
    crate::leanh::lean_dec_ref(v_m_2127_);
    return v_res_2129_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(
    mut v_a_2130_: *mut crate::leanh::LeanObject,
    mut v_v_2131_: *mut crate::leanh::LeanObject,
    mut v_other_2132_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2133_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_a_2130_, v_other_2132_);
    if crate::leanh::lean_obj_tag(v___x_2133_) == 1 {
        let mut v_val_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: u8 = 0;
        v_val_2134_ = crate::leanh::lean_ctor_get(v___x_2133_, 0);
        crate::leanh::lean_inc(v_val_2134_);
        crate::leanh::lean_dec_ref_known(v___x_2133_, 1);
        v___x_2135_ = l_Rat_ofInt(v_v_2131_);
        v___x_2136_ = l_instDecidableEqRat_decEq(v_val_2134_, v___x_2135_);
        crate::leanh::lean_dec_ref(v___x_2135_);
        crate::leanh::lean_dec(v_val_2134_);
        if v___x_2136_ == 0 {
            let mut v___x_2137_: u8 = 0;
            v___x_2137_ = 1;
            return v___x_2137_;
        } else {
            let mut v___x_2138_: u8 = 0;
            v___x_2138_ = 0;
            return v___x_2138_;
        }
    } else {
        let mut v___x_2139_: u8 = 0;
        crate::leanh::lean_dec(v___x_2133_);
        crate::leanh::lean_dec(v_v_2131_);
        v___x_2139_ = 1;
        return v___x_2139_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq___boxed(
    mut v_a_2140_: *mut crate::leanh::LeanObject,
    mut v_v_2141_: *mut crate::leanh::LeanObject,
    mut v_other_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2143_: u8 = 0;
    let mut v_r_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_2140_, v_v_2141_, v_other_2142_);
    crate::leanh::lean_dec_ref(v_other_2142_);
    crate::leanh::lean_dec_ref(v_a_2140_);
    v_r_2144_ = crate::leanh::lean_box((v_res_2143_) as usize);
    return v_r_2144_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(
    mut v_00_u03b2_2145_: *mut crate::leanh::LeanObject,
    mut v_m_2146_: *mut crate::leanh::LeanObject,
    mut v_a_2147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_2146_, v_a_2147_);
    return v___x_2148_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___boxed(
    mut v_00_u03b2_2149_: *mut crate::leanh::LeanObject,
    mut v_m_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(v_00_u03b2_2149_, v_m_2150_, v_a_2151_);
    crate::leanh::lean_dec_ref(v_a_2151_);
    crate::leanh::lean_dec_ref(v_m_2150_);
    return v_res_2152_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(
    mut v_00_u03b2_2153_: *mut crate::leanh::LeanObject,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
    mut v_x_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2156_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_2154_, v_x_2155_);
    return v___x_2156_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___boxed(
    mut v_00_u03b2_2157_: *mut crate::leanh::LeanObject,
    mut v_a_2158_: *mut crate::leanh::LeanObject,
    mut v_x_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2160_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(v_00_u03b2_2157_, v_a_2158_, v_x_2159_);
    crate::leanh::lean_dec(v_x_2159_);
    crate::leanh::lean_dec_ref(v_a_2158_);
    return v_res_2160_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(
    mut v_goal_2176_: *mut crate::leanh::LeanObject,
    mut v_e_2177_: *mut crate::leanh::LeanObject,
    mut v_a_2178_: *mut crate::leanh::LeanObject,
    mut v_v_2179_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2180_: *mut crate::leanh::LeanObject,
    mut v_b_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2187_: u8 = 0;
    let mut v___y_2188_: u8 = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v_arg_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v_arg_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: u8 = 0;
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2218_: u8 = 0;
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v___y_2223_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_2180_) == 0 {
                    crate::leanh::lean_dec(v_v_2179_);
                    crate::leanh::lean_inc_ref(v_b_2181_);
                    return v_b_2181_;
                } else {
                    v_head_2182_ = crate::leanh::lean_ctor_get(v_as_x27_2180_, 0);
                    v_tail_2183_ = crate::leanh::lean_ctor_get(v_as_x27_2180_, 1);
                    v___x_2184_ = crate::leanh::lean_box(0);
                    v___x_2185_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0;
                    crate::leanh::lean_inc(v_head_2182_);
                    v___x_2193_ = l_Lean_Expr_cleanupAnnotations(v_head_2182_);
                    v___x_2194_ = l_Lean_Expr_isApp(v___x_2193_);
                    if v___x_2194_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2193_);
                        v_as_x27_2180_ = v_tail_2183_;
                        v_b_2181_ = v___x_2185_;
                        state = 0;
                        continue;
                    } else {
                        v_arg_2196_ = crate::leanh::lean_ctor_get(v___x_2193_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2196_);
                        v___x_2197_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2193_);
                        v___x_2198_ = l_Lean_Expr_isApp(v___x_2197_);
                        if v___x_2198_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2197_);
                            crate::leanh::lean_dec_ref(v_arg_2196_);
                            v_as_x27_2180_ = v_tail_2183_;
                            v_b_2181_ = v___x_2185_;
                            state = 0;
                            continue;
                        } else {
                            v_arg_2200_ = crate::leanh::lean_ctor_get(v___x_2197_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2200_);
                            v___x_2201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2197_);
                            v___x_2202_ = l_Lean_Expr_isApp(v___x_2201_);
                            if v___x_2202_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2201_);
                                crate::leanh::lean_dec_ref(v_arg_2200_);
                                crate::leanh::lean_dec_ref(v_arg_2196_);
                                v_as_x27_2180_ = v_tail_2183_;
                                v_b_2181_ = v___x_2185_;
                                state = 0;
                                continue;
                            } else {
                                v___x_2204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2201_);
                                v___x_2205_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2;
                                v___x_2206_ = l_Lean_Expr_isConstOf(v___x_2204_, v___x_2205_);
                                crate::leanh::lean_dec_ref(v___x_2204_);
                                if v___x_2206_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_2200_);
                                    crate::leanh::lean_dec_ref(v_arg_2196_);
                                    v_as_x27_2180_ = v_tail_2183_;
                                    v_b_2181_ = v___x_2185_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_2208_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(
                                        v_goal_2176_,
                                        v_head_2182_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2208_) == 1 {
                                        v_val_2209_ = crate::leanh::lean_ctor_get(v___x_2208_, 0);
                                        crate::leanh::lean_inc(v_val_2209_);
                                        crate::leanh::lean_dec_ref_known(v___x_2208_, 1);
                                        v___x_2210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4;
                                        v___x_2211_ =
                                            l_Lean_Expr_isConstOf(v_val_2209_, v___x_2210_);
                                        crate::leanh::lean_dec(v_val_2209_);
                                        if v___x_2211_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_2200_);
                                            crate::leanh::lean_dec_ref(v_arg_2196_);
                                            v_as_x27_2180_ = v_tail_2183_;
                                            v_b_2181_ = v___x_2185_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v___x_2213_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(
                                                v_goal_2176_,
                                                v_arg_2200_,
                                            );
                                            crate::leanh::lean_dec_ref(v_arg_2200_);
                                            if crate::leanh::lean_obj_tag(v___x_2213_) == 1 {
                                                v_val_2214_ =
                                                    crate::leanh::lean_ctor_get(v___x_2213_, 0);
                                                crate::leanh::lean_inc(v_val_2214_);
                                                crate::leanh::lean_dec_ref_known(v___x_2213_, 1);
                                                v___x_2215_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(
                                                    v_goal_2176_,
                                                    v_arg_2196_,
                                                );
                                                crate::leanh::lean_dec_ref(v_arg_2196_);
                                                if crate::leanh::lean_obj_tag(v___x_2215_) == 1 {
                                                    v_val_2216_ =
                                                        crate::leanh::lean_ctor_get(v___x_2215_, 0);
                                                    crate::leanh::lean_inc(v_val_2216_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2215_,
                                                        1,
                                                    );
                                                    v___x_2225_ =
                                                        lean_expr_eqv(v_val_2214_, v_e_2177_);
                                                    if v___x_2225_ == 0 {
                                                        v___y_2223_ = v___x_2225_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_v_2179_);
                                                        v___x_2226_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_2178_, v_v_2179_, v_val_2216_);
                                                        if v___x_2226_ == 0 {
                                                            v___y_2223_ = v___x_2225_;
                                                            state = 3;
                                                            continue;
                                                        } else {
                                                            v___x_2227_ = 0;
                                                            v___y_2218_ = v___x_2227_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v___x_2215_);
                                                    crate::leanh::lean_dec(v_val_2214_);
                                                    v_as_x27_2180_ = v_tail_2183_;
                                                    v_b_2181_ = v___x_2185_;
                                                    state = 0;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v___x_2213_);
                                                crate::leanh::lean_dec_ref(v_arg_2196_);
                                                v_as_x27_2180_ = v_tail_2183_;
                                                v_b_2181_ = v___x_2185_;
                                                state = 0;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2208_);
                                        crate::leanh::lean_dec_ref(v_arg_2200_);
                                        crate::leanh::lean_dec_ref(v_arg_2196_);
                                        v_as_x27_2180_ = v_tail_2183_;
                                        v_b_2181_ = v___x_2185_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v___y_2188_ == 0 {
                    v_as_x27_2180_ = v_tail_2183_;
                    v_b_2181_ = v___x_2185_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_v_2179_);
                    v___x_2190_ = crate::leanh::lean_box((v___y_2187_) as usize);
                    v___x_2191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2191_, 0, v___x_2190_);
                    v___x_2192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2192_, 0, v___x_2191_);
                    crate::leanh::lean_ctor_set(v___x_2192_, 1, v___x_2184_);
                    return v___x_2192_;
                }
            }
            2 => {
                v___x_2219_ = lean_expr_eqv(v_val_2216_, v_e_2177_);
                crate::leanh::lean_dec(v_val_2216_);
                if v___x_2219_ == 0 {
                    crate::leanh::lean_dec(v_val_2214_);
                    v___y_2187_ = v___y_2218_;
                    v___y_2188_ = v___x_2219_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2179_);
                    v___x_2220_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_2178_, v_v_2179_, v_val_2214_);
                    crate::leanh::lean_dec(v_val_2214_);
                    if v___x_2220_ == 0 {
                        v___y_2187_ = v___y_2218_;
                        v___y_2188_ = v___x_2219_;
                        state = 1;
                        continue;
                    } else {
                        v_as_x27_2180_ = v_tail_2183_;
                        v_b_2181_ = v___x_2185_;
                        state = 0;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_2223_ == 0 {
                    v___y_2218_ = v___y_2223_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2216_);
                    crate::leanh::lean_dec(v_val_2214_);
                    crate::leanh::lean_dec(v_v_2179_);
                    v___x_2224_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6;
                    return v___x_2224_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(
    mut v_goal_2231_: *mut crate::leanh::LeanObject,
    mut v_e_2232_: *mut crate::leanh::LeanObject,
    mut v_a_2233_: *mut crate::leanh::LeanObject,
    mut v_v_2234_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2235_: *mut crate::leanh::LeanObject,
    mut v_b_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2237_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_2231_, v_e_2232_, v_a_2233_, v_v_2234_, v_as_x27_2235_, v_b_2236_);
    crate::leanh::lean_dec_ref(v_b_2236_);
    crate::leanh::lean_dec(v_as_x27_2235_);
    crate::leanh::lean_dec_ref(v_a_2233_);
    crate::leanh::lean_dec_ref(v_e_2232_);
    crate::leanh::lean_dec_ref(v_goal_2231_);
    return v_res_2237_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2238_: *mut crate::leanh::LeanObject,
    mut v_vals_2239_: *mut crate::leanh::LeanObject,
    mut v_i_2240_: *mut crate::leanh::LeanObject,
    mut v_k_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2242_ = lean_array_get_size(v_keys_2238_);
                v___x_2243_ = lean_nat_dec_lt(v_i_2240_, v___x_2242_);
                if v___x_2243_ == 0 {
                    crate::leanh::lean_dec(v_i_2240_);
                    v___x_2244_ = crate::leanh::lean_box(0);
                    return v___x_2244_;
                } else {
                    v_k_x27_2245_ = lean_array_fget_borrowed(v_keys_2238_, v_i_2240_);
                    v___x_2246_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2241_,
                            v_k_x27_2245_,
                        );
                    if v___x_2246_ == 0 {
                        v___x_2247_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2248_ = lean_nat_add(v_i_2240_, v___x_2247_);
                        crate::leanh::lean_dec(v_i_2240_);
                        v_i_2240_ = v___x_2248_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2250_ = lean_array_fget_borrowed(v_vals_2239_, v_i_2240_);
                        crate::leanh::lean_dec(v_i_2240_);
                        crate::leanh::lean_inc(v___x_2250_);
                        v___x_2251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                        return v___x_2251_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2252_: *mut crate::leanh::LeanObject,
    mut v_vals_2253_: *mut crate::leanh::LeanObject,
    mut v_i_2254_: *mut crate::leanh::LeanObject,
    mut v_k_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_2252_, v_vals_2253_, v_i_2254_, v_k_2255_);
    crate::leanh::lean_dec_ref(v_k_2255_);
    crate::leanh::lean_dec_ref(v_vals_2253_);
    crate::leanh::lean_dec_ref(v_keys_2252_);
    return v_res_2256_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2259_: usize = 0;
    v___x_2257_ = 5usize;
    v___x_2258_ = 1usize;
    v___x_2259_ = lean_usize_shift_left(v___x_2258_, v___x_2257_);
    return v___x_2259_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2260_: usize = 0;
    let mut v___x_2261_: usize = 0;
    let mut v___x_2262_: usize = 0;
    v___x_2260_ = 1usize;
    v___x_2261_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0);
    v___x_2262_ = lean_usize_sub(v___x_2261_, v___x_2260_);
    return v___x_2262_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(
    mut v_x_2263_: *mut crate::leanh::LeanObject,
    mut v_x_2264_: usize,
    mut v_x_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: usize = 0;
    let mut v___x_2269_: usize = 0;
    let mut v___x_2270_: usize = 0;
    let mut v_j_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: usize = 0;
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2263_) == 0 {
                    v_es_2266_ = crate::leanh::lean_ctor_get(v_x_2263_, 0);
                    v___x_2267_ = crate::leanh::lean_box(2);
                    v___x_2268_ = 5usize;
                    v___x_2269_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1);
                    v___x_2270_ = lean_usize_land(v_x_2264_, v___x_2269_);
                    v_j_2271_ = lean_usize_to_nat(v___x_2270_);
                    v___x_2272_ = lean_array_get_borrowed(v___x_2267_, v_es_2266_, v_j_2271_);
                    crate::leanh::lean_dec(v_j_2271_);
                    match crate::leanh::lean_obj_tag(v___x_2272_) {
                        0 => {
                            v_key_2273_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                            v_val_2274_ = crate::leanh::lean_ctor_get(v___x_2272_, 1);
                            v___x_2275_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2265_, v_key_2273_);
                            if v___x_2275_ == 0 {
                                v___x_2276_ = crate::leanh::lean_box(0);
                                return v___x_2276_;
                            } else {
                                crate::leanh::lean_inc(v_val_2274_);
                                v___x_2277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2277_, 0, v_val_2274_);
                                return v___x_2277_;
                            }
                        }
                        1 => {
                            v_node_2278_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                            v___x_2279_ = lean_usize_shift_right(v_x_2264_, v___x_2268_);
                            v_x_2263_ = v_node_2278_;
                            v_x_2264_ = v___x_2279_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2281_ = crate::leanh::lean_box(0);
                            return v___x_2281_;
                        }
                    }
                } else {
                    v_ks_2282_ = crate::leanh::lean_ctor_get(v_x_2263_, 0);
                    v_vs_2283_ = crate::leanh::lean_ctor_get(v_x_2263_, 1);
                    v___x_2284_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2285_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_2282_, v_vs_2283_, v___x_2284_, v_x_2265_);
                    return v___x_2285_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(
    mut v_x_2286_: *mut crate::leanh::LeanObject,
    mut v_x_2287_: *mut crate::leanh::LeanObject,
    mut v_x_2288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2615__boxed_2289_: usize = 0;
    let mut v_res_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2615__boxed_2289_ = crate::leanh::lean_unbox_usize(v_x_2287_);
    crate::leanh::lean_dec(v_x_2287_);
    v_res_2290_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_2286_, v_x_2615__boxed_2289_, v_x_2288_);
    crate::leanh::lean_dec_ref(v_x_2288_);
    crate::leanh::lean_dec_ref(v_x_2286_);
    return v_res_2290_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(
    mut v_x_2291_: *mut crate::leanh::LeanObject,
    mut v_x_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2293_: u64 = 0;
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2292_);
    v___x_2294_ = lean_uint64_to_usize(v___x_2293_);
    v___x_2295_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_2291_, v___x_2294_, v_x_2292_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(
    mut v_x_2296_: *mut crate::leanh::LeanObject,
    mut v_x_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2298_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_2296_, v_x_2297_);
    crate::leanh::lean_dec_ref(v_x_2297_);
    crate::leanh::lean_dec_ref(v_x_2296_);
    return v_res_2298_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(
    mut v_goal_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
    mut v_e_2301_: *mut crate::leanh::LeanObject,
    mut v_v_2302_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toGoalState_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toGoalState_2303_ = crate::leanh::lean_ctor_get(v_goal_2299_, 0);
    v_parents_2304_ = crate::leanh::lean_ctor_get(v_toGoalState_2303_, 3);
    v___x_2305_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_parents_2304_, v_e_2301_);
    if crate::leanh::lean_obj_tag(v___x_2305_) == 1 {
        let mut v_val_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2306_ = crate::leanh::lean_ctor_get(v___x_2305_, 0);
        crate::leanh::lean_inc(v_val_2306_);
        crate::leanh::lean_dec_ref_known(v___x_2305_, 1);
        v___x_2307_ = l_Lean_Meta_Grind_ParentSet_elems(v_val_2306_);
        crate::leanh::lean_dec(v_val_2306_);
        v___x_2308_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0;
        v___x_2309_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_2299_, v_e_2301_, v_a_2300_, v_v_2302_, v___x_2307_, v___x_2308_);
        crate::leanh::lean_dec(v___x_2307_);
        v_fst_2310_ = crate::leanh::lean_ctor_get(v___x_2309_, 0);
        crate::leanh::lean_inc(v_fst_2310_);
        crate::leanh::lean_dec_ref(v___x_2309_);
        if crate::leanh::lean_obj_tag(v_fst_2310_) == 0 {
            let mut v___x_2311_: u8 = 0;
            v___x_2311_ = 1;
            return v___x_2311_;
        } else {
            let mut v_val_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2313_: u8 = 0;
            v_val_2312_ = crate::leanh::lean_ctor_get(v_fst_2310_, 0);
            crate::leanh::lean_inc(v_val_2312_);
            crate::leanh::lean_dec_ref_known(v_fst_2310_, 1);
            v___x_2313_ = (crate::leanh::lean_unbox(v_val_2312_) as u8);
            crate::leanh::lean_dec(v_val_2312_);
            return v___x_2313_;
        }
    } else {
        let mut v___x_2314_: u8 = 0;
        crate::leanh::lean_dec(v___x_2305_);
        crate::leanh::lean_dec(v_v_2302_);
        v___x_2314_ = 1;
        return v___x_2314_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(
    mut v_goal_2315_: *mut crate::leanh::LeanObject,
    mut v_a_2316_: *mut crate::leanh::LeanObject,
    mut v_e_2317_: *mut crate::leanh::LeanObject,
    mut v_v_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2319_: u8 = 0;
    let mut v_r_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2319_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(
            v_goal_2315_,
            v_a_2316_,
            v_e_2317_,
            v_v_2318_,
        );
    crate::leanh::lean_dec_ref(v_e_2317_);
    crate::leanh::lean_dec_ref(v_a_2316_);
    crate::leanh::lean_dec_ref(v_goal_2315_);
    v_r_2320_ = crate::leanh::lean_box((v_res_2319_) as usize);
    return v_r_2320_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(
    mut v_00_u03b2_2321_: *mut crate::leanh::LeanObject,
    mut v_x_2322_: *mut crate::leanh::LeanObject,
    mut v_x_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2324_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_2322_, v_x_2323_);
    return v___x_2324_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(
    mut v_00_u03b2_2325_: *mut crate::leanh::LeanObject,
    mut v_x_2326_: *mut crate::leanh::LeanObject,
    mut v_x_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(v_00_u03b2_2325_, v_x_2326_, v_x_2327_);
    crate::leanh::lean_dec_ref(v_x_2327_);
    crate::leanh::lean_dec_ref(v_x_2326_);
    return v_res_2328_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(
    mut v_goal_2329_: *mut crate::leanh::LeanObject,
    mut v_e_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
    mut v_v_2332_: *mut crate::leanh::LeanObject,
    mut v_as_2333_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2334_: *mut crate::leanh::LeanObject,
    mut v_b_2335_: *mut crate::leanh::LeanObject,
    mut v_a_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_2329_, v_e_2330_, v_a_2331_, v_v_2332_, v_as_x27_2334_, v_b_2335_);
    return v___x_2337_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(
    mut v_goal_2338_: *mut crate::leanh::LeanObject,
    mut v_e_2339_: *mut crate::leanh::LeanObject,
    mut v_a_2340_: *mut crate::leanh::LeanObject,
    mut v_v_2341_: *mut crate::leanh::LeanObject,
    mut v_as_2342_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2343_: *mut crate::leanh::LeanObject,
    mut v_b_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2346_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(v_goal_2338_, v_e_2339_, v_a_2340_, v_v_2341_, v_as_2342_, v_as_x27_2343_, v_b_2344_, v_a_2345_);
    crate::leanh::lean_dec_ref(v_b_2344_);
    crate::leanh::lean_dec(v_as_x27_2343_);
    crate::leanh::lean_dec(v_as_2342_);
    crate::leanh::lean_dec_ref(v_a_2340_);
    crate::leanh::lean_dec_ref(v_e_2339_);
    crate::leanh::lean_dec_ref(v_goal_2338_);
    return v_res_2346_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(
    mut v_00_u03b2_2347_: *mut crate::leanh::LeanObject,
    mut v_x_2348_: *mut crate::leanh::LeanObject,
    mut v_x_2349_: usize,
    mut v_x_2350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_2348_, v_x_2349_, v_x_2350_);
    return v___x_2351_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(
    mut v_00_u03b2_2352_: *mut crate::leanh::LeanObject,
    mut v_x_2353_: *mut crate::leanh::LeanObject,
    mut v_x_2354_: *mut crate::leanh::LeanObject,
    mut v_x_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2716__boxed_2356_: usize = 0;
    let mut v_res_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2716__boxed_2356_ = crate::leanh::lean_unbox_usize(v_x_2354_);
    crate::leanh::lean_dec(v_x_2354_);
    v_res_2357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_2352_, v_x_2353_, v_x_2716__boxed_2356_, v_x_2355_);
    crate::leanh::lean_dec_ref(v_x_2355_);
    crate::leanh::lean_dec_ref(v_x_2353_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2358_: *mut crate::leanh::LeanObject,
    mut v_keys_2359_: *mut crate::leanh::LeanObject,
    mut v_vals_2360_: *mut crate::leanh::LeanObject,
    mut v_heq_2361_: *mut crate::leanh::LeanObject,
    mut v_i_2362_: *mut crate::leanh::LeanObject,
    mut v_k_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_2359_, v_vals_2360_, v_i_2362_, v_k_2363_);
    return v___x_2364_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2365_: *mut crate::leanh::LeanObject,
    mut v_keys_2366_: *mut crate::leanh::LeanObject,
    mut v_vals_2367_: *mut crate::leanh::LeanObject,
    mut v_heq_2368_: *mut crate::leanh::LeanObject,
    mut v_i_2369_: *mut crate::leanh::LeanObject,
    mut v_k_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2371_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(v_00_u03b2_2365_, v_keys_2366_, v_vals_2367_, v_heq_2368_, v_i_2369_, v_k_2370_);
    crate::leanh::lean_dec_ref(v_k_2370_);
    crate::leanh::lean_dec_ref(v_vals_2367_);
    crate::leanh::lean_dec_ref(v_keys_2366_);
    return v_res_2371_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(
    mut v_a_2372_: *mut crate::leanh::LeanObject,
    mut v_x_2373_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2374_: u8 = 0;
    let mut v_key_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2373_) == 0 {
                    v___x_2374_ = 0;
                    return v___x_2374_;
                } else {
                    v_key_2375_ = crate::leanh::lean_ctor_get(v_x_2373_, 0);
                    v_tail_2376_ = crate::leanh::lean_ctor_get(v_x_2373_, 2);
                    v___x_2377_ = lean_int_dec_eq(v_key_2375_, v_a_2372_);
                    if v___x_2377_ == 0 {
                        v_x_2373_ = v_tail_2376_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2377_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(
    mut v_a_2379_: *mut crate::leanh::LeanObject,
    mut v_x_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2381_: u8 = 0;
    let mut v_r_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2381_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_2379_, v_x_2380_);
    crate::leanh::lean_dec(v_x_2380_);
    crate::leanh::lean_dec(v_a_2379_);
    v_r_2382_ = crate::leanh::lean_box((v_res_2381_) as usize);
    return v_r_2382_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_natZero_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_2383_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_2384_ = lean_nat_to_int(v_natZero_2383_);
    return v_intZero_2384_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(
    mut v_m_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2390_: u64 = 0;
    let mut v___x_2391_: u64 = 0;
    let mut v___x_2392_: u64 = 0;
    let mut v_fold_2393_: u64 = 0;
    let mut v___x_2394_: u64 = 0;
    let mut v___x_2395_: u64 = 0;
    let mut v___x_2396_: u64 = 0;
    let mut v___x_2397_: usize = 0;
    let mut v___x_2398_: usize = 0;
    let mut v___x_2399_: usize = 0;
    let mut v___x_2400_: usize = 0;
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: u8 = 0;
    let mut v_intZero_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_2405_: u8 = 0;
    let mut v_a_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: u64 = 0;
    let mut v_abs_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2387_ = crate::leanh::lean_ctor_get(v_m_2385_, 1);
                v___x_2388_ = lean_array_get_size(v_buckets_2387_);
                v_intZero_2404_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
                v_isNeg_2405_ = lean_int_dec_lt(v_a_2386_, v_intZero_2404_);
                if v_isNeg_2405_ == 0 {
                    v_a_2406_ = lean_nat_abs(v_a_2386_);
                    v___x_2407_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2408_ = lean_nat_mul(v___x_2407_, v_a_2406_);
                    crate::leanh::lean_dec(v_a_2406_);
                    v___x_2409_ = lean_uint64_of_nat(v___x_2408_);
                    crate::leanh::lean_dec(v___x_2408_);
                    v___y_2390_ = v___x_2409_;
                    state = 1;
                    continue;
                } else {
                    v_abs_2410_ = lean_nat_abs(v_a_2386_);
                    v_one_2411_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_a_2412_ = lean_nat_sub(v_abs_2410_, v_one_2411_);
                    crate::leanh::lean_dec(v_abs_2410_);
                    v___x_2413_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2414_ = lean_nat_mul(v___x_2413_, v_a_2412_);
                    crate::leanh::lean_dec(v_a_2412_);
                    v___x_2415_ = lean_nat_add(v___x_2414_, v_one_2411_);
                    crate::leanh::lean_dec(v___x_2414_);
                    v___x_2416_ = lean_uint64_of_nat(v___x_2415_);
                    crate::leanh::lean_dec(v___x_2415_);
                    v___y_2390_ = v___x_2416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2391_ = 32u64;
                v___x_2392_ = lean_uint64_shift_right(v___y_2390_, v___x_2391_);
                v_fold_2393_ = lean_uint64_xor(v___y_2390_, v___x_2392_);
                v___x_2394_ = 16u64;
                v___x_2395_ = lean_uint64_shift_right(v_fold_2393_, v___x_2394_);
                v___x_2396_ = lean_uint64_xor(v_fold_2393_, v___x_2395_);
                v___x_2397_ = lean_uint64_to_usize(v___x_2396_);
                v___x_2398_ = lean_usize_of_nat(v___x_2388_);
                v___x_2399_ = 1usize;
                v___x_2400_ = lean_usize_sub(v___x_2398_, v___x_2399_);
                v___x_2401_ = lean_usize_land(v___x_2397_, v___x_2400_);
                v___x_2402_ = lean_array_uget_borrowed(v_buckets_2387_, v___x_2401_);
                v___x_2403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_2386_, v___x_2402_);
                return v___x_2403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(
    mut v_m_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2419_: u8 = 0;
    let mut v_r_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2419_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_2417_, v_a_2418_);
    crate::leanh::lean_dec(v_a_2418_);
    crate::leanh::lean_dec_ref(v_m_2417_);
    v_r_2420_ = crate::leanh::lean_box((v_res_2419_) as usize);
    return v_r_2420_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2421_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2422_ = lean_nat_to_int(v___x_2421_);
    return v___x_2422_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(
    mut v_goal_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
    mut v_e_2425_: *mut crate::leanh::LeanObject,
    mut v_alreadyUsed_2426_: *mut crate::leanh::LeanObject,
    mut v_next_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2428_: u8 = 0;
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_alreadyUsed_2426_, v_next_2427_);
                if v___x_2428_ == 0 {
                    crate::leanh::lean_inc(v_next_2427_);
                    v___x_2429_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_2423_, v_a_2424_, v_e_2425_, v_next_2427_);
                    if v___x_2429_ == 0 {
                        v___x_2430_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                        v___x_2431_ = lean_int_add(v_next_2427_, v___x_2430_);
                        crate::leanh::lean_dec(v_next_2427_);
                        v_next_2427_ = v___x_2431_;
                        state = 0;
                        continue;
                    } else {
                        return v_next_2427_;
                    }
                } else {
                    v___x_2433_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                    v___x_2434_ = lean_int_add(v_next_2427_, v___x_2433_);
                    crate::leanh::lean_dec(v_next_2427_);
                    v_next_2427_ = v___x_2434_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(
    mut v_goal_2436_: *mut crate::leanh::LeanObject,
    mut v_a_2437_: *mut crate::leanh::LeanObject,
    mut v_e_2438_: *mut crate::leanh::LeanObject,
    mut v_alreadyUsed_2439_: *mut crate::leanh::LeanObject,
    mut v_next_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_2436_, v_a_2437_, v_e_2438_, v_alreadyUsed_2439_, v_next_2440_);
    crate::leanh::lean_dec_ref(v_alreadyUsed_2439_);
    crate::leanh::lean_dec_ref(v_e_2438_);
    crate::leanh::lean_dec_ref(v_a_2437_);
    crate::leanh::lean_dec_ref(v_goal_2436_);
    return v_res_2441_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(
    mut v_00_u03b2_2442_: *mut crate::leanh::LeanObject,
    mut v_m_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2445_: u8 = 0;
    v___x_2445_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_2443_, v_a_2444_);
    return v___x_2445_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(
    mut v_00_u03b2_2446_: *mut crate::leanh::LeanObject,
    mut v_m_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2449_: u8 = 0;
    let mut v_r_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(v_00_u03b2_2446_, v_m_2447_, v_a_2448_);
    crate::leanh::lean_dec(v_a_2448_);
    crate::leanh::lean_dec_ref(v_m_2447_);
    v_r_2450_ = crate::leanh::lean_box((v_res_2449_) as usize);
    return v_r_2450_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(
    mut v_00_u03b2_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
    mut v_x_2453_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2454_: u8 = 0;
    v___x_2454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_2452_, v_x_2453_);
    return v___x_2454_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
    mut v_x_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2458_: u8 = 0;
    let mut v_r_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(v_00_u03b2_2455_, v_a_2456_, v_x_2457_);
    crate::leanh::lean_dec(v_x_2457_);
    crate::leanh::lean_dec(v_a_2456_);
    v_r_2459_ = crate::leanh::lean_box((v_res_2458_) as usize);
    return v_r_2459_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_pickUnusedValue(
    mut v_goal_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_e_2462_: *mut crate::leanh::LeanObject,
    mut v_next_2463_: *mut crate::leanh::LeanObject,
    mut v_alreadyUsed_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2465_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_2460_, v_a_2461_, v_e_2462_, v_alreadyUsed_2464_, v_next_2463_);
    return v___x_2465_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(
    mut v_goal_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_e_2468_: *mut crate::leanh::LeanObject,
    mut v_next_2469_: *mut crate::leanh::LeanObject,
    mut v_alreadyUsed_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2471_ = l_Lean_Meta_Grind_Arith_pickUnusedValue(
        v_goal_2466_,
        v_a_2467_,
        v_e_2468_,
        v_next_2469_,
        v_alreadyUsed_2470_,
    );
    crate::leanh::lean_dec_ref(v_alreadyUsed_2470_);
    crate::leanh::lean_dec_ref(v_e_2468_);
    crate::leanh::lean_dec_ref(v_a_2467_);
    crate::leanh::lean_dec_ref(v_goal_2466_);
    return v_res_2471_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isInterpretedTerm(
    mut v_e_2555_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2557_: u8 = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: u8 = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: u8 = 0;
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u8 = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: u8 = 0;
    let mut v_a_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: u8 = 0;
    let mut v___x_2593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2555_);
                v___x_2592_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_2555_);
                if v___x_2592_ == 0 {
                    crate::leanh::lean_inc_ref(v_e_2555_);
                    v___x_2593_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_2555_);
                    v___y_2557_ = v___x_2593_;
                    state = 1;
                    continue;
                } else {
                    v___y_2557_ = v___x_2592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2557_ == 0 {
                    v___x_2558_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2;
                    v___x_2559_ = l_Lean_Expr_isAppOf(v_e_2555_, v___x_2558_);
                    if v___x_2559_ == 0 {
                        v___x_2560_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5;
                        v___x_2561_ = l_Lean_Expr_isAppOf(v_e_2555_, v___x_2560_);
                        if v___x_2561_ == 0 {
                            v___x_2562_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8;
                            v___x_2563_ = l_Lean_Expr_isAppOf(v_e_2555_, v___x_2562_);
                            if v___x_2563_ == 0 {
                                v___x_2564_ =
                                    l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11;
                                v___x_2565_ = l_Lean_Expr_isAppOf(v_e_2555_, v___x_2564_);
                                if v___x_2565_ == 0 {
                                    v___x_2566_ =
                                        l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14;
                                    v___x_2567_ = l_Lean_Expr_isAppOf(v_e_2555_, v___x_2566_);
                                    if v___x_2567_ == 0 {
                                        v___x_2568_ =
                                            l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17;
                                        v___x_2569_ = l_Lean_Expr_isAppOf(v_e_2555_, v___x_2568_);
                                        if v___x_2569_ == 0 {
                                            v___x_2570_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20;
                                            v___x_2571_ =
                                                l_Lean_Expr_isAppOf(v_e_2555_, v___x_2570_);
                                            if v___x_2571_ == 0 {
                                                v___x_2572_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23;
                                                v___x_2573_ =
                                                    l_Lean_Expr_isAppOf(v_e_2555_, v___x_2572_);
                                                if v___x_2573_ == 0 {
                                                    v___x_2574_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26;
                                                    v___x_2575_ =
                                                        l_Lean_Expr_isAppOf(v_e_2555_, v___x_2574_);
                                                    if v___x_2575_ == 0 {
                                                        v___x_2576_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29;
                                                        v___x_2577_ = l_Lean_Expr_isAppOf(
                                                            v_e_2555_,
                                                            v___x_2576_,
                                                        );
                                                        if v___x_2577_ == 0 {
                                                            v___x_2578_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32;
                                                            v___x_2579_ = l_Lean_Expr_isAppOf(
                                                                v_e_2555_,
                                                                v___x_2578_,
                                                            );
                                                            if v___x_2579_ == 0 {
                                                                v___x_2580_ =
                                                                    l_Lean_Expr_isIte(v_e_2555_);
                                                                if v___x_2580_ == 0 {
                                                                    v___x_2581_ =
                                                                        l_Lean_Expr_isDIte(
                                                                            v_e_2555_,
                                                                        );
                                                                    if v___x_2581_ == 0 {
                                                                        v___x_2582_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35;
                                                                        v___x_2583_ =
                                                                            l_Lean_Expr_isAppOf(
                                                                                v_e_2555_,
                                                                                v___x_2582_,
                                                                            );
                                                                        if v___x_2583_ == 0 {
                                                                            v___x_2584_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40;
                                                                            v___x_2585_ =
                                                                                l_Lean_Expr_isAppOf(
                                                                                    v_e_2555_,
                                                                                    v___x_2584_,
                                                                                );
                                                                            if v___x_2585_ == 0 {
                                                                                v___x_2586_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43;
                                                                                v___x_2587_ = l_Lean_Expr_isAppOf(v_e_2555_, v___x_2586_);
                                                                                if v___x_2587_ == 0
                                                                                {
                                                                                    v___x_2588_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47;
                                                                                    v___x_2589_ = l_Lean_Expr_isAppOf(v_e_2555_, v___x_2588_);
                                                                                    if v___x_2589_
                                                                                        == 0
                                                                                    {
                                                                                        if crate::leanh::lean_obj_tag(v_e_2555_) == 9 {
v_a_2590_ = crate::leanh::lean_ctor_get(v_e_2555_, 0);
crate::leanh::lean_inc_ref(v_a_2590_);
crate::leanh::lean_dec_ref_known(v_e_2555_, 1);
if crate::leanh::lean_obj_tag(v_a_2590_) == 0 {
crate::leanh::lean_dec_ref_known(v_a_2590_, 1);
v___x_2591_ = 1;
return v___x_2591_;
} else {
crate::leanh::lean_dec_ref(v_a_2590_);
return v___x_2589_;
}
} else {
crate::leanh::lean_dec_ref(v_e_2555_);
return v___x_2589_;
}
                                                                                    } else {
                                                                                        crate::leanh::lean_dec_ref(v_e_2555_);
                                                                                        return v___x_2589_;
                                                                                    }
                                                                                } else {
                                                                                    crate::leanh::lean_dec_ref(v_e_2555_);
                                                                                    return v___x_2587_;
                                                                                }
                                                                            } else {
                                                                                crate::leanh::lean_dec_ref(v_e_2555_);
                                                                                return v___x_2585_;
                                                                            }
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v_e_2555_);
                                                                            return v___x_2583_;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_2555_,
                                                                        );
                                                                        return v___x_2581_;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_2555_,
                                                                    );
                                                                    return v___x_2580_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_2555_,
                                                                );
                                                                return v___x_2579_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_e_2555_);
                                                            return v___x_2577_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_e_2555_);
                                                        return v___x_2575_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_e_2555_);
                                                    return v___x_2573_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_e_2555_);
                                                return v___x_2571_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_e_2555_);
                                            return v___x_2569_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_e_2555_);
                                        return v___x_2567_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_e_2555_);
                                    return v___x_2565_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_2555_);
                                return v___x_2563_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_2555_);
                            return v___x_2561_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2555_);
                        return v___x_2559_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2555_);
                    return v___y_2557_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(
    mut v_e_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2595_: u8 = 0;
    let mut v_r_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2595_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_2594_);
    v_r_2596_ = crate::leanh::lean_box((v_res_2595_) as usize);
    return v_r_2596_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_2597_: *mut crate::leanh::LeanObject,
    mut v_x_2598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u64 = 0;
    let mut v___x_2607_: u64 = 0;
    let mut v___x_2608_: u64 = 0;
    let mut v_fold_2609_: u64 = 0;
    let mut v___x_2610_: u64 = 0;
    let mut v___x_2611_: u64 = 0;
    let mut v___x_2612_: u64 = 0;
    let mut v___x_2613_: usize = 0;
    let mut v___x_2614_: usize = 0;
    let mut v___x_2615_: usize = 0;
    let mut v___x_2616_: usize = 0;
    let mut v___x_2617_: usize = 0;
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2598_) == 0 {
                    return v_x_2597_;
                } else {
                    v_key_2599_ = crate::leanh::lean_ctor_get(v_x_2598_, 0);
                    v_value_2600_ = crate::leanh::lean_ctor_get(v_x_2598_, 1);
                    v_tail_2601_ = crate::leanh::lean_ctor_get(v_x_2598_, 2);
                    v_isSharedCheck_2624_ = (!crate::leanh::lean_is_exclusive(v_x_2598_)) as u8;
                    if v_isSharedCheck_2624_ == 0 {
                        v___x_2603_ = v_x_2598_;
                        v_isShared_2604_ = v_isSharedCheck_2624_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2601_);
                        crate::leanh::lean_inc(v_value_2600_);
                        crate::leanh::lean_inc(v_key_2599_);
                        crate::leanh::lean_dec(v_x_2598_);
                        v___x_2603_ = crate::leanh::lean_box(0);
                        v_isShared_2604_ = v_isSharedCheck_2624_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2605_ = lean_array_get_size(v_x_2597_);
                v___x_2606_ = l_Lean_Expr_hash(v_key_2599_);
                v___x_2607_ = 32u64;
                v___x_2608_ = lean_uint64_shift_right(v___x_2606_, v___x_2607_);
                v_fold_2609_ = lean_uint64_xor(v___x_2606_, v___x_2608_);
                v___x_2610_ = 16u64;
                v___x_2611_ = lean_uint64_shift_right(v_fold_2609_, v___x_2610_);
                v___x_2612_ = lean_uint64_xor(v_fold_2609_, v___x_2611_);
                v___x_2613_ = lean_uint64_to_usize(v___x_2612_);
                v___x_2614_ = lean_usize_of_nat(v___x_2605_);
                v___x_2615_ = 1usize;
                v___x_2616_ = lean_usize_sub(v___x_2614_, v___x_2615_);
                v___x_2617_ = lean_usize_land(v___x_2613_, v___x_2616_);
                v___x_2618_ = lean_array_uget_borrowed(v_x_2597_, v___x_2617_);
                crate::leanh::lean_inc(v___x_2618_);
                if v_isShared_2604_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2603_, 2, v___x_2618_);
                    v___x_2620_ = v___x_2603_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_key_2599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_value_2600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 2, v___x_2618_);
                    v___x_2620_ = v_reuseFailAlloc_2623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2621_ = lean_array_uset(v_x_2597_, v___x_2617_, v___x_2620_);
                v_x_2597_ = v___x_2621_;
                v_x_2598_ = v_tail_2601_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(
    mut v_i_2625_: *mut crate::leanh::LeanObject,
    mut v_source_2626_: *mut crate::leanh::LeanObject,
    mut v_target_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v_es_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2628_ = lean_array_get_size(v_source_2626_);
                v___x_2629_ = lean_nat_dec_lt(v_i_2625_, v___x_2628_);
                if v___x_2629_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2626_);
                    crate::leanh::lean_dec(v_i_2625_);
                    return v_target_2627_;
                } else {
                    v_es_2630_ = lean_array_fget(v_source_2626_, v_i_2625_);
                    v___x_2631_ = crate::leanh::lean_box(0);
                    v_source_2632_ = lean_array_fset(v_source_2626_, v_i_2625_, v___x_2631_);
                    v_target_2633_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2627_, v_es_2630_);
                    v___x_2634_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2635_ = lean_nat_add(v_i_2625_, v___x_2634_);
                    crate::leanh::lean_dec(v_i_2625_);
                    v_i_2625_ = v___x_2635_;
                    v_source_2626_ = v_source_2632_;
                    v_target_2627_ = v_target_2633_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(
    mut v_data_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = lean_array_get_size(v_data_2637_);
    v___x_2639_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2640_ = lean_nat_mul(v___x_2638_, v___x_2639_);
    v___x_2641_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2642_ = crate::leanh::lean_box(0);
    v___x_2643_ = lean_mk_array(v_nbuckets_2640_, v___x_2642_);
    v___x_2644_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_2641_, v_data_2637_, v___x_2643_);
    return v___x_2644_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(
    mut v_a_2645_: *mut crate::leanh::LeanObject,
    mut v_b_2646_: *mut crate::leanh::LeanObject,
    mut v_x_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2647_) == 0 {
                    crate::leanh::lean_dec(v_b_2646_);
                    crate::leanh::lean_dec_ref(v_a_2645_);
                    return v_x_2647_;
                } else {
                    v_key_2648_ = crate::leanh::lean_ctor_get(v_x_2647_, 0);
                    v_value_2649_ = crate::leanh::lean_ctor_get(v_x_2647_, 1);
                    v_tail_2650_ = crate::leanh::lean_ctor_get(v_x_2647_, 2);
                    v_isSharedCheck_2662_ = (!crate::leanh::lean_is_exclusive(v_x_2647_)) as u8;
                    if v_isSharedCheck_2662_ == 0 {
                        v___x_2652_ = v_x_2647_;
                        v_isShared_2653_ = v_isSharedCheck_2662_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2650_);
                        crate::leanh::lean_inc(v_value_2649_);
                        crate::leanh::lean_inc(v_key_2648_);
                        crate::leanh::lean_dec(v_x_2647_);
                        v___x_2652_ = crate::leanh::lean_box(0);
                        v_isShared_2653_ = v_isSharedCheck_2662_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2654_ = lean_expr_eqv(v_key_2648_, v_a_2645_);
                if v___x_2654_ == 0 {
                    v___x_2655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_2645_, v_b_2646_, v_tail_2650_);
                    if v_isShared_2653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2652_, 2, v___x_2655_);
                        v___x_2657_ = v___x_2652_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2658_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_key_2648_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_value_2649_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 2, v___x_2655_);
                        v___x_2657_ = v_reuseFailAlloc_2658_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2649_);
                    crate::leanh::lean_dec(v_key_2648_);
                    if v_isShared_2653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2652_, 1, v_b_2646_);
                        crate::leanh::lean_ctor_set(v___x_2652_, 0, v_a_2645_);
                        v___x_2660_ = v___x_2652_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2645_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_b_2646_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_tail_2650_);
                        v___x_2660_ = v_reuseFailAlloc_2661_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2657_;
            }
            3 => {
                return v___x_2660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(
    mut v_a_2663_: *mut crate::leanh::LeanObject,
    mut v_x_2664_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2665_: u8 = 0;
    let mut v_key_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2664_) == 0 {
                    v___x_2665_ = 0;
                    return v___x_2665_;
                } else {
                    v_key_2666_ = crate::leanh::lean_ctor_get(v_x_2664_, 0);
                    v_tail_2667_ = crate::leanh::lean_ctor_get(v_x_2664_, 2);
                    v___x_2668_ = lean_expr_eqv(v_key_2666_, v_a_2663_);
                    if v___x_2668_ == 0 {
                        v_x_2664_ = v_tail_2667_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2668_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(
    mut v_a_2670_: *mut crate::leanh::LeanObject,
    mut v_x_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2672_: u8 = 0;
    let mut v_r_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_2670_, v_x_2671_);
    crate::leanh::lean_dec(v_x_2671_);
    crate::leanh::lean_dec_ref(v_a_2670_);
    v_r_2673_ = crate::leanh::lean_box((v_res_2672_) as usize);
    return v_r_2673_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(
    mut v_m_2674_: *mut crate::leanh::LeanObject,
    mut v_a_2675_: *mut crate::leanh::LeanObject,
    mut v_b_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u64 = 0;
    let mut v___x_2684_: u64 = 0;
    let mut v___x_2685_: u64 = 0;
    let mut v_fold_2686_: u64 = 0;
    let mut v___x_2687_: u64 = 0;
    let mut v___x_2688_: u64 = 0;
    let mut v___x_2689_: u64 = 0;
    let mut v___x_2690_: usize = 0;
    let mut v___x_2691_: usize = 0;
    let mut v___x_2692_: usize = 0;
    let mut v___x_2693_: usize = 0;
    let mut v___x_2694_: usize = 0;
    let mut v_bkt_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: u8 = 0;
    let mut v_val_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2677_ = crate::leanh::lean_ctor_get(v_m_2674_, 0);
                v_buckets_2678_ = crate::leanh::lean_ctor_get(v_m_2674_, 1);
                v_isSharedCheck_2721_ = (!crate::leanh::lean_is_exclusive(v_m_2674_)) as u8;
                if v_isSharedCheck_2721_ == 0 {
                    v___x_2680_ = v_m_2674_;
                    v_isShared_2681_ = v_isSharedCheck_2721_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2678_);
                    crate::leanh::lean_inc(v_size_2677_);
                    crate::leanh::lean_dec(v_m_2674_);
                    v___x_2680_ = crate::leanh::lean_box(0);
                    v_isShared_2681_ = v_isSharedCheck_2721_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2682_ = lean_array_get_size(v_buckets_2678_);
                v___x_2683_ = l_Lean_Expr_hash(v_a_2675_);
                v___x_2684_ = 32u64;
                v___x_2685_ = lean_uint64_shift_right(v___x_2683_, v___x_2684_);
                v_fold_2686_ = lean_uint64_xor(v___x_2683_, v___x_2685_);
                v___x_2687_ = 16u64;
                v___x_2688_ = lean_uint64_shift_right(v_fold_2686_, v___x_2687_);
                v___x_2689_ = lean_uint64_xor(v_fold_2686_, v___x_2688_);
                v___x_2690_ = lean_uint64_to_usize(v___x_2689_);
                v___x_2691_ = lean_usize_of_nat(v___x_2682_);
                v___x_2692_ = 1usize;
                v___x_2693_ = lean_usize_sub(v___x_2691_, v___x_2692_);
                v___x_2694_ = lean_usize_land(v___x_2690_, v___x_2693_);
                v_bkt_2695_ = lean_array_uget_borrowed(v_buckets_2678_, v___x_2694_);
                v___x_2696_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_2675_, v_bkt_2695_);
                if v___x_2696_ == 0 {
                    v___x_2697_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2698_ = lean_nat_add(v_size_2677_, v___x_2697_);
                    crate::leanh::lean_dec(v_size_2677_);
                    crate::leanh::lean_inc(v_bkt_2695_);
                    v___x_2699_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2699_, 0, v_a_2675_);
                    crate::leanh::lean_ctor_set(v___x_2699_, 1, v_b_2676_);
                    crate::leanh::lean_ctor_set(v___x_2699_, 2, v_bkt_2695_);
                    v_buckets_x27_2700_ =
                        lean_array_uset(v_buckets_2678_, v___x_2694_, v___x_2699_);
                    v___x_2701_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2702_ = lean_nat_mul(v_size_x27_2698_, v___x_2701_);
                    v___x_2703_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2704_ = lean_nat_div(v___x_2702_, v___x_2703_);
                    crate::leanh::lean_dec(v___x_2702_);
                    v___x_2705_ = lean_array_get_size(v_buckets_x27_2700_);
                    v___x_2706_ = lean_nat_dec_le(v___x_2704_, v___x_2705_);
                    crate::leanh::lean_dec(v___x_2704_);
                    if v___x_2706_ == 0 {
                        v_val_2707_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_2700_);
                        if v_isShared_2681_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2680_, 1, v_val_2707_);
                            crate::leanh::lean_ctor_set(v___x_2680_, 0, v_size_x27_2698_);
                            v___x_2709_ = v___x_2680_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2710_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2710_,
                                0,
                                v_size_x27_2698_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_val_2707_);
                            v___x_2709_ = v_reuseFailAlloc_2710_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2681_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2680_, 1, v_buckets_x27_2700_);
                            crate::leanh::lean_ctor_set(v___x_2680_, 0, v_size_x27_2698_);
                            v___x_2712_ = v___x_2680_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2713_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2713_,
                                0,
                                v_size_x27_2698_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2713_,
                                1,
                                v_buckets_x27_2700_,
                            );
                            v___x_2712_ = v_reuseFailAlloc_2713_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2695_);
                    v___x_2714_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2715_ =
                        lean_array_uset(v_buckets_2678_, v___x_2694_, v___x_2714_);
                    v___x_2716_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_2675_, v_b_2676_, v_bkt_2695_);
                    v___x_2717_ = lean_array_uset(v_buckets_x27_2715_, v___x_2694_, v___x_2716_);
                    if v_isShared_2681_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2680_, 1, v___x_2717_);
                        v___x_2719_ = v___x_2680_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2720_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_size_2677_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2717_);
                        v___x_2719_ = v_reuseFailAlloc_2720_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2709_;
            }
            3 => {
                return v___x_2712_;
            }
            4 => {
                return v___x_2719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(
    mut v_v_2722_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2723_: *mut crate::leanh::LeanObject,
    mut v_b_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_2723_) == 0 {
                    crate::leanh::lean_dec_ref(v_v_2722_);
                    return v_b_2724_;
                } else {
                    v_head_2725_ = crate::leanh::lean_ctor_get(v_as_x27_2723_, 0);
                    v_tail_2726_ = crate::leanh::lean_ctor_get(v_as_x27_2723_, 1);
                    crate::leanh::lean_inc_ref(v_v_2722_);
                    crate::leanh::lean_inc(v_head_2725_);
                    v___x_2727_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_2724_, v_head_2725_, v_v_2722_);
                    v_as_x27_2723_ = v_tail_2726_;
                    v_b_2724_ = v___x_2727_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(
    mut v_v_2729_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2730_: *mut crate::leanh::LeanObject,
    mut v_b_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2732_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(
        v_v_2729_,
        v_as_x27_2730_,
        v_b_2731_,
    );
    crate::leanh::lean_dec(v_as_x27_2730_);
    return v_res_2732_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_assignEqc(
    mut v_goal_2733_: *mut crate::leanh::LeanObject,
    mut v_e_2734_: *mut crate::leanh::LeanObject,
    mut v_v_2735_: *mut crate::leanh::LeanObject,
    mut v_a_2736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2737_: u8 = 0;
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2737_ = 0;
    v___x_2738_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_2733_, v_e_2734_, v___x_2737_);
    v___x_2739_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(
        v_v_2735_,
        v___x_2738_,
        v_a_2736_,
    );
    crate::leanh::lean_dec(v___x_2738_);
    return v___x_2739_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_assignEqc___boxed(
    mut v_goal_2740_: *mut crate::leanh::LeanObject,
    mut v_e_2741_: *mut crate::leanh::LeanObject,
    mut v_v_2742_: *mut crate::leanh::LeanObject,
    mut v_a_2743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2744_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_2740_, v_e_2741_, v_v_2742_, v_a_2743_);
    crate::leanh::lean_dec_ref(v_goal_2740_);
    return v_res_2744_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(
    mut v_00_u03b2_2745_: *mut crate::leanh::LeanObject,
    mut v_m_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
    mut v_b_2748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2749_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_2746_, v_a_2747_, v_b_2748_);
    return v___x_2749_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(
    mut v_v_2750_: *mut crate::leanh::LeanObject,
    mut v_as_2751_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2752_: *mut crate::leanh::LeanObject,
    mut v_b_2753_: *mut crate::leanh::LeanObject,
    mut v_a_2754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2755_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(
        v_v_2750_,
        v_as_x27_2752_,
        v_b_2753_,
    );
    return v___x_2755_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(
    mut v_v_2756_: *mut crate::leanh::LeanObject,
    mut v_as_2757_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2758_: *mut crate::leanh::LeanObject,
    mut v_b_2759_: *mut crate::leanh::LeanObject,
    mut v_a_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(
        v_v_2756_,
        v_as_2757_,
        v_as_x27_2758_,
        v_b_2759_,
        v_a_2760_,
    );
    crate::leanh::lean_dec(v_as_x27_2758_);
    crate::leanh::lean_dec(v_as_2757_);
    return v_res_2761_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(
    mut v_00_u03b2_2762_: *mut crate::leanh::LeanObject,
    mut v_a_2763_: *mut crate::leanh::LeanObject,
    mut v_x_2764_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2765_: u8 = 0;
    v___x_2765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_2763_, v_x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(
    mut v_00_u03b2_2766_: *mut crate::leanh::LeanObject,
    mut v_a_2767_: *mut crate::leanh::LeanObject,
    mut v_x_2768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2769_: u8 = 0;
    let mut v_r_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_2766_, v_a_2767_, v_x_2768_);
    crate::leanh::lean_dec(v_x_2768_);
    crate::leanh::lean_dec_ref(v_a_2767_);
    v_r_2770_ = crate::leanh::lean_box((v_res_2769_) as usize);
    return v_r_2770_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(
    mut v_00_u03b2_2771_: *mut crate::leanh::LeanObject,
    mut v_data_2772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2773_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_2772_);
    return v___x_2773_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(
    mut v_00_u03b2_2774_: *mut crate::leanh::LeanObject,
    mut v_a_2775_: *mut crate::leanh::LeanObject,
    mut v_b_2776_: *mut crate::leanh::LeanObject,
    mut v_x_2777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_2775_, v_b_2776_, v_x_2777_);
    return v___x_2778_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2779_: *mut crate::leanh::LeanObject,
    mut v_i_2780_: *mut crate::leanh::LeanObject,
    mut v_source_2781_: *mut crate::leanh::LeanObject,
    mut v_target_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2783_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_2780_, v_source_2781_, v_target_2782_);
    return v___x_2783_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2784_: *mut crate::leanh::LeanObject,
    mut v_x_2785_: *mut crate::leanh::LeanObject,
    mut v_x_2786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2785_, v_x_2786_);
    return v___x_2787_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_x_2788_: *mut crate::leanh::LeanObject,
    mut v_x_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2798_: u64 = 0;
    let mut v___x_2799_: u64 = 0;
    let mut v___x_2800_: u64 = 0;
    let mut v_fold_2801_: u64 = 0;
    let mut v___x_2802_: u64 = 0;
    let mut v___x_2803_: u64 = 0;
    let mut v___x_2804_: u64 = 0;
    let mut v___x_2805_: usize = 0;
    let mut v___x_2806_: usize = 0;
    let mut v___x_2807_: usize = 0;
    let mut v___x_2808_: usize = 0;
    let mut v___x_2809_: usize = 0;
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_2817_: u8 = 0;
    let mut v_a_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u64 = 0;
    let mut v_abs_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u64 = 0;
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2789_) == 0 {
                    return v_x_2788_;
                } else {
                    v_key_2790_ = crate::leanh::lean_ctor_get(v_x_2789_, 0);
                    v_value_2791_ = crate::leanh::lean_ctor_get(v_x_2789_, 1);
                    v_tail_2792_ = crate::leanh::lean_ctor_get(v_x_2789_, 2);
                    v_isSharedCheck_2829_ = (!crate::leanh::lean_is_exclusive(v_x_2789_)) as u8;
                    if v_isSharedCheck_2829_ == 0 {
                        v___x_2794_ = v_x_2789_;
                        v_isShared_2795_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2792_);
                        crate::leanh::lean_inc(v_value_2791_);
                        crate::leanh::lean_inc(v_key_2790_);
                        crate::leanh::lean_dec(v_x_2789_);
                        v___x_2794_ = crate::leanh::lean_box(0);
                        v_isShared_2795_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2796_ = lean_array_get_size(v_x_2788_);
                v_intZero_2816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
                v_isNeg_2817_ = lean_int_dec_lt(v_key_2790_, v_intZero_2816_);
                if v_isNeg_2817_ == 0 {
                    v_a_2818_ = lean_nat_abs(v_key_2790_);
                    v___x_2819_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2820_ = lean_nat_mul(v___x_2819_, v_a_2818_);
                    crate::leanh::lean_dec(v_a_2818_);
                    v___x_2821_ = lean_uint64_of_nat(v___x_2820_);
                    crate::leanh::lean_dec(v___x_2820_);
                    v___y_2798_ = v___x_2821_;
                    state = 2;
                    continue;
                } else {
                    v_abs_2822_ = lean_nat_abs(v_key_2790_);
                    v_one_2823_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_a_2824_ = lean_nat_sub(v_abs_2822_, v_one_2823_);
                    crate::leanh::lean_dec(v_abs_2822_);
                    v___x_2825_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2826_ = lean_nat_mul(v___x_2825_, v_a_2824_);
                    crate::leanh::lean_dec(v_a_2824_);
                    v___x_2827_ = lean_nat_add(v___x_2826_, v_one_2823_);
                    crate::leanh::lean_dec(v___x_2826_);
                    v___x_2828_ = lean_uint64_of_nat(v___x_2827_);
                    crate::leanh::lean_dec(v___x_2827_);
                    v___y_2798_ = v___x_2828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2799_ = 32u64;
                v___x_2800_ = lean_uint64_shift_right(v___y_2798_, v___x_2799_);
                v_fold_2801_ = lean_uint64_xor(v___y_2798_, v___x_2800_);
                v___x_2802_ = 16u64;
                v___x_2803_ = lean_uint64_shift_right(v_fold_2801_, v___x_2802_);
                v___x_2804_ = lean_uint64_xor(v_fold_2801_, v___x_2803_);
                v___x_2805_ = lean_uint64_to_usize(v___x_2804_);
                v___x_2806_ = lean_usize_of_nat(v___x_2796_);
                v___x_2807_ = 1usize;
                v___x_2808_ = lean_usize_sub(v___x_2806_, v___x_2807_);
                v___x_2809_ = lean_usize_land(v___x_2805_, v___x_2808_);
                v___x_2810_ = lean_array_uget_borrowed(v_x_2788_, v___x_2809_);
                crate::leanh::lean_inc(v___x_2810_);
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v___x_2810_);
                    v___x_2812_ = v___x_2794_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_key_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_value_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 2, v___x_2810_);
                    v___x_2812_ = v_reuseFailAlloc_2815_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2813_ = lean_array_uset(v_x_2788_, v___x_2809_, v___x_2812_);
                v_x_2788_ = v___x_2813_;
                v_x_2789_ = v_tail_2792_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(
    mut v_i_2830_: *mut crate::leanh::LeanObject,
    mut v_source_2831_: *mut crate::leanh::LeanObject,
    mut v_target_2832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    let mut v_es_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2833_ = lean_array_get_size(v_source_2831_);
                v___x_2834_ = lean_nat_dec_lt(v_i_2830_, v___x_2833_);
                if v___x_2834_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2831_);
                    crate::leanh::lean_dec(v_i_2830_);
                    return v_target_2832_;
                } else {
                    v_es_2835_ = lean_array_fget(v_source_2831_, v_i_2830_);
                    v___x_2836_ = crate::leanh::lean_box(0);
                    v_source_2837_ = lean_array_fset(v_source_2831_, v_i_2830_, v___x_2836_);
                    v_target_2838_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_2832_, v_es_2835_);
                    v___x_2839_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2840_ = lean_nat_add(v_i_2830_, v___x_2839_);
                    crate::leanh::lean_dec(v_i_2830_);
                    v_i_2830_ = v___x_2840_;
                    v_source_2831_ = v_source_2837_;
                    v_target_2832_ = v_target_2838_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(
    mut v_data_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2843_ = lean_array_get_size(v_data_2842_);
    v___x_2844_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2845_ = lean_nat_mul(v___x_2843_, v___x_2844_);
    v___x_2846_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2847_ = crate::leanh::lean_box(0);
    v___x_2848_ = lean_mk_array(v_nbuckets_2845_, v___x_2847_);
    v___x_2849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_2846_, v_data_2842_, v___x_2848_);
    return v___x_2849_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(
    mut v_m_2850_: *mut crate::leanh::LeanObject,
    mut v_a_2851_: *mut crate::leanh::LeanObject,
    mut v_b_2852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2857_: u64 = 0;
    let mut v___x_2858_: u64 = 0;
    let mut v___x_2859_: u64 = 0;
    let mut v_fold_2860_: u64 = 0;
    let mut v___x_2861_: u64 = 0;
    let mut v___x_2862_: u64 = 0;
    let mut v___x_2863_: u64 = 0;
    let mut v___x_2864_: usize = 0;
    let mut v___x_2865_: usize = 0;
    let mut v___x_2866_: usize = 0;
    let mut v___x_2867_: usize = 0;
    let mut v___x_2868_: usize = 0;
    let mut v_bkt_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: u8 = 0;
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2873_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: u8 = 0;
    let mut v_val_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut v_unused_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_2895_: u8 = 0;
    let mut v_a_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u64 = 0;
    let mut v_abs_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2853_ = crate::leanh::lean_ctor_get(v_m_2850_, 0);
                v_buckets_2854_ = crate::leanh::lean_ctor_get(v_m_2850_, 1);
                v___x_2855_ = lean_array_get_size(v_buckets_2854_);
                v_intZero_2894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
                v_isNeg_2895_ = lean_int_dec_lt(v_a_2851_, v_intZero_2894_);
                if v_isNeg_2895_ == 0 {
                    v_a_2896_ = lean_nat_abs(v_a_2851_);
                    v___x_2897_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2898_ = lean_nat_mul(v___x_2897_, v_a_2896_);
                    crate::leanh::lean_dec(v_a_2896_);
                    v___x_2899_ = lean_uint64_of_nat(v___x_2898_);
                    crate::leanh::lean_dec(v___x_2898_);
                    v___y_2857_ = v___x_2899_;
                    state = 1;
                    continue;
                } else {
                    v_abs_2900_ = lean_nat_abs(v_a_2851_);
                    v_one_2901_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_a_2902_ = lean_nat_sub(v_abs_2900_, v_one_2901_);
                    crate::leanh::lean_dec(v_abs_2900_);
                    v___x_2903_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2904_ = lean_nat_mul(v___x_2903_, v_a_2902_);
                    crate::leanh::lean_dec(v_a_2902_);
                    v___x_2905_ = lean_nat_add(v___x_2904_, v_one_2901_);
                    crate::leanh::lean_dec(v___x_2904_);
                    v___x_2906_ = lean_uint64_of_nat(v___x_2905_);
                    crate::leanh::lean_dec(v___x_2905_);
                    v___y_2857_ = v___x_2906_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2858_ = 32u64;
                v___x_2859_ = lean_uint64_shift_right(v___y_2857_, v___x_2858_);
                v_fold_2860_ = lean_uint64_xor(v___y_2857_, v___x_2859_);
                v___x_2861_ = 16u64;
                v___x_2862_ = lean_uint64_shift_right(v_fold_2860_, v___x_2861_);
                v___x_2863_ = lean_uint64_xor(v_fold_2860_, v___x_2862_);
                v___x_2864_ = lean_uint64_to_usize(v___x_2863_);
                v___x_2865_ = lean_usize_of_nat(v___x_2855_);
                v___x_2866_ = 1usize;
                v___x_2867_ = lean_usize_sub(v___x_2865_, v___x_2866_);
                v___x_2868_ = lean_usize_land(v___x_2864_, v___x_2867_);
                v_bkt_2869_ = lean_array_uget_borrowed(v_buckets_2854_, v___x_2868_);
                v___x_2870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_2851_, v_bkt_2869_);
                if v___x_2870_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2854_);
                    crate::leanh::lean_inc(v_size_2853_);
                    v_isSharedCheck_2891_ = (!crate::leanh::lean_is_exclusive(v_m_2850_)) as u8;
                    if v_isSharedCheck_2891_ == 0 {
                        v_unused_2892_ = crate::leanh::lean_ctor_get(v_m_2850_, 1);
                        crate::leanh::lean_dec(v_unused_2892_);
                        v_unused_2893_ = crate::leanh::lean_ctor_get(v_m_2850_, 0);
                        crate::leanh::lean_dec(v_unused_2893_);
                        v___x_2872_ = v_m_2850_;
                        v_isShared_2873_ = v_isSharedCheck_2891_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2850_);
                        v___x_2872_ = crate::leanh::lean_box(0);
                        v_isShared_2873_ = v_isSharedCheck_2891_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2852_);
                    crate::leanh::lean_dec(v_a_2851_);
                    return v_m_2850_;
                }
            }
            2 => {
                v___x_2874_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2875_ = lean_nat_add(v_size_2853_, v___x_2874_);
                crate::leanh::lean_dec(v_size_2853_);
                crate::leanh::lean_inc(v_bkt_2869_);
                v___x_2876_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2876_, 0, v_a_2851_);
                crate::leanh::lean_ctor_set(v___x_2876_, 1, v_b_2852_);
                crate::leanh::lean_ctor_set(v___x_2876_, 2, v_bkt_2869_);
                v_buckets_x27_2877_ = lean_array_uset(v_buckets_2854_, v___x_2868_, v___x_2876_);
                v___x_2878_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2879_ = lean_nat_mul(v_size_x27_2875_, v___x_2878_);
                v___x_2880_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2881_ = lean_nat_div(v___x_2879_, v___x_2880_);
                crate::leanh::lean_dec(v___x_2879_);
                v___x_2882_ = lean_array_get_size(v_buckets_x27_2877_);
                v___x_2883_ = lean_nat_dec_le(v___x_2881_, v___x_2882_);
                crate::leanh::lean_dec(v___x_2881_);
                if v___x_2883_ == 0 {
                    v_val_2884_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_2877_);
                    if v_isShared_2873_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2872_, 1, v_val_2884_);
                        crate::leanh::lean_ctor_set(v___x_2872_, 0, v_size_x27_2875_);
                        v___x_2886_ = v___x_2872_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_size_x27_2875_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_val_2884_);
                        v___x_2886_ = v_reuseFailAlloc_2887_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2873_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2872_, 1, v_buckets_x27_2877_);
                        crate::leanh::lean_ctor_set(v___x_2872_, 0, v_size_x27_2875_);
                        v___x_2889_ = v___x_2872_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2890_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_size_x27_2875_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_buckets_x27_2877_);
                        v___x_2889_ = v_reuseFailAlloc_2890_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2886_;
            }
            4 => {
                return v___x_2889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(
    mut v_goal_2907_: *mut crate::leanh::LeanObject,
    mut v_isTarget_2908_: *mut crate::leanh::LeanObject,
    mut v_as_2909_: *mut crate::leanh::LeanObject,
    mut v_sz_2910_: usize,
    mut v_i_2911_: usize,
    mut v_b_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
    mut v___y_2915_: *mut crate::leanh::LeanObject,
    mut v___y_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2923_: u8 = 0;
    let mut v_a_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_fst_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: usize = 0;
    let mut v_reuseFailAlloc_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v_isSharedCheck_2991_: u8 = 0;
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut v_unused_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_unused_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2918_ = lean_usize_dec_lt(v_i_2911_, v_sz_2910_);
                if v___x_2918_ == 0 {
                    crate::leanh::lean_dec_ref(v_isTarget_2908_);
                    v___x_2919_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2919_, 0, v_b_2912_);
                    return v___x_2919_;
                } else {
                    v_snd_2920_ = crate::leanh::lean_ctor_get(v_b_2912_, 1);
                    v_isSharedCheck_3002_ = (!crate::leanh::lean_is_exclusive(v_b_2912_)) as u8;
                    if v_isSharedCheck_3002_ == 0 {
                        v_unused_3003_ = crate::leanh::lean_ctor_get(v_b_2912_, 0);
                        crate::leanh::lean_dec(v_unused_3003_);
                        v___x_2922_ = v_b_2912_;
                        v_isShared_2923_ = v_isSharedCheck_3002_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2920_);
                        crate::leanh::lean_dec(v_b_2912_);
                        v___x_2922_ = crate::leanh::lean_box(0);
                        v_isShared_2923_ = v_isSharedCheck_3002_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2924_ = lean_array_uget_borrowed(v_as_2909_, v_i_2911_);
                crate::leanh::lean_inc(v_a_2924_);
                v___x_2925_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_2907_,
                    v_a_2924_,
                    v___y_2913_,
                    v___y_2914_,
                    v___y_2915_,
                    v___y_2916_,
                );
                if crate::leanh::lean_obj_tag(v___x_2925_) == 0 {
                    v_snd_2926_ = crate::leanh::lean_ctor_get(v_snd_2920_, 1);
                    crate::leanh::lean_inc(v_snd_2926_);
                    v_a_2927_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
                    crate::leanh::lean_inc(v_a_2927_);
                    crate::leanh::lean_dec_ref_known(v___x_2925_, 1);
                    v_fst_2928_ = crate::leanh::lean_ctor_get(v_snd_2920_, 0);
                    v_isSharedCheck_2992_ = (!crate::leanh::lean_is_exclusive(v_snd_2920_)) as u8;
                    if v_isSharedCheck_2992_ == 0 {
                        v_unused_2993_ = crate::leanh::lean_ctor_get(v_snd_2920_, 1);
                        crate::leanh::lean_dec(v_unused_2993_);
                        v___x_2930_ = v_snd_2920_;
                        v_isShared_2931_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2928_);
                        crate::leanh::lean_dec(v_snd_2920_);
                        v___x_2930_ = crate::leanh::lean_box(0);
                        v_isShared_2931_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2922_);
                    crate::leanh::lean_dec(v_snd_2920_);
                    crate::leanh::lean_dec_ref(v_isTarget_2908_);
                    v_a_2994_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
                    v_isSharedCheck_3001_ = (!crate::leanh::lean_is_exclusive(v___x_2925_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2996_ = v___x_2925_;
                        v_isShared_2997_ = v_isSharedCheck_3001_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2994_);
                        crate::leanh::lean_dec(v___x_2925_);
                        v___x_2996_ = crate::leanh::lean_box(0);
                        v_isShared_2997_ = v_isSharedCheck_3001_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_2932_ = crate::leanh::lean_ctor_get(v_snd_2926_, 0);
                v_snd_2933_ = crate::leanh::lean_ctor_get(v_snd_2926_, 1);
                v_isSharedCheck_2991_ = (!crate::leanh::lean_is_exclusive(v_snd_2926_)) as u8;
                if v_isSharedCheck_2991_ == 0 {
                    v___x_2935_ = v_snd_2926_;
                    v_isShared_2936_ = v_isSharedCheck_2991_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2933_);
                    crate::leanh::lean_inc(v_fst_2932_);
                    crate::leanh::lean_dec(v_snd_2926_);
                    v___x_2935_ = crate::leanh::lean_box(0);
                    v_isShared_2936_ = v_isSharedCheck_2991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2937_ = crate::leanh::lean_box(0);
                v___x_2946_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2927_);
                if v___x_2946_ == 0 {
                    crate::leanh::lean_dec(v_a_2927_);
                    if v_isShared_2931_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2930_, 1, v_snd_2933_);
                        crate::leanh::lean_ctor_set(v___x_2930_, 0, v_fst_2932_);
                        v___x_2948_ = v___x_2930_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_fst_2932_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_snd_2933_);
                        v___x_2948_ = v_reuseFailAlloc_2952_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_isTarget_2908_);
                    crate::leanh::lean_inc(v___y_2916_);
                    crate::leanh::lean_inc_ref(v___y_2915_);
                    crate::leanh::lean_inc(v___y_2914_);
                    crate::leanh::lean_inc_ref(v___y_2913_);
                    crate::leanh::lean_inc(v_a_2927_);
                    v___x_2953_ = crate::leanh::lean_apply_6(
                        v_isTarget_2908_,
                        v_a_2927_,
                        v___y_2913_,
                        v___y_2914_,
                        v___y_2915_,
                        v___y_2916_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2953_) == 0 {
                        v_a_2954_ = crate::leanh::lean_ctor_get(v___x_2953_, 0);
                        crate::leanh::lean_inc(v_a_2954_);
                        crate::leanh::lean_dec_ref_known(v___x_2953_, 1);
                        v___x_2955_ = (crate::leanh::lean_unbox(v_a_2954_) as u8);
                        crate::leanh::lean_dec(v_a_2954_);
                        if v___x_2955_ == 0 {
                            crate::leanh::lean_dec(v_a_2927_);
                            if v_isShared_2931_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2930_, 1, v_snd_2933_);
                                crate::leanh::lean_ctor_set(v___x_2930_, 0, v_fst_2932_);
                                v___x_2957_ = v___x_2930_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_2961_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_fst_2932_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_snd_2933_);
                                v___x_2957_ = v_reuseFailAlloc_2961_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_self_2962_ = crate::leanh::lean_ctor_get(v_a_2927_, 0);
                            crate::leanh::lean_inc_ref(v_self_2962_);
                            crate::leanh::lean_dec(v_a_2927_);
                            v___x_2963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_2933_, v_self_2962_);
                            if crate::leanh::lean_obj_tag(v___x_2963_) == 0 {
                                v___x_2964_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_2907_, v_snd_2933_, v_self_2962_, v_fst_2932_, v_fst_2928_);
                                crate::leanh::lean_inc_n(v___x_2964_, 2);
                                v___x_2965_ = l_Rat_ofInt(v___x_2964_);
                                v___x_2966_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_2907_,
                                    v_self_2962_,
                                    v___x_2965_,
                                    v_snd_2933_,
                                );
                                v___x_2967_ = crate::leanh::lean_box(0);
                                v___x_2968_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_2932_, v___x_2964_, v___x_2967_);
                                v___x_2969_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                                v___x_2970_ = lean_int_add(v___x_2964_, v___x_2969_);
                                crate::leanh::lean_dec(v___x_2964_);
                                if v_isShared_2931_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2930_, 1, v___x_2966_);
                                    crate::leanh::lean_ctor_set(v___x_2930_, 0, v___x_2968_);
                                    v___x_2972_ = v___x_2930_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2976_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2976_,
                                        0,
                                        v___x_2968_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2976_,
                                        1,
                                        v___x_2966_,
                                    );
                                    v___x_2972_ = v_reuseFailAlloc_2976_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2963_, 1);
                                crate::leanh::lean_dec_ref(v_self_2962_);
                                if v_isShared_2931_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2930_, 1, v_snd_2933_);
                                    crate::leanh::lean_ctor_set(v___x_2930_, 0, v_fst_2932_);
                                    v___x_2978_ = v___x_2930_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2982_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2982_,
                                        0,
                                        v_fst_2932_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2982_,
                                        1,
                                        v_snd_2933_,
                                    );
                                    v___x_2978_ = v_reuseFailAlloc_2982_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2935_);
                        crate::leanh::lean_dec(v_snd_2933_);
                        crate::leanh::lean_dec(v_fst_2932_);
                        crate::leanh::lean_del_object(v___x_2930_);
                        crate::leanh::lean_dec(v_fst_2928_);
                        crate::leanh::lean_dec(v_a_2927_);
                        crate::leanh::lean_del_object(v___x_2922_);
                        crate::leanh::lean_dec_ref(v_isTarget_2908_);
                        v_a_2983_ = crate::leanh::lean_ctor_get(v___x_2953_, 0);
                        v_isSharedCheck_2990_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2953_)) as u8;
                        if v_isSharedCheck_2990_ == 0 {
                            v___x_2985_ = v___x_2953_;
                            v_isShared_2986_ = v_isSharedCheck_2990_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2983_);
                            crate::leanh::lean_dec(v___x_2953_);
                            v___x_2985_ = crate::leanh::lean_box(0);
                            v_isShared_2986_ = v_isSharedCheck_2990_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_2936_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2935_, 1, v_a_2939_);
                    crate::leanh::lean_ctor_set(v___x_2935_, 0, v___x_2937_);
                    v___x_2941_ = v___x_2935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2945_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_a_2939_);
                    v___x_2941_ = v_reuseFailAlloc_2945_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2942_ = 1usize;
                v___x_2943_ = lean_usize_add(v_i_2911_, v___x_2942_);
                v_i_2911_ = v___x_2943_;
                v_b_2912_ = v___x_2941_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2922_, 1, v___x_2948_);
                    crate::leanh::lean_ctor_set(v___x_2922_, 0, v_fst_2928_);
                    v___x_2950_ = v___x_2922_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_fst_2928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2948_);
                    v___x_2950_ = v_reuseFailAlloc_2951_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_2939_ = v___x_2950_;
                state = 4;
                continue;
            }
            8 => {
                if v_isShared_2923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2922_, 1, v___x_2957_);
                    crate::leanh::lean_ctor_set(v___x_2922_, 0, v_fst_2928_);
                    v___x_2959_ = v___x_2922_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_fst_2928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2957_);
                    v___x_2959_ = v_reuseFailAlloc_2960_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_2939_ = v___x_2959_;
                state = 4;
                continue;
            }
            10 => {
                if v_isShared_2923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2922_, 1, v___x_2972_);
                    crate::leanh::lean_ctor_set(v___x_2922_, 0, v___x_2970_);
                    v___x_2974_ = v___x_2922_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2972_);
                    v___x_2974_ = v_reuseFailAlloc_2975_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_2939_ = v___x_2974_;
                state = 4;
                continue;
            }
            12 => {
                if v_isShared_2923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2922_, 1, v___x_2978_);
                    crate::leanh::lean_ctor_set(v___x_2922_, 0, v_fst_2928_);
                    v___x_2980_ = v___x_2922_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_fst_2928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2978_);
                    v___x_2980_ = v_reuseFailAlloc_2981_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_2939_ = v___x_2980_;
                state = 4;
                continue;
            }
            14 => {
                if v_isShared_2986_ == 0 {
                    v___x_2988_ = v___x_2985_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
                    v___x_2988_ = v_reuseFailAlloc_2989_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2988_;
            }
            16 => {
                if v_isShared_2997_ == 0 {
                    v___x_2999_ = v___x_2996_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3000_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
                    v___x_2999_ = v_reuseFailAlloc_3000_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(
    mut v_goal_3004_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3005_: *mut crate::leanh::LeanObject,
    mut v_as_3006_: *mut crate::leanh::LeanObject,
    mut v_sz_3007_: *mut crate::leanh::LeanObject,
    mut v_i_3008_: *mut crate::leanh::LeanObject,
    mut v_b_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3015_: usize = 0;
    let mut v_i_boxed_3016_: usize = 0;
    let mut v_res_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3015_ = crate::leanh::lean_unbox_usize(v_sz_3007_);
    crate::leanh::lean_dec(v_sz_3007_);
    v_i_boxed_3016_ = crate::leanh::lean_unbox_usize(v_i_3008_);
    crate::leanh::lean_dec(v_i_3008_);
    v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_3004_, v_isTarget_3005_, v_as_3006_, v_sz_boxed_3015_, v_i_boxed_3016_, v_b_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
    crate::leanh::lean_dec(v___y_3013_);
    crate::leanh::lean_dec_ref(v___y_3012_);
    crate::leanh::lean_dec(v___y_3011_);
    crate::leanh::lean_dec_ref(v___y_3010_);
    crate::leanh::lean_dec_ref(v_as_3006_);
    crate::leanh::lean_dec_ref(v_goal_3004_);
    return v_res_3017_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(
    mut v_goal_3018_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3019_: *mut crate::leanh::LeanObject,
    mut v_as_3020_: *mut crate::leanh::LeanObject,
    mut v_sz_3021_: usize,
    mut v_i_3022_: usize,
    mut v_b_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
    mut v___y_3026_: *mut crate::leanh::LeanObject,
    mut v___y_3027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3029_: u8 = 0;
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v_a_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3042_: u8 = 0;
    let mut v_fst_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: usize = 0;
    let mut v___x_3054_: usize = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut v_isSharedCheck_3103_: u8 = 0;
    let mut v_unused_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3108_: u8 = 0;
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_unused_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3029_ = lean_usize_dec_lt(v_i_3022_, v_sz_3021_);
                if v___x_3029_ == 0 {
                    crate::leanh::lean_dec_ref(v_isTarget_3019_);
                    v___x_3030_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3030_, 0, v_b_3023_);
                    return v___x_3030_;
                } else {
                    v_snd_3031_ = crate::leanh::lean_ctor_get(v_b_3023_, 1);
                    v_isSharedCheck_3113_ = (!crate::leanh::lean_is_exclusive(v_b_3023_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v_unused_3114_ = crate::leanh::lean_ctor_get(v_b_3023_, 0);
                        crate::leanh::lean_dec(v_unused_3114_);
                        v___x_3033_ = v_b_3023_;
                        v_isShared_3034_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3031_);
                        crate::leanh::lean_dec(v_b_3023_);
                        v___x_3033_ = crate::leanh::lean_box(0);
                        v_isShared_3034_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3035_ = lean_array_uget_borrowed(v_as_3020_, v_i_3022_);
                crate::leanh::lean_inc(v_a_3035_);
                v___x_3036_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3018_,
                    v_a_3035_,
                    v___y_3024_,
                    v___y_3025_,
                    v___y_3026_,
                    v___y_3027_,
                );
                if crate::leanh::lean_obj_tag(v___x_3036_) == 0 {
                    v_snd_3037_ = crate::leanh::lean_ctor_get(v_snd_3031_, 1);
                    crate::leanh::lean_inc(v_snd_3037_);
                    v_a_3038_ = crate::leanh::lean_ctor_get(v___x_3036_, 0);
                    crate::leanh::lean_inc(v_a_3038_);
                    crate::leanh::lean_dec_ref_known(v___x_3036_, 1);
                    v_fst_3039_ = crate::leanh::lean_ctor_get(v_snd_3031_, 0);
                    v_isSharedCheck_3103_ = (!crate::leanh::lean_is_exclusive(v_snd_3031_)) as u8;
                    if v_isSharedCheck_3103_ == 0 {
                        v_unused_3104_ = crate::leanh::lean_ctor_get(v_snd_3031_, 1);
                        crate::leanh::lean_dec(v_unused_3104_);
                        v___x_3041_ = v_snd_3031_;
                        v_isShared_3042_ = v_isSharedCheck_3103_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3039_);
                        crate::leanh::lean_dec(v_snd_3031_);
                        v___x_3041_ = crate::leanh::lean_box(0);
                        v_isShared_3042_ = v_isSharedCheck_3103_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3033_);
                    crate::leanh::lean_dec(v_snd_3031_);
                    crate::leanh::lean_dec_ref(v_isTarget_3019_);
                    v_a_3105_ = crate::leanh::lean_ctor_get(v___x_3036_, 0);
                    v_isSharedCheck_3112_ = (!crate::leanh::lean_is_exclusive(v___x_3036_)) as u8;
                    if v_isSharedCheck_3112_ == 0 {
                        v___x_3107_ = v___x_3036_;
                        v_isShared_3108_ = v_isSharedCheck_3112_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3105_);
                        crate::leanh::lean_dec(v___x_3036_);
                        v___x_3107_ = crate::leanh::lean_box(0);
                        v_isShared_3108_ = v_isSharedCheck_3112_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3043_ = crate::leanh::lean_ctor_get(v_snd_3037_, 0);
                v_snd_3044_ = crate::leanh::lean_ctor_get(v_snd_3037_, 1);
                v_isSharedCheck_3102_ = (!crate::leanh::lean_is_exclusive(v_snd_3037_)) as u8;
                if v_isSharedCheck_3102_ == 0 {
                    v___x_3046_ = v_snd_3037_;
                    v_isShared_3047_ = v_isSharedCheck_3102_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3044_);
                    crate::leanh::lean_inc(v_fst_3043_);
                    crate::leanh::lean_dec(v_snd_3037_);
                    v___x_3046_ = crate::leanh::lean_box(0);
                    v_isShared_3047_ = v_isSharedCheck_3102_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3048_ = crate::leanh::lean_box(0);
                v___x_3057_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3038_);
                if v___x_3057_ == 0 {
                    crate::leanh::lean_dec(v_a_3038_);
                    if v_isShared_3042_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3041_, 1, v_snd_3044_);
                        crate::leanh::lean_ctor_set(v___x_3041_, 0, v_fst_3043_);
                        v___x_3059_ = v___x_3041_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_fst_3043_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_snd_3044_);
                        v___x_3059_ = v_reuseFailAlloc_3063_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_isTarget_3019_);
                    crate::leanh::lean_inc(v___y_3027_);
                    crate::leanh::lean_inc_ref(v___y_3026_);
                    crate::leanh::lean_inc(v___y_3025_);
                    crate::leanh::lean_inc_ref(v___y_3024_);
                    crate::leanh::lean_inc(v_a_3038_);
                    v___x_3064_ = crate::leanh::lean_apply_6(
                        v_isTarget_3019_,
                        v_a_3038_,
                        v___y_3024_,
                        v___y_3025_,
                        v___y_3026_,
                        v___y_3027_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3064_) == 0 {
                        v_a_3065_ = crate::leanh::lean_ctor_get(v___x_3064_, 0);
                        crate::leanh::lean_inc(v_a_3065_);
                        crate::leanh::lean_dec_ref_known(v___x_3064_, 1);
                        v___x_3066_ = (crate::leanh::lean_unbox(v_a_3065_) as u8);
                        crate::leanh::lean_dec(v_a_3065_);
                        if v___x_3066_ == 0 {
                            crate::leanh::lean_dec(v_a_3038_);
                            if v_isShared_3042_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3041_, 1, v_snd_3044_);
                                crate::leanh::lean_ctor_set(v___x_3041_, 0, v_fst_3043_);
                                v___x_3068_ = v___x_3041_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_3072_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_fst_3043_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_snd_3044_);
                                v___x_3068_ = v_reuseFailAlloc_3072_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_self_3073_ = crate::leanh::lean_ctor_get(v_a_3038_, 0);
                            crate::leanh::lean_inc_ref(v_self_3073_);
                            crate::leanh::lean_dec(v_a_3038_);
                            v___x_3074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_3044_, v_self_3073_);
                            if crate::leanh::lean_obj_tag(v___x_3074_) == 0 {
                                v___x_3075_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_3018_, v_snd_3044_, v_self_3073_, v_fst_3043_, v_fst_3039_);
                                crate::leanh::lean_inc_n(v___x_3075_, 2);
                                v___x_3076_ = l_Rat_ofInt(v___x_3075_);
                                v___x_3077_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3018_,
                                    v_self_3073_,
                                    v___x_3076_,
                                    v_snd_3044_,
                                );
                                v___x_3078_ = crate::leanh::lean_box(0);
                                v___x_3079_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_3043_, v___x_3075_, v___x_3078_);
                                v___x_3080_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                                v___x_3081_ = lean_int_add(v___x_3075_, v___x_3080_);
                                crate::leanh::lean_dec(v___x_3075_);
                                if v_isShared_3042_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3041_, 1, v___x_3077_);
                                    crate::leanh::lean_ctor_set(v___x_3041_, 0, v___x_3079_);
                                    v___x_3083_ = v___x_3041_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3087_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3087_,
                                        0,
                                        v___x_3079_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3087_,
                                        1,
                                        v___x_3077_,
                                    );
                                    v___x_3083_ = v_reuseFailAlloc_3087_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_3074_, 1);
                                crate::leanh::lean_dec_ref(v_self_3073_);
                                if v_isShared_3042_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3041_, 1, v_snd_3044_);
                                    crate::leanh::lean_ctor_set(v___x_3041_, 0, v_fst_3043_);
                                    v___x_3089_ = v___x_3041_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3093_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3093_,
                                        0,
                                        v_fst_3043_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3093_,
                                        1,
                                        v_snd_3044_,
                                    );
                                    v___x_3089_ = v_reuseFailAlloc_3093_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3046_);
                        crate::leanh::lean_dec(v_snd_3044_);
                        crate::leanh::lean_dec(v_fst_3043_);
                        crate::leanh::lean_del_object(v___x_3041_);
                        crate::leanh::lean_dec(v_fst_3039_);
                        crate::leanh::lean_dec(v_a_3038_);
                        crate::leanh::lean_del_object(v___x_3033_);
                        crate::leanh::lean_dec_ref(v_isTarget_3019_);
                        v_a_3094_ = crate::leanh::lean_ctor_get(v___x_3064_, 0);
                        v_isSharedCheck_3101_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3064_)) as u8;
                        if v_isSharedCheck_3101_ == 0 {
                            v___x_3096_ = v___x_3064_;
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3094_);
                            crate::leanh::lean_dec(v___x_3064_);
                            v___x_3096_ = crate::leanh::lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3047_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3046_, 1, v_a_3050_);
                    crate::leanh::lean_ctor_set(v___x_3046_, 0, v___x_3048_);
                    v___x_3052_ = v___x_3046_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_a_3050_);
                    v___x_3052_ = v_reuseFailAlloc_3056_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3053_ = 1usize;
                v___x_3054_ = lean_usize_add(v_i_3022_, v___x_3053_);
                v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_3018_, v_isTarget_3019_, v_as_3020_, v_sz_3021_, v___x_3054_, v___x_3052_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
                return v___x_3055_;
            }
            6 => {
                if v_isShared_3034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3033_, 1, v___x_3059_);
                    crate::leanh::lean_ctor_set(v___x_3033_, 0, v_fst_3039_);
                    v___x_3061_ = v___x_3033_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_fst_3039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3059_);
                    v___x_3061_ = v_reuseFailAlloc_3062_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_3050_ = v___x_3061_;
                state = 4;
                continue;
            }
            8 => {
                if v_isShared_3034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3033_, 1, v___x_3068_);
                    crate::leanh::lean_ctor_set(v___x_3033_, 0, v_fst_3039_);
                    v___x_3070_ = v___x_3033_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_fst_3039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_3068_);
                    v___x_3070_ = v_reuseFailAlloc_3071_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_3050_ = v___x_3070_;
                state = 4;
                continue;
            }
            10 => {
                if v_isShared_3034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3033_, 1, v___x_3083_);
                    crate::leanh::lean_ctor_set(v___x_3033_, 0, v___x_3081_);
                    v___x_3085_ = v___x_3033_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3086_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3083_);
                    v___x_3085_ = v_reuseFailAlloc_3086_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_3050_ = v___x_3085_;
                state = 4;
                continue;
            }
            12 => {
                if v_isShared_3034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3033_, 1, v___x_3089_);
                    crate::leanh::lean_ctor_set(v___x_3033_, 0, v_fst_3039_);
                    v___x_3091_ = v___x_3033_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_fst_3039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3089_);
                    v___x_3091_ = v_reuseFailAlloc_3092_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_3050_ = v___x_3091_;
                state = 4;
                continue;
            }
            14 => {
                if v_isShared_3097_ == 0 {
                    v___x_3099_ = v___x_3096_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3099_;
            }
            16 => {
                if v_isShared_3108_ == 0 {
                    v___x_3110_ = v___x_3107_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
                    v___x_3110_ = v_reuseFailAlloc_3111_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(
    mut v_goal_3115_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3116_: *mut crate::leanh::LeanObject,
    mut v_as_3117_: *mut crate::leanh::LeanObject,
    mut v_sz_3118_: *mut crate::leanh::LeanObject,
    mut v_i_3119_: *mut crate::leanh::LeanObject,
    mut v_b_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3126_: usize = 0;
    let mut v_i_boxed_3127_: usize = 0;
    let mut v_res_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3126_ = crate::leanh::lean_unbox_usize(v_sz_3118_);
    crate::leanh::lean_dec(v_sz_3118_);
    v_i_boxed_3127_ = crate::leanh::lean_unbox_usize(v_i_3119_);
    crate::leanh::lean_dec(v_i_3119_);
    v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_3115_, v_isTarget_3116_, v_as_3117_, v_sz_boxed_3126_, v_i_boxed_3127_, v_b_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
    crate::leanh::lean_dec(v___y_3124_);
    crate::leanh::lean_dec_ref(v___y_3123_);
    crate::leanh::lean_dec(v___y_3122_);
    crate::leanh::lean_dec_ref(v___y_3121_);
    crate::leanh::lean_dec_ref(v_as_3117_);
    crate::leanh::lean_dec_ref(v_goal_3115_);
    return v_res_3128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(
    mut v_goal_3129_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3130_: *mut crate::leanh::LeanObject,
    mut v_as_3131_: *mut crate::leanh::LeanObject,
    mut v_sz_3132_: usize,
    mut v_i_3133_: usize,
    mut v_b_3134_: *mut crate::leanh::LeanObject,
    mut v___y_3135_: *mut crate::leanh::LeanObject,
    mut v___y_3136_: *mut crate::leanh::LeanObject,
    mut v___y_3137_: *mut crate::leanh::LeanObject,
    mut v___y_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3145_: u8 = 0;
    let mut v_a_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3153_: u8 = 0;
    let mut v_fst_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3158_: u8 = 0;
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: usize = 0;
    let mut v___x_3165_: usize = 0;
    let mut v_reuseFailAlloc_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut v_unused_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v_isSharedCheck_3224_: u8 = 0;
    let mut v_unused_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3140_ = lean_usize_dec_lt(v_i_3133_, v_sz_3132_);
                if v___x_3140_ == 0 {
                    crate::leanh::lean_dec_ref(v_isTarget_3130_);
                    v___x_3141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3141_, 0, v_b_3134_);
                    return v___x_3141_;
                } else {
                    v_snd_3142_ = crate::leanh::lean_ctor_get(v_b_3134_, 1);
                    v_isSharedCheck_3224_ = (!crate::leanh::lean_is_exclusive(v_b_3134_)) as u8;
                    if v_isSharedCheck_3224_ == 0 {
                        v_unused_3225_ = crate::leanh::lean_ctor_get(v_b_3134_, 0);
                        crate::leanh::lean_dec(v_unused_3225_);
                        v___x_3144_ = v_b_3134_;
                        v_isShared_3145_ = v_isSharedCheck_3224_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3142_);
                        crate::leanh::lean_dec(v_b_3134_);
                        v___x_3144_ = crate::leanh::lean_box(0);
                        v_isShared_3145_ = v_isSharedCheck_3224_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3146_ = lean_array_uget_borrowed(v_as_3131_, v_i_3133_);
                crate::leanh::lean_inc(v_a_3146_);
                v___x_3147_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3129_,
                    v_a_3146_,
                    v___y_3135_,
                    v___y_3136_,
                    v___y_3137_,
                    v___y_3138_,
                );
                if crate::leanh::lean_obj_tag(v___x_3147_) == 0 {
                    v_snd_3148_ = crate::leanh::lean_ctor_get(v_snd_3142_, 1);
                    crate::leanh::lean_inc(v_snd_3148_);
                    v_a_3149_ = crate::leanh::lean_ctor_get(v___x_3147_, 0);
                    crate::leanh::lean_inc(v_a_3149_);
                    crate::leanh::lean_dec_ref_known(v___x_3147_, 1);
                    v_fst_3150_ = crate::leanh::lean_ctor_get(v_snd_3142_, 0);
                    v_isSharedCheck_3214_ = (!crate::leanh::lean_is_exclusive(v_snd_3142_)) as u8;
                    if v_isSharedCheck_3214_ == 0 {
                        v_unused_3215_ = crate::leanh::lean_ctor_get(v_snd_3142_, 1);
                        crate::leanh::lean_dec(v_unused_3215_);
                        v___x_3152_ = v_snd_3142_;
                        v_isShared_3153_ = v_isSharedCheck_3214_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3150_);
                        crate::leanh::lean_dec(v_snd_3142_);
                        v___x_3152_ = crate::leanh::lean_box(0);
                        v_isShared_3153_ = v_isSharedCheck_3214_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3144_);
                    crate::leanh::lean_dec(v_snd_3142_);
                    crate::leanh::lean_dec_ref(v_isTarget_3130_);
                    v_a_3216_ = crate::leanh::lean_ctor_get(v___x_3147_, 0);
                    v_isSharedCheck_3223_ = (!crate::leanh::lean_is_exclusive(v___x_3147_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3218_ = v___x_3147_;
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3216_);
                        crate::leanh::lean_dec(v___x_3147_);
                        v___x_3218_ = crate::leanh::lean_box(0);
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3154_ = crate::leanh::lean_ctor_get(v_snd_3148_, 0);
                v_snd_3155_ = crate::leanh::lean_ctor_get(v_snd_3148_, 1);
                v_isSharedCheck_3213_ = (!crate::leanh::lean_is_exclusive(v_snd_3148_)) as u8;
                if v_isSharedCheck_3213_ == 0 {
                    v___x_3157_ = v_snd_3148_;
                    v_isShared_3158_ = v_isSharedCheck_3213_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3155_);
                    crate::leanh::lean_inc(v_fst_3154_);
                    crate::leanh::lean_dec(v_snd_3148_);
                    v___x_3157_ = crate::leanh::lean_box(0);
                    v_isShared_3158_ = v_isSharedCheck_3213_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3159_ = crate::leanh::lean_box(0);
                v___x_3168_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3149_);
                if v___x_3168_ == 0 {
                    crate::leanh::lean_dec(v_a_3149_);
                    if v_isShared_3153_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3152_, 1, v_snd_3155_);
                        crate::leanh::lean_ctor_set(v___x_3152_, 0, v_fst_3154_);
                        v___x_3170_ = v___x_3152_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3174_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_fst_3154_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_snd_3155_);
                        v___x_3170_ = v_reuseFailAlloc_3174_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_isTarget_3130_);
                    crate::leanh::lean_inc(v___y_3138_);
                    crate::leanh::lean_inc_ref(v___y_3137_);
                    crate::leanh::lean_inc(v___y_3136_);
                    crate::leanh::lean_inc_ref(v___y_3135_);
                    crate::leanh::lean_inc(v_a_3149_);
                    v___x_3175_ = crate::leanh::lean_apply_6(
                        v_isTarget_3130_,
                        v_a_3149_,
                        v___y_3135_,
                        v___y_3136_,
                        v___y_3137_,
                        v___y_3138_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3175_) == 0 {
                        v_a_3176_ = crate::leanh::lean_ctor_get(v___x_3175_, 0);
                        crate::leanh::lean_inc(v_a_3176_);
                        crate::leanh::lean_dec_ref_known(v___x_3175_, 1);
                        v___x_3177_ = (crate::leanh::lean_unbox(v_a_3176_) as u8);
                        crate::leanh::lean_dec(v_a_3176_);
                        if v___x_3177_ == 0 {
                            crate::leanh::lean_dec(v_a_3149_);
                            if v_isShared_3153_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3152_, 1, v_snd_3155_);
                                crate::leanh::lean_ctor_set(v___x_3152_, 0, v_fst_3154_);
                                v___x_3179_ = v___x_3152_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_3183_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_fst_3154_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_snd_3155_);
                                v___x_3179_ = v_reuseFailAlloc_3183_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_self_3184_ = crate::leanh::lean_ctor_get(v_a_3149_, 0);
                            crate::leanh::lean_inc_ref(v_self_3184_);
                            crate::leanh::lean_dec(v_a_3149_);
                            v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_3155_, v_self_3184_);
                            if crate::leanh::lean_obj_tag(v___x_3185_) == 0 {
                                v___x_3186_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_3129_, v_snd_3155_, v_self_3184_, v_fst_3154_, v_fst_3150_);
                                crate::leanh::lean_inc_n(v___x_3186_, 2);
                                v___x_3187_ = l_Rat_ofInt(v___x_3186_);
                                v___x_3188_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3129_,
                                    v_self_3184_,
                                    v___x_3187_,
                                    v_snd_3155_,
                                );
                                v___x_3189_ = crate::leanh::lean_box(0);
                                v___x_3190_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_3154_, v___x_3186_, v___x_3189_);
                                v___x_3191_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                                v___x_3192_ = lean_int_add(v___x_3186_, v___x_3191_);
                                crate::leanh::lean_dec(v___x_3186_);
                                if v_isShared_3153_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3152_, 1, v___x_3188_);
                                    crate::leanh::lean_ctor_set(v___x_3152_, 0, v___x_3190_);
                                    v___x_3194_ = v___x_3152_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3198_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3198_,
                                        0,
                                        v___x_3190_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3198_,
                                        1,
                                        v___x_3188_,
                                    );
                                    v___x_3194_ = v_reuseFailAlloc_3198_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_3185_, 1);
                                crate::leanh::lean_dec_ref(v_self_3184_);
                                if v_isShared_3153_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3152_, 1, v_snd_3155_);
                                    crate::leanh::lean_ctor_set(v___x_3152_, 0, v_fst_3154_);
                                    v___x_3200_ = v___x_3152_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3204_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3204_,
                                        0,
                                        v_fst_3154_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3204_,
                                        1,
                                        v_snd_3155_,
                                    );
                                    v___x_3200_ = v_reuseFailAlloc_3204_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3157_);
                        crate::leanh::lean_dec(v_snd_3155_);
                        crate::leanh::lean_dec(v_fst_3154_);
                        crate::leanh::lean_del_object(v___x_3152_);
                        crate::leanh::lean_dec(v_fst_3150_);
                        crate::leanh::lean_dec(v_a_3149_);
                        crate::leanh::lean_del_object(v___x_3144_);
                        crate::leanh::lean_dec_ref(v_isTarget_3130_);
                        v_a_3205_ = crate::leanh::lean_ctor_get(v___x_3175_, 0);
                        v_isSharedCheck_3212_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3175_)) as u8;
                        if v_isSharedCheck_3212_ == 0 {
                            v___x_3207_ = v___x_3175_;
                            v_isShared_3208_ = v_isSharedCheck_3212_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3205_);
                            crate::leanh::lean_dec(v___x_3175_);
                            v___x_3207_ = crate::leanh::lean_box(0);
                            v_isShared_3208_ = v_isSharedCheck_3212_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3158_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3157_, 1, v_a_3161_);
                    crate::leanh::lean_ctor_set(v___x_3157_, 0, v___x_3159_);
                    v___x_3163_ = v___x_3157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_a_3161_);
                    v___x_3163_ = v_reuseFailAlloc_3167_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3164_ = 1usize;
                v___x_3165_ = lean_usize_add(v_i_3133_, v___x_3164_);
                v_i_3133_ = v___x_3165_;
                v_b_3134_ = v___x_3163_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3145_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3144_, 1, v___x_3170_);
                    crate::leanh::lean_ctor_set(v___x_3144_, 0, v_fst_3150_);
                    v___x_3172_ = v___x_3144_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3173_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_fst_3150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___x_3170_);
                    v___x_3172_ = v_reuseFailAlloc_3173_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_3161_ = v___x_3172_;
                state = 4;
                continue;
            }
            8 => {
                if v_isShared_3145_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3144_, 1, v___x_3179_);
                    crate::leanh::lean_ctor_set(v___x_3144_, 0, v_fst_3150_);
                    v___x_3181_ = v___x_3144_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_fst_3150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3179_);
                    v___x_3181_ = v_reuseFailAlloc_3182_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_3161_ = v___x_3181_;
                state = 4;
                continue;
            }
            10 => {
                if v_isShared_3145_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3144_, 1, v___x_3194_);
                    crate::leanh::lean_ctor_set(v___x_3144_, 0, v___x_3192_);
                    v___x_3196_ = v___x_3144_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3197_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3194_);
                    v___x_3196_ = v_reuseFailAlloc_3197_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_3161_ = v___x_3196_;
                state = 4;
                continue;
            }
            12 => {
                if v_isShared_3145_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3144_, 1, v___x_3200_);
                    crate::leanh::lean_ctor_set(v___x_3144_, 0, v_fst_3150_);
                    v___x_3202_ = v___x_3144_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_fst_3150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___x_3200_);
                    v___x_3202_ = v_reuseFailAlloc_3203_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_3161_ = v___x_3202_;
                state = 4;
                continue;
            }
            14 => {
                if v_isShared_3208_ == 0 {
                    v___x_3210_ = v___x_3207_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
                    v___x_3210_ = v_reuseFailAlloc_3211_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3210_;
            }
            16 => {
                if v_isShared_3219_ == 0 {
                    v___x_3221_ = v___x_3218_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
                    v___x_3221_ = v_reuseFailAlloc_3222_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(
    mut v_goal_3226_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3227_: *mut crate::leanh::LeanObject,
    mut v_as_3228_: *mut crate::leanh::LeanObject,
    mut v_sz_3229_: *mut crate::leanh::LeanObject,
    mut v_i_3230_: *mut crate::leanh::LeanObject,
    mut v_b_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3237_: usize = 0;
    let mut v_i_boxed_3238_: usize = 0;
    let mut v_res_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3237_ = crate::leanh::lean_unbox_usize(v_sz_3229_);
    crate::leanh::lean_dec(v_sz_3229_);
    v_i_boxed_3238_ = crate::leanh::lean_unbox_usize(v_i_3230_);
    crate::leanh::lean_dec(v_i_3230_);
    v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_3226_, v_isTarget_3227_, v_as_3228_, v_sz_boxed_3237_, v_i_boxed_3238_, v_b_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
    crate::leanh::lean_dec(v___y_3235_);
    crate::leanh::lean_dec_ref(v___y_3234_);
    crate::leanh::lean_dec(v___y_3233_);
    crate::leanh::lean_dec_ref(v___y_3232_);
    crate::leanh::lean_dec_ref(v_as_3228_);
    crate::leanh::lean_dec_ref(v_goal_3226_);
    return v_res_3239_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(
    mut v_goal_3240_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3241_: *mut crate::leanh::LeanObject,
    mut v_as_3242_: *mut crate::leanh::LeanObject,
    mut v_sz_3243_: usize,
    mut v_i_3244_: usize,
    mut v_b_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v_a_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v_fst_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3319_: u8 = 0;
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3323_: u8 = 0;
    let mut v_isSharedCheck_3324_: u8 = 0;
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_unused_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3330_: u8 = 0;
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3334_: u8 = 0;
    let mut v_isSharedCheck_3335_: u8 = 0;
    let mut v_unused_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3251_ = lean_usize_dec_lt(v_i_3244_, v_sz_3243_);
                if v___x_3251_ == 0 {
                    crate::leanh::lean_dec_ref(v_isTarget_3241_);
                    v___x_3252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3252_, 0, v_b_3245_);
                    return v___x_3252_;
                } else {
                    v_snd_3253_ = crate::leanh::lean_ctor_get(v_b_3245_, 1);
                    v_isSharedCheck_3335_ = (!crate::leanh::lean_is_exclusive(v_b_3245_)) as u8;
                    if v_isSharedCheck_3335_ == 0 {
                        v_unused_3336_ = crate::leanh::lean_ctor_get(v_b_3245_, 0);
                        crate::leanh::lean_dec(v_unused_3336_);
                        v___x_3255_ = v_b_3245_;
                        v_isShared_3256_ = v_isSharedCheck_3335_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3253_);
                        crate::leanh::lean_dec(v_b_3245_);
                        v___x_3255_ = crate::leanh::lean_box(0);
                        v_isShared_3256_ = v_isSharedCheck_3335_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3257_ = lean_array_uget_borrowed(v_as_3242_, v_i_3244_);
                crate::leanh::lean_inc(v_a_3257_);
                v___x_3258_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3240_,
                    v_a_3257_,
                    v___y_3246_,
                    v___y_3247_,
                    v___y_3248_,
                    v___y_3249_,
                );
                if crate::leanh::lean_obj_tag(v___x_3258_) == 0 {
                    v_snd_3259_ = crate::leanh::lean_ctor_get(v_snd_3253_, 1);
                    crate::leanh::lean_inc(v_snd_3259_);
                    v_a_3260_ = crate::leanh::lean_ctor_get(v___x_3258_, 0);
                    crate::leanh::lean_inc(v_a_3260_);
                    crate::leanh::lean_dec_ref_known(v___x_3258_, 1);
                    v_fst_3261_ = crate::leanh::lean_ctor_get(v_snd_3253_, 0);
                    v_isSharedCheck_3325_ = (!crate::leanh::lean_is_exclusive(v_snd_3253_)) as u8;
                    if v_isSharedCheck_3325_ == 0 {
                        v_unused_3326_ = crate::leanh::lean_ctor_get(v_snd_3253_, 1);
                        crate::leanh::lean_dec(v_unused_3326_);
                        v___x_3263_ = v_snd_3253_;
                        v_isShared_3264_ = v_isSharedCheck_3325_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3261_);
                        crate::leanh::lean_dec(v_snd_3253_);
                        v___x_3263_ = crate::leanh::lean_box(0);
                        v_isShared_3264_ = v_isSharedCheck_3325_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3255_);
                    crate::leanh::lean_dec(v_snd_3253_);
                    crate::leanh::lean_dec_ref(v_isTarget_3241_);
                    v_a_3327_ = crate::leanh::lean_ctor_get(v___x_3258_, 0);
                    v_isSharedCheck_3334_ = (!crate::leanh::lean_is_exclusive(v___x_3258_)) as u8;
                    if v_isSharedCheck_3334_ == 0 {
                        v___x_3329_ = v___x_3258_;
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3327_);
                        crate::leanh::lean_dec(v___x_3258_);
                        v___x_3329_ = crate::leanh::lean_box(0);
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3265_ = crate::leanh::lean_ctor_get(v_snd_3259_, 0);
                v_snd_3266_ = crate::leanh::lean_ctor_get(v_snd_3259_, 1);
                v_isSharedCheck_3324_ = (!crate::leanh::lean_is_exclusive(v_snd_3259_)) as u8;
                if v_isSharedCheck_3324_ == 0 {
                    v___x_3268_ = v_snd_3259_;
                    v_isShared_3269_ = v_isSharedCheck_3324_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3266_);
                    crate::leanh::lean_inc(v_fst_3265_);
                    crate::leanh::lean_dec(v_snd_3259_);
                    v___x_3268_ = crate::leanh::lean_box(0);
                    v_isShared_3269_ = v_isSharedCheck_3324_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3270_ = crate::leanh::lean_box(0);
                v___x_3279_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3260_);
                if v___x_3279_ == 0 {
                    crate::leanh::lean_dec(v_a_3260_);
                    if v_isShared_3264_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3263_, 1, v_snd_3266_);
                        crate::leanh::lean_ctor_set(v___x_3263_, 0, v_fst_3265_);
                        v___x_3281_ = v___x_3263_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_fst_3265_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_snd_3266_);
                        v___x_3281_ = v_reuseFailAlloc_3285_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_isTarget_3241_);
                    crate::leanh::lean_inc(v___y_3249_);
                    crate::leanh::lean_inc_ref(v___y_3248_);
                    crate::leanh::lean_inc(v___y_3247_);
                    crate::leanh::lean_inc_ref(v___y_3246_);
                    crate::leanh::lean_inc(v_a_3260_);
                    v___x_3286_ = crate::leanh::lean_apply_6(
                        v_isTarget_3241_,
                        v_a_3260_,
                        v___y_3246_,
                        v___y_3247_,
                        v___y_3248_,
                        v___y_3249_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3286_) == 0 {
                        v_a_3287_ = crate::leanh::lean_ctor_get(v___x_3286_, 0);
                        crate::leanh::lean_inc(v_a_3287_);
                        crate::leanh::lean_dec_ref_known(v___x_3286_, 1);
                        v___x_3288_ = (crate::leanh::lean_unbox(v_a_3287_) as u8);
                        crate::leanh::lean_dec(v_a_3287_);
                        if v___x_3288_ == 0 {
                            crate::leanh::lean_dec(v_a_3260_);
                            if v_isShared_3264_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3263_, 1, v_snd_3266_);
                                crate::leanh::lean_ctor_set(v___x_3263_, 0, v_fst_3265_);
                                v___x_3290_ = v___x_3263_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_3294_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_fst_3265_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_snd_3266_);
                                v___x_3290_ = v_reuseFailAlloc_3294_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_self_3295_ = crate::leanh::lean_ctor_get(v_a_3260_, 0);
                            crate::leanh::lean_inc_ref(v_self_3295_);
                            crate::leanh::lean_dec(v_a_3260_);
                            v___x_3296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_3266_, v_self_3295_);
                            if crate::leanh::lean_obj_tag(v___x_3296_) == 0 {
                                v___x_3297_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_3240_, v_snd_3266_, v_self_3295_, v_fst_3265_, v_fst_3261_);
                                crate::leanh::lean_inc_n(v___x_3297_, 2);
                                v___x_3298_ = l_Rat_ofInt(v___x_3297_);
                                v___x_3299_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3240_,
                                    v_self_3295_,
                                    v___x_3298_,
                                    v_snd_3266_,
                                );
                                v___x_3300_ = crate::leanh::lean_box(0);
                                v___x_3301_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_3265_, v___x_3297_, v___x_3300_);
                                v___x_3302_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                                v___x_3303_ = lean_int_add(v___x_3297_, v___x_3302_);
                                crate::leanh::lean_dec(v___x_3297_);
                                if v_isShared_3264_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3263_, 1, v___x_3299_);
                                    crate::leanh::lean_ctor_set(v___x_3263_, 0, v___x_3301_);
                                    v___x_3305_ = v___x_3263_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3309_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3309_,
                                        0,
                                        v___x_3301_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3309_,
                                        1,
                                        v___x_3299_,
                                    );
                                    v___x_3305_ = v_reuseFailAlloc_3309_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_3296_, 1);
                                crate::leanh::lean_dec_ref(v_self_3295_);
                                if v_isShared_3264_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3263_, 1, v_snd_3266_);
                                    crate::leanh::lean_ctor_set(v___x_3263_, 0, v_fst_3265_);
                                    v___x_3311_ = v___x_3263_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3315_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3315_,
                                        0,
                                        v_fst_3265_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3315_,
                                        1,
                                        v_snd_3266_,
                                    );
                                    v___x_3311_ = v_reuseFailAlloc_3315_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3268_);
                        crate::leanh::lean_dec(v_snd_3266_);
                        crate::leanh::lean_dec(v_fst_3265_);
                        crate::leanh::lean_del_object(v___x_3263_);
                        crate::leanh::lean_dec(v_fst_3261_);
                        crate::leanh::lean_dec(v_a_3260_);
                        crate::leanh::lean_del_object(v___x_3255_);
                        crate::leanh::lean_dec_ref(v_isTarget_3241_);
                        v_a_3316_ = crate::leanh::lean_ctor_get(v___x_3286_, 0);
                        v_isSharedCheck_3323_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3286_)) as u8;
                        if v_isSharedCheck_3323_ == 0 {
                            v___x_3318_ = v___x_3286_;
                            v_isShared_3319_ = v_isSharedCheck_3323_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3316_);
                            crate::leanh::lean_dec(v___x_3286_);
                            v___x_3318_ = crate::leanh::lean_box(0);
                            v_isShared_3319_ = v_isSharedCheck_3323_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3269_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3268_, 1, v_a_3272_);
                    crate::leanh::lean_ctor_set(v___x_3268_, 0, v___x_3270_);
                    v___x_3274_ = v___x_3268_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_a_3272_);
                    v___x_3274_ = v_reuseFailAlloc_3278_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3275_ = 1usize;
                v___x_3276_ = lean_usize_add(v_i_3244_, v___x_3275_);
                v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_3240_, v_isTarget_3241_, v_as_3242_, v_sz_3243_, v___x_3276_, v___x_3274_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
                return v___x_3277_;
            }
            6 => {
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3255_, 1, v___x_3281_);
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v_fst_3261_);
                    v___x_3283_ = v___x_3255_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_fst_3261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 1, v___x_3281_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_3272_ = v___x_3283_;
                state = 4;
                continue;
            }
            8 => {
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3255_, 1, v___x_3290_);
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v_fst_3261_);
                    v___x_3292_ = v___x_3255_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_fst_3261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3290_);
                    v___x_3292_ = v_reuseFailAlloc_3293_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_3272_ = v___x_3292_;
                state = 4;
                continue;
            }
            10 => {
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3255_, 1, v___x_3305_);
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3303_);
                    v___x_3307_ = v___x_3255_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 1, v___x_3305_);
                    v___x_3307_ = v_reuseFailAlloc_3308_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_3272_ = v___x_3307_;
                state = 4;
                continue;
            }
            12 => {
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3255_, 1, v___x_3311_);
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v_fst_3261_);
                    v___x_3313_ = v___x_3255_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_fst_3261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3311_);
                    v___x_3313_ = v_reuseFailAlloc_3314_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_3272_ = v___x_3313_;
                state = 4;
                continue;
            }
            14 => {
                if v_isShared_3319_ == 0 {
                    v___x_3321_ = v___x_3318_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
                    v___x_3321_ = v_reuseFailAlloc_3322_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3321_;
            }
            16 => {
                if v_isShared_3330_ == 0 {
                    v___x_3332_ = v___x_3329_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
                    v___x_3332_ = v_reuseFailAlloc_3333_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(
    mut v_goal_3337_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3338_: *mut crate::leanh::LeanObject,
    mut v_as_3339_: *mut crate::leanh::LeanObject,
    mut v_sz_3340_: *mut crate::leanh::LeanObject,
    mut v_i_3341_: *mut crate::leanh::LeanObject,
    mut v_b_3342_: *mut crate::leanh::LeanObject,
    mut v___y_3343_: *mut crate::leanh::LeanObject,
    mut v___y_3344_: *mut crate::leanh::LeanObject,
    mut v___y_3345_: *mut crate::leanh::LeanObject,
    mut v___y_3346_: *mut crate::leanh::LeanObject,
    mut v___y_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3348_: usize = 0;
    let mut v_i_boxed_3349_: usize = 0;
    let mut v_res_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3348_ = crate::leanh::lean_unbox_usize(v_sz_3340_);
    crate::leanh::lean_dec(v_sz_3340_);
    v_i_boxed_3349_ = crate::leanh::lean_unbox_usize(v_i_3341_);
    crate::leanh::lean_dec(v_i_3341_);
    v_res_3350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_3337_, v_isTarget_3338_, v_as_3339_, v_sz_boxed_3348_, v_i_boxed_3349_, v_b_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
    crate::leanh::lean_dec(v___y_3346_);
    crate::leanh::lean_dec_ref(v___y_3345_);
    crate::leanh::lean_dec(v___y_3344_);
    crate::leanh::lean_dec_ref(v___y_3343_);
    crate::leanh::lean_dec_ref(v_as_3339_);
    crate::leanh::lean_dec_ref(v_goal_3337_);
    return v_res_3350_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(
    mut v_init_3351_: *mut crate::leanh::LeanObject,
    mut v_goal_3352_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3353_: *mut crate::leanh::LeanObject,
    mut v_n_3354_: *mut crate::leanh::LeanObject,
    mut v_b_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
    mut v___y_3358_: *mut crate::leanh::LeanObject,
    mut v___y_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3364_: usize = 0;
    let mut v___x_3365_: usize = 0;
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v_fst_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_a_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut v_vs_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3393_: usize = 0;
    let mut v___x_3394_: usize = 0;
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v_fst_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3410_: u8 = 0;
    let mut v_a_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_3354_) == 0 {
                    v_cs_3361_ = crate::leanh::lean_ctor_get(v_n_3354_, 0);
                    v___x_3362_ = crate::leanh::lean_box(0);
                    v___x_3363_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3363_, 0, v___x_3362_);
                    crate::leanh::lean_ctor_set(v___x_3363_, 1, v_b_3355_);
                    v_sz_3364_ = lean_array_size(v_cs_3361_);
                    v___x_3365_ = 0usize;
                    v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_3351_, v_goal_3352_, v_isTarget_3353_, v_cs_3361_, v_sz_3364_, v___x_3365_, v___x_3363_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
                    if crate::leanh::lean_obj_tag(v___x_3366_) == 0 {
                        v_a_3367_ = crate::leanh::lean_ctor_get(v___x_3366_, 0);
                        v_isSharedCheck_3381_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3366_)) as u8;
                        if v_isSharedCheck_3381_ == 0 {
                            v___x_3369_ = v___x_3366_;
                            v_isShared_3370_ = v_isSharedCheck_3381_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3367_);
                            crate::leanh::lean_dec(v___x_3366_);
                            v___x_3369_ = crate::leanh::lean_box(0);
                            v_isShared_3370_ = v_isSharedCheck_3381_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3382_ = crate::leanh::lean_ctor_get(v___x_3366_, 0);
                        v_isSharedCheck_3389_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3366_)) as u8;
                        if v_isSharedCheck_3389_ == 0 {
                            v___x_3384_ = v___x_3366_;
                            v_isShared_3385_ = v_isSharedCheck_3389_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3382_);
                            crate::leanh::lean_dec(v___x_3366_);
                            v___x_3384_ = crate::leanh::lean_box(0);
                            v_isShared_3385_ = v_isSharedCheck_3389_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3390_ = crate::leanh::lean_ctor_get(v_n_3354_, 0);
                    v___x_3391_ = crate::leanh::lean_box(0);
                    v___x_3392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3392_, 0, v___x_3391_);
                    crate::leanh::lean_ctor_set(v___x_3392_, 1, v_b_3355_);
                    v_sz_3393_ = lean_array_size(v_vs_3390_);
                    v___x_3394_ = 0usize;
                    v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_3352_, v_isTarget_3353_, v_vs_3390_, v_sz_3393_, v___x_3394_, v___x_3392_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
                    if crate::leanh::lean_obj_tag(v___x_3395_) == 0 {
                        v_a_3396_ = crate::leanh::lean_ctor_get(v___x_3395_, 0);
                        v_isSharedCheck_3410_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3395_)) as u8;
                        if v_isSharedCheck_3410_ == 0 {
                            v___x_3398_ = v___x_3395_;
                            v_isShared_3399_ = v_isSharedCheck_3410_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3396_);
                            crate::leanh::lean_dec(v___x_3395_);
                            v___x_3398_ = crate::leanh::lean_box(0);
                            v_isShared_3399_ = v_isSharedCheck_3410_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3411_ = crate::leanh::lean_ctor_get(v___x_3395_, 0);
                        v_isSharedCheck_3418_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3395_)) as u8;
                        if v_isSharedCheck_3418_ == 0 {
                            v___x_3413_ = v___x_3395_;
                            v_isShared_3414_ = v_isSharedCheck_3418_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3411_);
                            crate::leanh::lean_dec(v___x_3395_);
                            v___x_3413_ = crate::leanh::lean_box(0);
                            v_isShared_3414_ = v_isSharedCheck_3418_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3371_ = crate::leanh::lean_ctor_get(v_a_3367_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3371_) == 0 {
                    v_snd_3372_ = crate::leanh::lean_ctor_get(v_a_3367_, 1);
                    crate::leanh::lean_inc(v_snd_3372_);
                    crate::leanh::lean_dec(v_a_3367_);
                    v___x_3373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3373_, 0, v_snd_3372_);
                    if v_isShared_3370_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3369_, 0, v___x_3373_);
                        v___x_3375_ = v___x_3369_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3376_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
                        v___x_3375_ = v_reuseFailAlloc_3376_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3371_);
                    crate::leanh::lean_dec(v_a_3367_);
                    v_val_3377_ = crate::leanh::lean_ctor_get(v_fst_3371_, 0);
                    crate::leanh::lean_inc(v_val_3377_);
                    crate::leanh::lean_dec_ref_known(v_fst_3371_, 1);
                    if v_isShared_3370_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3369_, 0, v_val_3377_);
                        v___x_3379_ = v___x_3369_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_val_3377_);
                        v___x_3379_ = v_reuseFailAlloc_3380_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3375_;
            }
            3 => {
                return v___x_3379_;
            }
            4 => {
                if v_isShared_3385_ == 0 {
                    v___x_3387_ = v___x_3384_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
                    v___x_3387_ = v_reuseFailAlloc_3388_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3387_;
            }
            6 => {
                v_fst_3400_ = crate::leanh::lean_ctor_get(v_a_3396_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3400_) == 0 {
                    v_snd_3401_ = crate::leanh::lean_ctor_get(v_a_3396_, 1);
                    crate::leanh::lean_inc(v_snd_3401_);
                    crate::leanh::lean_dec(v_a_3396_);
                    v___x_3402_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3402_, 0, v_snd_3401_);
                    if v_isShared_3399_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3398_, 0, v___x_3402_);
                        v___x_3404_ = v___x_3398_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
                        v___x_3404_ = v_reuseFailAlloc_3405_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3400_);
                    crate::leanh::lean_dec(v_a_3396_);
                    v_val_3406_ = crate::leanh::lean_ctor_get(v_fst_3400_, 0);
                    crate::leanh::lean_inc(v_val_3406_);
                    crate::leanh::lean_dec_ref_known(v_fst_3400_, 1);
                    if v_isShared_3399_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3398_, 0, v_val_3406_);
                        v___x_3408_ = v___x_3398_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_val_3406_);
                        v___x_3408_ = v_reuseFailAlloc_3409_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3404_;
            }
            8 => {
                return v___x_3408_;
            }
            9 => {
                if v_isShared_3414_ == 0 {
                    v___x_3416_ = v___x_3413_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
                    v___x_3416_ = v_reuseFailAlloc_3417_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(
    mut v_init_3419_: *mut crate::leanh::LeanObject,
    mut v_goal_3420_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3421_: *mut crate::leanh::LeanObject,
    mut v_as_3422_: *mut crate::leanh::LeanObject,
    mut v_sz_3423_: usize,
    mut v_i_3424_: usize,
    mut v_b_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
    mut v___y_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: usize = 0;
    let mut v___x_3455_: usize = 0;
    let mut v_reuseFailAlloc_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3458_: u8 = 0;
    let mut v_a_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3466_: u8 = 0;
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v_unused_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3431_ = lean_usize_dec_lt(v_i_3424_, v_sz_3423_);
                if v___x_3431_ == 0 {
                    crate::leanh::lean_dec_ref(v_isTarget_3421_);
                    v___x_3432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3432_, 0, v_b_3425_);
                    return v___x_3432_;
                } else {
                    v_snd_3433_ = crate::leanh::lean_ctor_get(v_b_3425_, 1);
                    v_isSharedCheck_3467_ = (!crate::leanh::lean_is_exclusive(v_b_3425_)) as u8;
                    if v_isSharedCheck_3467_ == 0 {
                        v_unused_3468_ = crate::leanh::lean_ctor_get(v_b_3425_, 0);
                        crate::leanh::lean_dec(v_unused_3468_);
                        v___x_3435_ = v_b_3425_;
                        v_isShared_3436_ = v_isSharedCheck_3467_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3433_);
                        crate::leanh::lean_dec(v_b_3425_);
                        v___x_3435_ = crate::leanh::lean_box(0);
                        v_isShared_3436_ = v_isSharedCheck_3467_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3437_ = lean_array_uget_borrowed(v_as_3422_, v_i_3424_);
                crate::leanh::lean_inc(v_snd_3433_);
                crate::leanh::lean_inc_ref(v_isTarget_3421_);
                v___x_3438_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_3419_, v_goal_3420_, v_isTarget_3421_, v_a_3437_, v_snd_3433_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
                if crate::leanh::lean_obj_tag(v___x_3438_) == 0 {
                    v_a_3439_ = crate::leanh::lean_ctor_get(v___x_3438_, 0);
                    v_isSharedCheck_3458_ = (!crate::leanh::lean_is_exclusive(v___x_3438_)) as u8;
                    if v_isSharedCheck_3458_ == 0 {
                        v___x_3441_ = v___x_3438_;
                        v_isShared_3442_ = v_isSharedCheck_3458_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3439_);
                        crate::leanh::lean_dec(v___x_3438_);
                        v___x_3441_ = crate::leanh::lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3458_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3435_);
                    crate::leanh::lean_dec(v_snd_3433_);
                    crate::leanh::lean_dec_ref(v_isTarget_3421_);
                    v_a_3459_ = crate::leanh::lean_ctor_get(v___x_3438_, 0);
                    v_isSharedCheck_3466_ = (!crate::leanh::lean_is_exclusive(v___x_3438_)) as u8;
                    if v_isSharedCheck_3466_ == 0 {
                        v___x_3461_ = v___x_3438_;
                        v_isShared_3462_ = v_isSharedCheck_3466_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3459_);
                        crate::leanh::lean_dec(v___x_3438_);
                        v___x_3461_ = crate::leanh::lean_box(0);
                        v_isShared_3462_ = v_isSharedCheck_3466_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3439_) == 0 {
                    crate::leanh::lean_dec_ref(v_isTarget_3421_);
                    v___x_3443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3443_, 0, v_a_3439_);
                    if v_isShared_3436_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3435_, 0, v___x_3443_);
                        v___x_3445_ = v___x_3435_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3449_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3443_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_snd_3433_);
                        v___x_3445_ = v_reuseFailAlloc_3449_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3441_);
                    crate::leanh::lean_dec(v_snd_3433_);
                    v_a_3450_ = crate::leanh::lean_ctor_get(v_a_3439_, 0);
                    crate::leanh::lean_inc(v_a_3450_);
                    crate::leanh::lean_dec_ref_known(v_a_3439_, 1);
                    v___x_3451_ = crate::leanh::lean_box(0);
                    if v_isShared_3436_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3435_, 1, v_a_3450_);
                        crate::leanh::lean_ctor_set(v___x_3435_, 0, v___x_3451_);
                        v___x_3453_ = v___x_3435_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3457_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3451_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_a_3450_);
                        v___x_3453_ = v_reuseFailAlloc_3457_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3442_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3441_, 0, v___x_3445_);
                    v___x_3447_ = v___x_3441_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3448_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
                    v___x_3447_ = v_reuseFailAlloc_3448_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3447_;
            }
            5 => {
                v___x_3454_ = 1usize;
                v___x_3455_ = lean_usize_add(v_i_3424_, v___x_3454_);
                v_i_3424_ = v___x_3455_;
                v_b_3425_ = v___x_3453_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3462_ == 0 {
                    v___x_3464_ = v___x_3461_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
                    v___x_3464_ = v_reuseFailAlloc_3465_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3464_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(
    mut v_init_3469_: *mut crate::leanh::LeanObject,
    mut v_goal_3470_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3471_: *mut crate::leanh::LeanObject,
    mut v_as_3472_: *mut crate::leanh::LeanObject,
    mut v_sz_3473_: *mut crate::leanh::LeanObject,
    mut v_i_3474_: *mut crate::leanh::LeanObject,
    mut v_b_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3481_: usize = 0;
    let mut v_i_boxed_3482_: usize = 0;
    let mut v_res_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3481_ = crate::leanh::lean_unbox_usize(v_sz_3473_);
    crate::leanh::lean_dec(v_sz_3473_);
    v_i_boxed_3482_ = crate::leanh::lean_unbox_usize(v_i_3474_);
    crate::leanh::lean_dec(v_i_3474_);
    v_res_3483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_3469_, v_goal_3470_, v_isTarget_3471_, v_as_3472_, v_sz_boxed_3481_, v_i_boxed_3482_, v_b_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
    crate::leanh::lean_dec(v___y_3479_);
    crate::leanh::lean_dec_ref(v___y_3478_);
    crate::leanh::lean_dec(v___y_3477_);
    crate::leanh::lean_dec_ref(v___y_3476_);
    crate::leanh::lean_dec_ref(v_as_3472_);
    crate::leanh::lean_dec_ref(v_goal_3470_);
    crate::leanh::lean_dec_ref(v_init_3469_);
    return v_res_3483_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(
    mut v_init_3484_: *mut crate::leanh::LeanObject,
    mut v_goal_3485_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3486_: *mut crate::leanh::LeanObject,
    mut v_n_3487_: *mut crate::leanh::LeanObject,
    mut v_b_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3494_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_3484_, v_goal_3485_, v_isTarget_3486_, v_n_3487_, v_b_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
    crate::leanh::lean_dec(v___y_3492_);
    crate::leanh::lean_dec_ref(v___y_3491_);
    crate::leanh::lean_dec(v___y_3490_);
    crate::leanh::lean_dec_ref(v___y_3489_);
    crate::leanh::lean_dec_ref(v_n_3487_);
    crate::leanh::lean_dec_ref(v_goal_3485_);
    crate::leanh::lean_dec_ref(v_init_3484_);
    return v_res_3494_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(
    mut v_goal_3495_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3496_: *mut crate::leanh::LeanObject,
    mut v_t_3497_: *mut crate::leanh::LeanObject,
    mut v_init_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v_a_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3518_: usize = 0;
    let mut v___x_3519_: usize = 0;
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v_fst_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut v_a_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut v_a_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3547_: u8 = 0;
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3504_ = crate::leanh::lean_ctor_get(v_t_3497_, 0);
                v_tail_3505_ = crate::leanh::lean_ctor_get(v_t_3497_, 1);
                crate::leanh::lean_inc_ref(v_isTarget_3496_);
                crate::leanh::lean_inc_ref(v_init_3498_);
                v___x_3506_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_3498_, v_goal_3495_, v_isTarget_3496_, v_root_3504_, v_init_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
                crate::leanh::lean_dec_ref(v_init_3498_);
                if crate::leanh::lean_obj_tag(v___x_3506_) == 0 {
                    v_a_3507_ = crate::leanh::lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3543_ = (!crate::leanh::lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3543_ == 0 {
                        v___x_3509_ = v___x_3506_;
                        v_isShared_3510_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3507_);
                        crate::leanh::lean_dec(v___x_3506_);
                        v___x_3509_ = crate::leanh::lean_box(0);
                        v_isShared_3510_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_isTarget_3496_);
                    v_a_3544_ = crate::leanh::lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3551_ = (!crate::leanh::lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3551_ == 0 {
                        v___x_3546_ = v___x_3506_;
                        v_isShared_3547_ = v_isSharedCheck_3551_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3544_);
                        crate::leanh::lean_dec(v___x_3506_);
                        v___x_3546_ = crate::leanh::lean_box(0);
                        v_isShared_3547_ = v_isSharedCheck_3551_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3507_) == 0 {
                    crate::leanh::lean_dec_ref(v_isTarget_3496_);
                    v_a_3511_ = crate::leanh::lean_ctor_get(v_a_3507_, 0);
                    crate::leanh::lean_inc(v_a_3511_);
                    crate::leanh::lean_dec_ref_known(v_a_3507_, 1);
                    if v_isShared_3510_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3509_, 0, v_a_3511_);
                        v___x_3513_ = v___x_3509_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3511_);
                        v___x_3513_ = v_reuseFailAlloc_3514_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3509_);
                    v_a_3515_ = crate::leanh::lean_ctor_get(v_a_3507_, 0);
                    crate::leanh::lean_inc(v_a_3515_);
                    crate::leanh::lean_dec_ref_known(v_a_3507_, 1);
                    v___x_3516_ = crate::leanh::lean_box(0);
                    v___x_3517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3517_, 0, v___x_3516_);
                    crate::leanh::lean_ctor_set(v___x_3517_, 1, v_a_3515_);
                    v_sz_3518_ = lean_array_size(v_tail_3505_);
                    v___x_3519_ = 0usize;
                    v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_3495_, v_isTarget_3496_, v_tail_3505_, v_sz_3518_, v___x_3519_, v___x_3517_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
                    if crate::leanh::lean_obj_tag(v___x_3520_) == 0 {
                        v_a_3521_ = crate::leanh::lean_ctor_get(v___x_3520_, 0);
                        v_isSharedCheck_3534_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3520_)) as u8;
                        if v_isSharedCheck_3534_ == 0 {
                            v___x_3523_ = v___x_3520_;
                            v_isShared_3524_ = v_isSharedCheck_3534_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3521_);
                            crate::leanh::lean_dec(v___x_3520_);
                            v___x_3523_ = crate::leanh::lean_box(0);
                            v_isShared_3524_ = v_isSharedCheck_3534_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3535_ = crate::leanh::lean_ctor_get(v___x_3520_, 0);
                        v_isSharedCheck_3542_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3520_)) as u8;
                        if v_isSharedCheck_3542_ == 0 {
                            v___x_3537_ = v___x_3520_;
                            v_isShared_3538_ = v_isSharedCheck_3542_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3535_);
                            crate::leanh::lean_dec(v___x_3520_);
                            v___x_3537_ = crate::leanh::lean_box(0);
                            v_isShared_3538_ = v_isSharedCheck_3542_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3513_;
            }
            3 => {
                v_fst_3525_ = crate::leanh::lean_ctor_get(v_a_3521_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3525_) == 0 {
                    v_snd_3526_ = crate::leanh::lean_ctor_get(v_a_3521_, 1);
                    crate::leanh::lean_inc(v_snd_3526_);
                    crate::leanh::lean_dec(v_a_3521_);
                    if v_isShared_3524_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3523_, 0, v_snd_3526_);
                        v___x_3528_ = v___x_3523_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_snd_3526_);
                        v___x_3528_ = v_reuseFailAlloc_3529_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3525_);
                    crate::leanh::lean_dec(v_a_3521_);
                    v_val_3530_ = crate::leanh::lean_ctor_get(v_fst_3525_, 0);
                    crate::leanh::lean_inc(v_val_3530_);
                    crate::leanh::lean_dec_ref_known(v_fst_3525_, 1);
                    if v_isShared_3524_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3523_, 0, v_val_3530_);
                        v___x_3532_ = v___x_3523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_val_3530_);
                        v___x_3532_ = v_reuseFailAlloc_3533_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3528_;
            }
            5 => {
                return v___x_3532_;
            }
            6 => {
                if v_isShared_3538_ == 0 {
                    v___x_3540_ = v___x_3537_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
                    v___x_3540_ = v_reuseFailAlloc_3541_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3540_;
            }
            8 => {
                if v_isShared_3547_ == 0 {
                    v___x_3549_ = v___x_3546_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
                    v___x_3549_ = v_reuseFailAlloc_3550_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(
    mut v_goal_3552_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3553_: *mut crate::leanh::LeanObject,
    mut v_t_3554_: *mut crate::leanh::LeanObject,
    mut v_init_3555_: *mut crate::leanh::LeanObject,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
    mut v___y_3560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3561_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_3552_, v_isTarget_3553_, v_t_3554_, v_init_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
    crate::leanh::lean_dec(v___y_3559_);
    crate::leanh::lean_dec_ref(v___y_3558_);
    crate::leanh::lean_dec(v___y_3557_);
    crate::leanh::lean_dec_ref(v___y_3556_);
    crate::leanh::lean_dec_ref(v_t_3554_);
    crate::leanh::lean_dec_ref(v_goal_3552_);
    return v_res_3561_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(
    mut v_a_3562_: *mut crate::leanh::LeanObject,
    mut v_a_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3562_) == 0 {
                    v___x_3565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3565_, 0, v_a_3563_);
                    v___x_3566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3566_, 0, v___x_3565_);
                    return v___x_3566_;
                } else {
                    v_value_3567_ = crate::leanh::lean_ctor_get(v_a_3562_, 1);
                    crate::leanh::lean_inc(v_value_3567_);
                    v_tail_3568_ = crate::leanh::lean_ctor_get(v_a_3562_, 2);
                    crate::leanh::lean_inc(v_tail_3568_);
                    crate::leanh::lean_dec_ref_known(v_a_3562_, 3);
                    v_num_3569_ = crate::leanh::lean_ctor_get(v_value_3567_, 0);
                    crate::leanh::lean_inc(v_num_3569_);
                    v_den_3570_ = crate::leanh::lean_ctor_get(v_value_3567_, 1);
                    crate::leanh::lean_inc(v_den_3570_);
                    crate::leanh::lean_dec(v_value_3567_);
                    v___x_3571_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3572_ = lean_nat_dec_eq(v_den_3570_, v___x_3571_);
                    crate::leanh::lean_dec(v_den_3570_);
                    if v___x_3572_ == 0 {
                        crate::leanh::lean_dec(v_num_3569_);
                        v_a_3562_ = v_tail_3568_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3574_ = crate::leanh::lean_box(0);
                        v___x_3575_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_a_3563_, v_num_3569_, v___x_3574_);
                        v_a_3562_ = v_tail_3568_;
                        v_a_3563_ = v___x_3575_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(
    mut v_a_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3580_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_3577_, v_a_3578_);
    return v_res_3580_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(
    mut v_as_3581_: *mut crate::leanh::LeanObject,
    mut v_sz_3582_: usize,
    mut v_i_3583_: usize,
    mut v_b_3584_: *mut crate::leanh::LeanObject,
    mut v___y_3585_: *mut crate::leanh::LeanObject,
    mut v___y_3586_: *mut crate::leanh::LeanObject,
    mut v___y_3587_: *mut crate::leanh::LeanObject,
    mut v___y_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v_a_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: usize = 0;
    let mut v___x_3604_: usize = 0;
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut v_a_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3590_ = lean_usize_dec_lt(v_i_3583_, v_sz_3582_);
                if v___x_3590_ == 0 {
                    v___x_3591_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3591_, 0, v_b_3584_);
                    return v___x_3591_;
                } else {
                    v_a_3592_ = lean_array_uget_borrowed(v_as_3581_, v_i_3583_);
                    crate::leanh::lean_inc(v_a_3592_);
                    v___x_3593_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_3592_, v_b_3584_);
                    if crate::leanh::lean_obj_tag(v___x_3593_) == 0 {
                        v_a_3594_ = crate::leanh::lean_ctor_get(v___x_3593_, 0);
                        v_isSharedCheck_3606_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3593_)) as u8;
                        if v_isSharedCheck_3606_ == 0 {
                            v___x_3596_ = v___x_3593_;
                            v_isShared_3597_ = v_isSharedCheck_3606_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3594_);
                            crate::leanh::lean_dec(v___x_3593_);
                            v___x_3596_ = crate::leanh::lean_box(0);
                            v_isShared_3597_ = v_isSharedCheck_3606_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3607_ = crate::leanh::lean_ctor_get(v___x_3593_, 0);
                        v_isSharedCheck_3614_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3593_)) as u8;
                        if v_isSharedCheck_3614_ == 0 {
                            v___x_3609_ = v___x_3593_;
                            v_isShared_3610_ = v_isSharedCheck_3614_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3607_);
                            crate::leanh::lean_dec(v___x_3593_);
                            v___x_3609_ = crate::leanh::lean_box(0);
                            v_isShared_3610_ = v_isSharedCheck_3614_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3594_) == 0 {
                    v_a_3598_ = crate::leanh::lean_ctor_get(v_a_3594_, 0);
                    crate::leanh::lean_inc(v_a_3598_);
                    crate::leanh::lean_dec_ref_known(v_a_3594_, 1);
                    if v_isShared_3597_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3596_, 0, v_a_3598_);
                        v___x_3600_ = v___x_3596_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3598_);
                        v___x_3600_ = v_reuseFailAlloc_3601_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3596_);
                    v_a_3602_ = crate::leanh::lean_ctor_get(v_a_3594_, 0);
                    crate::leanh::lean_inc(v_a_3602_);
                    crate::leanh::lean_dec_ref_known(v_a_3594_, 1);
                    v___x_3603_ = 1usize;
                    v___x_3604_ = lean_usize_add(v_i_3583_, v___x_3603_);
                    v_i_3583_ = v___x_3604_;
                    v_b_3584_ = v_a_3602_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_3600_;
            }
            3 => {
                if v_isShared_3610_ == 0 {
                    v___x_3612_ = v___x_3609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
                    v___x_3612_ = v_reuseFailAlloc_3613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(
    mut v_as_3615_: *mut crate::leanh::LeanObject,
    mut v_sz_3616_: *mut crate::leanh::LeanObject,
    mut v_i_3617_: *mut crate::leanh::LeanObject,
    mut v_b_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
    mut v___y_3621_: *mut crate::leanh::LeanObject,
    mut v___y_3622_: *mut crate::leanh::LeanObject,
    mut v___y_3623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3624_: usize = 0;
    let mut v_i_boxed_3625_: usize = 0;
    let mut v_res_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3624_ = crate::leanh::lean_unbox_usize(v_sz_3616_);
    crate::leanh::lean_dec(v_sz_3616_);
    v_i_boxed_3625_ = crate::leanh::lean_unbox_usize(v_i_3617_);
    crate::leanh::lean_dec(v_i_3617_);
    v_res_3626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_3615_, v_sz_boxed_3624_, v_i_boxed_3625_, v_b_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
    crate::leanh::lean_dec(v___y_3622_);
    crate::leanh::lean_dec_ref(v___y_3621_);
    crate::leanh::lean_dec(v___y_3620_);
    crate::leanh::lean_dec_ref(v___y_3619_);
    crate::leanh::lean_dec_ref(v_as_3615_);
    return v_res_3626_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3627_ = crate::leanh::lean_box(0);
    v___x_3628_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3629_ = lean_mk_array(v___x_3628_, v___x_3627_);
    return v___x_3629_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3630_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
    v___x_3631_ = crate::leanh::lean_unsigned_to_nat(0);
    v_used_3632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_used_3632_, 0, v___x_3631_);
    crate::leanh::lean_ctor_set(v_used_3632_, 1, v___x_3630_);
    return v_used_3632_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(
    mut v_goal_3633_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3634_: *mut crate::leanh::LeanObject,
    mut v_model_3635_: *mut crate::leanh::LeanObject,
    mut v_a_3636_: *mut crate::leanh::LeanObject,
    mut v_a_3637_: *mut crate::leanh::LeanObject,
    mut v_a_3638_: *mut crate::leanh::LeanObject,
    mut v_a_3639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3643_: usize = 0;
    let mut v___x_3644_: usize = 0;
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextVal_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v_snd_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_a_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v_a_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3674_: u8 = 0;
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3641_ = crate::leanh::lean_ctor_get(v_model_3635_, 1);
                v_used_3642_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
                v_sz_3643_ = lean_array_size(v_buckets_3641_);
                v___x_3644_ = 0usize;
                v___x_3645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_3641_, v_sz_3643_, v___x_3644_, v_used_3642_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
                if crate::leanh::lean_obj_tag(v___x_3645_) == 0 {
                    v_toGoalState_3646_ = crate::leanh::lean_ctor_get(v_goal_3633_, 0);
                    v_a_3647_ = crate::leanh::lean_ctor_get(v___x_3645_, 0);
                    crate::leanh::lean_inc(v_a_3647_);
                    crate::leanh::lean_dec_ref_known(v___x_3645_, 1);
                    v_exprs_3648_ = crate::leanh::lean_ctor_get(v_toGoalState_3646_, 2);
                    v_nextVal_3649_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
                    v___x_3650_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3650_, 0, v_a_3647_);
                    crate::leanh::lean_ctor_set(v___x_3650_, 1, v_model_3635_);
                    v___x_3651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3651_, 0, v_nextVal_3649_);
                    crate::leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                    v___x_3652_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_3633_, v_isTarget_3634_, v_exprs_3648_, v___x_3651_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
                    if crate::leanh::lean_obj_tag(v___x_3652_) == 0 {
                        v_a_3653_ = crate::leanh::lean_ctor_get(v___x_3652_, 0);
                        v_isSharedCheck_3662_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3652_)) as u8;
                        if v_isSharedCheck_3662_ == 0 {
                            v___x_3655_ = v___x_3652_;
                            v_isShared_3656_ = v_isSharedCheck_3662_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3653_);
                            crate::leanh::lean_dec(v___x_3652_);
                            v___x_3655_ = crate::leanh::lean_box(0);
                            v_isShared_3656_ = v_isSharedCheck_3662_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3663_ = crate::leanh::lean_ctor_get(v___x_3652_, 0);
                        v_isSharedCheck_3670_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3652_)) as u8;
                        if v_isSharedCheck_3670_ == 0 {
                            v___x_3665_ = v___x_3652_;
                            v_isShared_3666_ = v_isSharedCheck_3670_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3663_);
                            crate::leanh::lean_dec(v___x_3652_);
                            v___x_3665_ = crate::leanh::lean_box(0);
                            v_isShared_3666_ = v_isSharedCheck_3670_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_model_3635_);
                    crate::leanh::lean_dec_ref(v_isTarget_3634_);
                    v_a_3671_ = crate::leanh::lean_ctor_get(v___x_3645_, 0);
                    v_isSharedCheck_3678_ = (!crate::leanh::lean_is_exclusive(v___x_3645_)) as u8;
                    if v_isSharedCheck_3678_ == 0 {
                        v___x_3673_ = v___x_3645_;
                        v_isShared_3674_ = v_isSharedCheck_3678_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3671_);
                        crate::leanh::lean_dec(v___x_3645_);
                        v___x_3673_ = crate::leanh::lean_box(0);
                        v_isShared_3674_ = v_isSharedCheck_3678_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3657_ = crate::leanh::lean_ctor_get(v_a_3653_, 1);
                crate::leanh::lean_inc(v_snd_3657_);
                crate::leanh::lean_dec(v_a_3653_);
                v_snd_3658_ = crate::leanh::lean_ctor_get(v_snd_3657_, 1);
                crate::leanh::lean_inc(v_snd_3658_);
                crate::leanh::lean_dec(v_snd_3657_);
                if v_isShared_3656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3655_, 0, v_snd_3658_);
                    v___x_3660_ = v___x_3655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_snd_3658_);
                    v___x_3660_ = v_reuseFailAlloc_3661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3660_;
            }
            3 => {
                if v_isShared_3666_ == 0 {
                    v___x_3668_ = v___x_3665_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
                    v___x_3668_ = v_reuseFailAlloc_3669_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3668_;
            }
            5 => {
                if v_isShared_3674_ == 0 {
                    v___x_3676_ = v___x_3673_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
                    v___x_3676_ = v_reuseFailAlloc_3677_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(
    mut v_goal_3679_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3680_: *mut crate::leanh::LeanObject,
    mut v_model_3681_: *mut crate::leanh::LeanObject,
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
    mut v_a_3684_: *mut crate::leanh::LeanObject,
    mut v_a_3685_: *mut crate::leanh::LeanObject,
    mut v_a_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3687_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_3679_, v_isTarget_3680_, v_model_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
    crate::leanh::lean_dec(v_a_3685_);
    crate::leanh::lean_dec_ref(v_a_3684_);
    crate::leanh::lean_dec(v_a_3683_);
    crate::leanh::lean_dec_ref(v_a_3682_);
    crate::leanh::lean_dec_ref(v_goal_3679_);
    return v_res_3687_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(
    mut v_00_u03b2_3688_: *mut crate::leanh::LeanObject,
    mut v_m_3689_: *mut crate::leanh::LeanObject,
    mut v_a_3690_: *mut crate::leanh::LeanObject,
    mut v_b_3691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3692_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_3689_, v_a_3690_, v_b_3691_);
    return v___x_3692_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(
    mut v_a_3693_: *mut crate::leanh::LeanObject,
    mut v_a_3694_: *mut crate::leanh::LeanObject,
    mut v___y_3695_: *mut crate::leanh::LeanObject,
    mut v___y_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_3693_, v_a_3694_);
    return v___x_3700_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(
    mut v_a_3701_: *mut crate::leanh::LeanObject,
    mut v_a_3702_: *mut crate::leanh::LeanObject,
    mut v___y_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3708_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_3701_, v_a_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
    crate::leanh::lean_dec(v___y_3706_);
    crate::leanh::lean_dec_ref(v___y_3705_);
    crate::leanh::lean_dec(v___y_3704_);
    crate::leanh::lean_dec_ref(v___y_3703_);
    return v_res_3708_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(
    mut v_00_u03b2_3709_: *mut crate::leanh::LeanObject,
    mut v_data_3710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3711_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_3710_);
    return v___x_3711_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3712_: *mut crate::leanh::LeanObject,
    mut v_i_3713_: *mut crate::leanh::LeanObject,
    mut v_source_3714_: *mut crate::leanh::LeanObject,
    mut v_target_3715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3716_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_3713_, v_source_3714_, v_target_3715_);
    return v___x_3716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b2_3717_: *mut crate::leanh::LeanObject,
    mut v_x_3718_: *mut crate::leanh::LeanObject,
    mut v_x_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_3718_, v_x_3719_);
    return v___x_3720_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(
    mut v_goal_3721_: *mut crate::leanh::LeanObject,
    mut v_hi_3722_: *mut crate::leanh::LeanObject,
    mut v_pivot_3723_: *mut crate::leanh::LeanObject,
    mut v_as_3724_: *mut crate::leanh::LeanObject,
    mut v_i_3725_: *mut crate::leanh::LeanObject,
    mut v_k_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3728_: u8 = 0;
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_u2081_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_u2082_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: u8 = 0;
    let mut v___x_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3737_ = lean_nat_dec_lt(v_k_3726_, v_hi_3722_);
                if v___x_3737_ == 0 {
                    crate::leanh::lean_dec(v_k_3726_);
                    v___x_3738_ = lean_array_fswap(v_as_3724_, v_i_3725_, v_hi_3722_);
                    v___x_3739_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3739_, 0, v_i_3725_);
                    crate::leanh::lean_ctor_set(v___x_3739_, 1, v___x_3738_);
                    return v___x_3739_;
                } else {
                    v___x_3740_ = lean_array_fget_borrowed(v_as_3724_, v_k_3726_);
                    v_fst_3741_ = crate::leanh::lean_ctor_get(v___x_3740_, 0);
                    v_fst_3742_ = crate::leanh::lean_ctor_get(v_pivot_3723_, 0);
                    v_g_u2081_3743_ =
                        l_Lean_Meta_Grind_Goal_getGeneration(v_goal_3721_, v_fst_3741_);
                    v_g_u2082_3744_ =
                        l_Lean_Meta_Grind_Goal_getGeneration(v_goal_3721_, v_fst_3742_);
                    v___x_3745_ = lean_nat_dec_eq(v_g_u2081_3743_, v_g_u2082_3744_);
                    if v___x_3745_ == 0 {
                        v___x_3746_ = lean_nat_dec_lt(v_g_u2081_3743_, v_g_u2082_3744_);
                        crate::leanh::lean_dec(v_g_u2082_3744_);
                        crate::leanh::lean_dec(v_g_u2081_3743_);
                        v___y_3728_ = v___x_3746_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_g_u2082_3744_);
                        crate::leanh::lean_dec(v_g_u2081_3743_);
                        v___x_3747_ = lean_expr_lt(v_fst_3741_, v_fst_3742_);
                        v___y_3728_ = v___x_3747_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3728_ == 0 {
                    v___x_3729_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3730_ = lean_nat_add(v_k_3726_, v___x_3729_);
                    crate::leanh::lean_dec(v_k_3726_);
                    v_k_3726_ = v___x_3730_;
                    state = 0;
                    continue;
                } else {
                    v___x_3732_ = lean_array_fswap(v_as_3724_, v_i_3725_, v_k_3726_);
                    v___x_3733_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3734_ = lean_nat_add(v_i_3725_, v___x_3733_);
                    crate::leanh::lean_dec(v_i_3725_);
                    v___x_3735_ = lean_nat_add(v_k_3726_, v___x_3733_);
                    crate::leanh::lean_dec(v_k_3726_);
                    v_as_3724_ = v___x_3732_;
                    v_i_3725_ = v___x_3734_;
                    v_k_3726_ = v___x_3735_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(
    mut v_goal_3748_: *mut crate::leanh::LeanObject,
    mut v_hi_3749_: *mut crate::leanh::LeanObject,
    mut v_pivot_3750_: *mut crate::leanh::LeanObject,
    mut v_as_3751_: *mut crate::leanh::LeanObject,
    mut v_i_3752_: *mut crate::leanh::LeanObject,
    mut v_k_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_3748_, v_hi_3749_, v_pivot_3750_, v_as_3751_, v_i_3752_, v_k_3753_);
    crate::leanh::lean_dec_ref(v_pivot_3750_);
    crate::leanh::lean_dec(v_hi_3749_);
    crate::leanh::lean_dec_ref(v_goal_3748_);
    return v_res_3754_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(
    mut v_goal_3755_: *mut crate::leanh::LeanObject,
    mut v_x_3756_: *mut crate::leanh::LeanObject,
    mut v_x_3757_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_u2081_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_u2082_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: u8 = 0;
    v_fst_3758_ = crate::leanh::lean_ctor_get(v_x_3756_, 0);
    v_fst_3759_ = crate::leanh::lean_ctor_get(v_x_3757_, 0);
    v_g_u2081_3760_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_3755_, v_fst_3758_);
    v_g_u2082_3761_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_3755_, v_fst_3759_);
    v___x_3762_ = lean_nat_dec_eq(v_g_u2081_3760_, v_g_u2082_3761_);
    if v___x_3762_ == 0 {
        let mut v___x_3763_: u8 = 0;
        v___x_3763_ = lean_nat_dec_lt(v_g_u2081_3760_, v_g_u2082_3761_);
        crate::leanh::lean_dec(v_g_u2082_3761_);
        crate::leanh::lean_dec(v_g_u2081_3760_);
        return v___x_3763_;
    } else {
        let mut v___x_3764_: u8 = 0;
        crate::leanh::lean_dec(v_g_u2082_3761_);
        crate::leanh::lean_dec(v_g_u2081_3760_);
        v___x_3764_ = lean_expr_lt(v_fst_3758_, v_fst_3759_);
        return v___x_3764_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(
    mut v_goal_3765_: *mut crate::leanh::LeanObject,
    mut v_x_3766_: *mut crate::leanh::LeanObject,
    mut v_x_3767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3768_: u8 = 0;
    let mut v_r_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_3765_, v_x_3766_, v_x_3767_);
    crate::leanh::lean_dec_ref(v_x_3767_);
    crate::leanh::lean_dec_ref(v_x_3766_);
    crate::leanh::lean_dec_ref(v_goal_3765_);
    v_r_3769_ = crate::leanh::lean_box((v_res_3768_) as usize);
    return v_r_3769_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(
    mut v_goal_3770_: *mut crate::leanh::LeanObject,
    mut v_n_3771_: *mut crate::leanh::LeanObject,
    mut v_as_3772_: *mut crate::leanh::LeanObject,
    mut v_lo_3773_: *mut crate::leanh::LeanObject,
    mut v_hi_3774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: u8 = 0;
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: u8 = 0;
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3786_ = lean_nat_dec_lt(v_lo_3773_, v_hi_3774_);
                if v___x_3786_ == 0 {
                    crate::leanh::lean_dec(v_lo_3773_);
                    return v_as_3772_;
                } else {
                    v___x_3787_ = lean_nat_add(v_lo_3773_, v_hi_3774_);
                    v___x_3788_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3789_ = lean_nat_shiftr(v___x_3787_, v___x_3788_);
                    crate::leanh::lean_dec(v___x_3787_);
                    v___x_3802_ = lean_array_fget_borrowed(v_as_3772_, v_mid_3789_);
                    v___x_3803_ = lean_array_fget_borrowed(v_as_3772_, v_lo_3773_);
                    v___x_3804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_3770_, v___x_3802_, v___x_3803_);
                    if v___x_3804_ == 0 {
                        v___y_3797_ = v_as_3772_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3805_ = lean_array_fswap(v_as_3772_, v_lo_3773_, v_mid_3789_);
                        v___y_3797_ = v___x_3805_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3777_ = lean_array_fget(v___y_3776_, v_hi_3774_);
                crate::leanh::lean_inc_n(v_lo_3773_, 2);
                v___x_3778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_3770_, v_hi_3774_, v_pivot_3777_, v___y_3776_, v_lo_3773_, v_lo_3773_);
                crate::leanh::lean_dec(v_pivot_3777_);
                v_fst_3779_ = crate::leanh::lean_ctor_get(v___x_3778_, 0);
                crate::leanh::lean_inc(v_fst_3779_);
                v_snd_3780_ = crate::leanh::lean_ctor_get(v___x_3778_, 1);
                crate::leanh::lean_inc(v_snd_3780_);
                crate::leanh::lean_dec_ref(v___x_3778_);
                v___x_3781_ = lean_nat_dec_le(v_hi_3774_, v_fst_3779_);
                if v___x_3781_ == 0 {
                    v___x_3782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3770_, v_n_3771_, v_snd_3780_, v_lo_3773_, v_fst_3779_);
                    v___x_3783_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3784_ = lean_nat_add(v_fst_3779_, v___x_3783_);
                    crate::leanh::lean_dec(v_fst_3779_);
                    v_as_3772_ = v___x_3782_;
                    v_lo_3773_ = v___x_3784_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3779_);
                    crate::leanh::lean_dec(v_lo_3773_);
                    return v_snd_3780_;
                }
            }
            2 => {
                v___x_3792_ = lean_array_fget_borrowed(v___y_3791_, v_mid_3789_);
                v___x_3793_ = lean_array_fget_borrowed(v___y_3791_, v_hi_3774_);
                v___x_3794_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_3770_, v___x_3792_, v___x_3793_);
                if v___x_3794_ == 0 {
                    crate::leanh::lean_dec(v_mid_3789_);
                    v___y_3776_ = v___y_3791_;
                    state = 1;
                    continue;
                } else {
                    v___x_3795_ = lean_array_fswap(v___y_3791_, v_mid_3789_, v_hi_3774_);
                    crate::leanh::lean_dec(v_mid_3789_);
                    v___y_3776_ = v___x_3795_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3798_ = lean_array_fget_borrowed(v___y_3797_, v_hi_3774_);
                v___x_3799_ = lean_array_fget_borrowed(v___y_3797_, v_lo_3773_);
                v___x_3800_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_3770_, v___x_3798_, v___x_3799_);
                if v___x_3800_ == 0 {
                    v___y_3791_ = v___y_3797_;
                    state = 2;
                    continue;
                } else {
                    v___x_3801_ = lean_array_fswap(v___y_3797_, v_lo_3773_, v_hi_3774_);
                    v___y_3791_ = v___x_3801_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(
    mut v_goal_3806_: *mut crate::leanh::LeanObject,
    mut v_n_3807_: *mut crate::leanh::LeanObject,
    mut v_as_3808_: *mut crate::leanh::LeanObject,
    mut v_lo_3809_: *mut crate::leanh::LeanObject,
    mut v_hi_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3806_, v_n_3807_, v_as_3808_, v_lo_3809_, v_hi_3810_);
    crate::leanh::lean_dec(v_hi_3810_);
    crate::leanh::lean_dec(v_n_3807_);
    crate::leanh::lean_dec_ref(v_goal_3806_);
    return v_res_3811_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(
    mut v_goal_3812_: *mut crate::leanh::LeanObject,
    mut v_m_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3814_ = lean_array_get_size(v_m_3813_);
                v___x_3815_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3816_ = lean_nat_dec_eq(v___x_3814_, v___x_3815_);
                if v___x_3816_ == 0 {
                    v___x_3817_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3818_ = lean_nat_sub(v___x_3814_, v___x_3817_);
                    v___x_3824_ = lean_nat_dec_le(v___x_3815_, v___x_3818_);
                    if v___x_3824_ == 0 {
                        crate::leanh::lean_inc(v___x_3818_);
                        v___y_3820_ = v___x_3818_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3820_ = v___x_3815_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_m_3813_;
                }
            }
            1 => {
                v___x_3821_ = lean_nat_dec_le(v___y_3820_, v___x_3818_);
                if v___x_3821_ == 0 {
                    crate::leanh::lean_dec(v___x_3818_);
                    crate::leanh::lean_inc(v___y_3820_);
                    v___x_3822_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3812_, v___x_3814_, v_m_3813_, v___y_3820_, v___y_3820_);
                    crate::leanh::lean_dec(v___y_3820_);
                    return v___x_3822_;
                } else {
                    v___x_3823_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3812_, v___x_3814_, v_m_3813_, v___y_3820_, v___x_3818_);
                    crate::leanh::lean_dec(v___x_3818_);
                    return v___x_3823_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(
    mut v_goal_3825_: *mut crate::leanh::LeanObject,
    mut v_m_3826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3827_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(
            v_goal_3825_,
            v_m_3826_,
        );
    crate::leanh::lean_dec_ref(v_goal_3825_);
    return v_res_3827_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(
    mut v_goal_3828_: *mut crate::leanh::LeanObject,
    mut v_n_3829_: *mut crate::leanh::LeanObject,
    mut v_as_3830_: *mut crate::leanh::LeanObject,
    mut v_lo_3831_: *mut crate::leanh::LeanObject,
    mut v_hi_3832_: *mut crate::leanh::LeanObject,
    mut v_w_3833_: *mut crate::leanh::LeanObject,
    mut v_hlo_3834_: *mut crate::leanh::LeanObject,
    mut v_hhi_3835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3828_, v_n_3829_, v_as_3830_, v_lo_3831_, v_hi_3832_);
    return v___x_3836_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(
    mut v_goal_3837_: *mut crate::leanh::LeanObject,
    mut v_n_3838_: *mut crate::leanh::LeanObject,
    mut v_as_3839_: *mut crate::leanh::LeanObject,
    mut v_lo_3840_: *mut crate::leanh::LeanObject,
    mut v_hi_3841_: *mut crate::leanh::LeanObject,
    mut v_w_3842_: *mut crate::leanh::LeanObject,
    mut v_hlo_3843_: *mut crate::leanh::LeanObject,
    mut v_hhi_3844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_3837_, v_n_3838_, v_as_3839_, v_lo_3840_, v_hi_3841_, v_w_3842_, v_hlo_3843_, v_hhi_3844_);
    crate::leanh::lean_dec(v_hi_3841_);
    crate::leanh::lean_dec(v_n_3838_);
    crate::leanh::lean_dec_ref(v_goal_3837_);
    return v_res_3845_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(
    mut v_goal_3846_: *mut crate::leanh::LeanObject,
    mut v_n_3847_: *mut crate::leanh::LeanObject,
    mut v_lo_3848_: *mut crate::leanh::LeanObject,
    mut v_hi_3849_: *mut crate::leanh::LeanObject,
    mut v_hhi_3850_: *mut crate::leanh::LeanObject,
    mut v_pivot_3851_: *mut crate::leanh::LeanObject,
    mut v_as_3852_: *mut crate::leanh::LeanObject,
    mut v_i_3853_: *mut crate::leanh::LeanObject,
    mut v_k_3854_: *mut crate::leanh::LeanObject,
    mut v_ilo_3855_: *mut crate::leanh::LeanObject,
    mut v_ik_3856_: *mut crate::leanh::LeanObject,
    mut v_w_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_3846_, v_hi_3849_, v_pivot_3851_, v_as_3852_, v_i_3853_, v_k_3854_);
    return v___x_3858_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(
    mut v_goal_3859_: *mut crate::leanh::LeanObject,
    mut v_n_3860_: *mut crate::leanh::LeanObject,
    mut v_lo_3861_: *mut crate::leanh::LeanObject,
    mut v_hi_3862_: *mut crate::leanh::LeanObject,
    mut v_hhi_3863_: *mut crate::leanh::LeanObject,
    mut v_pivot_3864_: *mut crate::leanh::LeanObject,
    mut v_as_3865_: *mut crate::leanh::LeanObject,
    mut v_i_3866_: *mut crate::leanh::LeanObject,
    mut v_k_3867_: *mut crate::leanh::LeanObject,
    mut v_ilo_3868_: *mut crate::leanh::LeanObject,
    mut v_ik_3869_: *mut crate::leanh::LeanObject,
    mut v_w_3870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3871_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_3859_, v_n_3860_, v_lo_3861_, v_hi_3862_, v_hhi_3863_, v_pivot_3864_, v_as_3865_, v_i_3866_, v_k_3867_, v_ilo_3868_, v_ik_3869_, v_w_3870_);
    crate::leanh::lean_dec_ref(v_pivot_3864_);
    crate::leanh::lean_dec(v_hi_3862_);
    crate::leanh::lean_dec(v_lo_3861_);
    crate::leanh::lean_dec(v_n_3860_);
    crate::leanh::lean_dec_ref(v_goal_3859_);
    return v_res_3871_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: u8 = 0;
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3872_) == 0 {
                    v___x_3875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3875_, 0, v_a_3873_);
                    v___x_3876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3876_, 0, v___x_3875_);
                    return v___x_3876_;
                } else {
                    v_key_3877_ = crate::leanh::lean_ctor_get(v_a_3872_, 0);
                    crate::leanh::lean_inc_n(v_key_3877_, 2);
                    v_value_3878_ = crate::leanh::lean_ctor_get(v_a_3872_, 1);
                    crate::leanh::lean_inc(v_value_3878_);
                    v_tail_3879_ = crate::leanh::lean_ctor_get(v_a_3872_, 2);
                    crate::leanh::lean_inc(v_tail_3879_);
                    crate::leanh::lean_dec_ref_known(v_a_3872_, 3);
                    v___x_3880_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_3877_);
                    if v___x_3880_ == 0 {
                        v___x_3881_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3881_, 0, v_key_3877_);
                        crate::leanh::lean_ctor_set(v___x_3881_, 1, v_value_3878_);
                        v___x_3882_ = lean_array_push(v_a_3873_, v___x_3881_);
                        v_a_3872_ = v_tail_3879_;
                        v_a_3873_ = v___x_3882_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_value_3878_);
                        crate::leanh::lean_dec(v_key_3877_);
                        v_a_3872_ = v_tail_3879_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(
    mut v_a_3885_: *mut crate::leanh::LeanObject,
    mut v_a_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3888_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_3885_, v_a_3886_);
    return v_res_3888_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(
    mut v_as_3889_: *mut crate::leanh::LeanObject,
    mut v_sz_3890_: usize,
    mut v_i_3891_: usize,
    mut v_b_3892_: *mut crate::leanh::LeanObject,
    mut v___y_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
    mut v___y_3896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3905_: u8 = 0;
    let mut v_a_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: usize = 0;
    let mut v___x_3912_: usize = 0;
    let mut v_isSharedCheck_3914_: u8 = 0;
    let mut v_a_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3898_ = lean_usize_dec_lt(v_i_3891_, v_sz_3890_);
                if v___x_3898_ == 0 {
                    v___x_3899_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3899_, 0, v_b_3892_);
                    return v___x_3899_;
                } else {
                    v_a_3900_ = lean_array_uget_borrowed(v_as_3889_, v_i_3891_);
                    crate::leanh::lean_inc(v_a_3900_);
                    v___x_3901_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_3900_, v_b_3892_);
                    if crate::leanh::lean_obj_tag(v___x_3901_) == 0 {
                        v_a_3902_ = crate::leanh::lean_ctor_get(v___x_3901_, 0);
                        v_isSharedCheck_3914_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3901_)) as u8;
                        if v_isSharedCheck_3914_ == 0 {
                            v___x_3904_ = v___x_3901_;
                            v_isShared_3905_ = v_isSharedCheck_3914_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3902_);
                            crate::leanh::lean_dec(v___x_3901_);
                            v___x_3904_ = crate::leanh::lean_box(0);
                            v_isShared_3905_ = v_isSharedCheck_3914_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3915_ = crate::leanh::lean_ctor_get(v___x_3901_, 0);
                        v_isSharedCheck_3922_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3901_)) as u8;
                        if v_isSharedCheck_3922_ == 0 {
                            v___x_3917_ = v___x_3901_;
                            v_isShared_3918_ = v_isSharedCheck_3922_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3915_);
                            crate::leanh::lean_dec(v___x_3901_);
                            v___x_3917_ = crate::leanh::lean_box(0);
                            v_isShared_3918_ = v_isSharedCheck_3922_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3902_) == 0 {
                    v_a_3906_ = crate::leanh::lean_ctor_get(v_a_3902_, 0);
                    crate::leanh::lean_inc(v_a_3906_);
                    crate::leanh::lean_dec_ref_known(v_a_3902_, 1);
                    if v_isShared_3905_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3904_, 0, v_a_3906_);
                        v___x_3908_ = v___x_3904_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3909_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3906_);
                        v___x_3908_ = v_reuseFailAlloc_3909_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3904_);
                    v_a_3910_ = crate::leanh::lean_ctor_get(v_a_3902_, 0);
                    crate::leanh::lean_inc(v_a_3910_);
                    crate::leanh::lean_dec_ref_known(v_a_3902_, 1);
                    v___x_3911_ = 1usize;
                    v___x_3912_ = lean_usize_add(v_i_3891_, v___x_3911_);
                    v_i_3891_ = v___x_3912_;
                    v_b_3892_ = v_a_3910_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_3908_;
            }
            3 => {
                if v_isShared_3918_ == 0 {
                    v___x_3920_ = v___x_3917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
                    v___x_3920_ = v_reuseFailAlloc_3921_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(
    mut v_as_3923_: *mut crate::leanh::LeanObject,
    mut v_sz_3924_: *mut crate::leanh::LeanObject,
    mut v_i_3925_: *mut crate::leanh::LeanObject,
    mut v_b_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3932_: usize = 0;
    let mut v_i_boxed_3933_: usize = 0;
    let mut v_res_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3932_ = crate::leanh::lean_unbox_usize(v_sz_3924_);
    crate::leanh::lean_dec(v_sz_3924_);
    v_i_boxed_3933_ = crate::leanh::lean_unbox_usize(v_i_3925_);
    crate::leanh::lean_dec(v_i_3925_);
    v_res_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_3923_, v_sz_boxed_3932_, v_i_boxed_3933_, v_b_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
    crate::leanh::lean_dec(v___y_3930_);
    crate::leanh::lean_dec_ref(v___y_3929_);
    crate::leanh::lean_dec(v___y_3928_);
    crate::leanh::lean_dec_ref(v___y_3927_);
    crate::leanh::lean_dec_ref(v_as_3923_);
    return v_res_3934_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_finalizeModel(
    mut v_goal_3937_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3938_: *mut crate::leanh::LeanObject,
    mut v_model_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_a_3942_: *mut crate::leanh::LeanObject,
    mut v_a_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3949_: usize = 0;
    let mut v___x_3950_: usize = 0;
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut v_a_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3945_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_3937_, v_isTarget_3938_, v_model_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
                if crate::leanh::lean_obj_tag(v___x_3945_) == 0 {
                    v_a_3946_ = crate::leanh::lean_ctor_get(v___x_3945_, 0);
                    crate::leanh::lean_inc(v_a_3946_);
                    crate::leanh::lean_dec_ref_known(v___x_3945_, 1);
                    v_buckets_3947_ = crate::leanh::lean_ctor_get(v_a_3946_, 1);
                    crate::leanh::lean_inc_ref(v_buckets_3947_);
                    crate::leanh::lean_dec(v_a_3946_);
                    v___x_3948_ = l_Lean_Meta_Grind_Arith_finalizeModel___closed__0;
                    v_sz_3949_ = lean_array_size(v_buckets_3947_);
                    v___x_3950_ = 0usize;
                    v___x_3951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_3947_, v_sz_3949_, v___x_3950_, v___x_3948_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
                    crate::leanh::lean_dec_ref(v_buckets_3947_);
                    if crate::leanh::lean_obj_tag(v___x_3951_) == 0 {
                        v_a_3952_ = crate::leanh::lean_ctor_get(v___x_3951_, 0);
                        v_isSharedCheck_3960_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3951_)) as u8;
                        if v_isSharedCheck_3960_ == 0 {
                            v___x_3954_ = v___x_3951_;
                            v_isShared_3955_ = v_isSharedCheck_3960_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3952_);
                            crate::leanh::lean_dec(v___x_3951_);
                            v___x_3954_ = crate::leanh::lean_box(0);
                            v_isShared_3955_ = v_isSharedCheck_3960_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3951_;
                    }
                } else {
                    v_a_3961_ = crate::leanh::lean_ctor_get(v___x_3945_, 0);
                    v_isSharedCheck_3968_ = (!crate::leanh::lean_is_exclusive(v___x_3945_)) as u8;
                    if v_isSharedCheck_3968_ == 0 {
                        v___x_3963_ = v___x_3945_;
                        v_isShared_3964_ = v_isSharedCheck_3968_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3961_);
                        crate::leanh::lean_dec(v___x_3945_);
                        v___x_3963_ = crate::leanh::lean_box(0);
                        v_isShared_3964_ = v_isSharedCheck_3968_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3956_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_3937_, v_a_3952_);
                if v_isShared_3955_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3954_, 0, v___x_3956_);
                    v___x_3958_ = v___x_3954_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
                    v___x_3958_ = v_reuseFailAlloc_3959_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3958_;
            }
            3 => {
                if v_isShared_3964_ == 0 {
                    v___x_3966_ = v___x_3963_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
                    v___x_3966_ = v_reuseFailAlloc_3967_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_finalizeModel___boxed(
    mut v_goal_3969_: *mut crate::leanh::LeanObject,
    mut v_isTarget_3970_: *mut crate::leanh::LeanObject,
    mut v_model_3971_: *mut crate::leanh::LeanObject,
    mut v_a_3972_: *mut crate::leanh::LeanObject,
    mut v_a_3973_: *mut crate::leanh::LeanObject,
    mut v_a_3974_: *mut crate::leanh::LeanObject,
    mut v_a_3975_: *mut crate::leanh::LeanObject,
    mut v_a_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3977_ = l_Lean_Meta_Grind_Arith_finalizeModel(
        v_goal_3969_,
        v_isTarget_3970_,
        v_model_3971_,
        v_a_3972_,
        v_a_3973_,
        v_a_3974_,
        v_a_3975_,
    );
    crate::leanh::lean_dec(v_a_3975_);
    crate::leanh::lean_dec_ref(v_a_3974_);
    crate::leanh::lean_dec(v_a_3973_);
    crate::leanh::lean_dec_ref(v_a_3972_);
    crate::leanh::lean_dec_ref(v_goal_3969_);
    return v_res_3977_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(
    mut v_a_3978_: *mut crate::leanh::LeanObject,
    mut v_a_3979_: *mut crate::leanh::LeanObject,
    mut v___y_3980_: *mut crate::leanh::LeanObject,
    mut v___y_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3985_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_3978_, v_a_3979_);
    return v___x_3985_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(
    mut v_a_3986_: *mut crate::leanh::LeanObject,
    mut v_a_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
    mut v___y_3989_: *mut crate::leanh::LeanObject,
    mut v___y_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3993_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_3986_, v_a_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
    crate::leanh::lean_dec(v___y_3991_);
    crate::leanh::lean_dec_ref(v___y_3990_);
    crate::leanh::lean_dec(v___y_3989_);
    crate::leanh::lean_dec_ref(v___y_3988_);
    return v_res_3993_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(
    mut v_msgData_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
    mut v___y_3997_: *mut crate::leanh::LeanObject,
    mut v___y_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4000_ = lean_st_ref_get(v___y_3998_);
    v_env_4001_ = crate::leanh::lean_ctor_get(v___x_4000_, 0);
    crate::leanh::lean_inc_ref(v_env_4001_);
    crate::leanh::lean_dec(v___x_4000_);
    v___x_4002_ = lean_st_ref_get(v___y_3996_);
    v_mctx_4003_ = crate::leanh::lean_ctor_get(v___x_4002_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4003_);
    crate::leanh::lean_dec(v___x_4002_);
    v_lctx_4004_ = crate::leanh::lean_ctor_get(v___y_3995_, 2);
    v_options_4005_ = crate::leanh::lean_ctor_get(v___y_3997_, 2);
    crate::leanh::lean_inc_ref(v_options_4005_);
    crate::leanh::lean_inc_ref(v_lctx_4004_);
    v___x_4006_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4006_, 0, v_env_4001_);
    crate::leanh::lean_ctor_set(v___x_4006_, 1, v_mctx_4003_);
    crate::leanh::lean_ctor_set(v___x_4006_, 2, v_lctx_4004_);
    crate::leanh::lean_ctor_set(v___x_4006_, 3, v_options_4005_);
    v___x_4007_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4007_, 0, v___x_4006_);
    crate::leanh::lean_ctor_set(v___x_4007_, 1, v_msgData_3994_);
    v___x_4008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4008_, 0, v___x_4007_);
    return v___x_4008_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(
    mut v_msgData_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
    crate::leanh::lean_dec(v___y_4013_);
    crate::leanh::lean_dec_ref(v___y_4012_);
    crate::leanh::lean_dec(v___y_4011_);
    crate::leanh::lean_dec_ref(v___y_4010_);
    return v_res_4015_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0()
-> f64 {
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: f64 = 0.0;
    v___x_4016_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4017_ = lean_float_of_nat(v___x_4016_);
    return v___x_4017_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(
    mut v_cls_4021_: *mut crate::leanh::LeanObject,
    mut v_msg_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v_tid_4047_: u64 = 0;
    let mut v_traces_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4051_: u8 = 0;
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: f64 = 0.0;
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_isSharedCheck_4073_: u8 = 0;
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4028_ = crate::leanh::lean_ctor_get(v___y_4025_, 5);
                v___x_4029_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
                v_a_4030_ = crate::leanh::lean_ctor_get(v___x_4029_, 0);
                v_isSharedCheck_4074_ = (!crate::leanh::lean_is_exclusive(v___x_4029_)) as u8;
                if v_isSharedCheck_4074_ == 0 {
                    v___x_4032_ = v___x_4029_;
                    v_isShared_4033_ = v_isSharedCheck_4074_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4030_);
                    crate::leanh::lean_dec(v___x_4029_);
                    v___x_4032_ = crate::leanh::lean_box(0);
                    v_isShared_4033_ = v_isSharedCheck_4074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4034_ = lean_st_ref_take(v___y_4026_);
                v_traceState_4035_ = crate::leanh::lean_ctor_get(v___x_4034_, 4);
                v_env_4036_ = crate::leanh::lean_ctor_get(v___x_4034_, 0);
                v_nextMacroScope_4037_ = crate::leanh::lean_ctor_get(v___x_4034_, 1);
                v_ngen_4038_ = crate::leanh::lean_ctor_get(v___x_4034_, 2);
                v_auxDeclNGen_4039_ = crate::leanh::lean_ctor_get(v___x_4034_, 3);
                v_cache_4040_ = crate::leanh::lean_ctor_get(v___x_4034_, 5);
                v_messages_4041_ = crate::leanh::lean_ctor_get(v___x_4034_, 6);
                v_infoState_4042_ = crate::leanh::lean_ctor_get(v___x_4034_, 7);
                v_snapshotTasks_4043_ = crate::leanh::lean_ctor_get(v___x_4034_, 8);
                v_isSharedCheck_4073_ = (!crate::leanh::lean_is_exclusive(v___x_4034_)) as u8;
                if v_isSharedCheck_4073_ == 0 {
                    v___x_4045_ = v___x_4034_;
                    v_isShared_4046_ = v_isSharedCheck_4073_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4043_);
                    crate::leanh::lean_inc(v_infoState_4042_);
                    crate::leanh::lean_inc(v_messages_4041_);
                    crate::leanh::lean_inc(v_cache_4040_);
                    crate::leanh::lean_inc(v_traceState_4035_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4039_);
                    crate::leanh::lean_inc(v_ngen_4038_);
                    crate::leanh::lean_inc(v_nextMacroScope_4037_);
                    crate::leanh::lean_inc(v_env_4036_);
                    crate::leanh::lean_dec(v___x_4034_);
                    v___x_4045_ = crate::leanh::lean_box(0);
                    v_isShared_4046_ = v_isSharedCheck_4073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4047_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4035_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4048_ = crate::leanh::lean_ctor_get(v_traceState_4035_, 0);
                v_isSharedCheck_4072_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4035_)) as u8;
                if v_isSharedCheck_4072_ == 0 {
                    v___x_4050_ = v_traceState_4035_;
                    v_isShared_4051_ = v_isSharedCheck_4072_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4048_);
                    crate::leanh::lean_dec(v_traceState_4035_);
                    v___x_4050_ = crate::leanh::lean_box(0);
                    v_isShared_4051_ = v_isSharedCheck_4072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4052_ = crate::leanh::lean_box(0);
                v___x_4053_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
                v___x_4054_ = 0;
                v___x_4055_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1;
                v___x_4056_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4056_, 0, v_cls_4021_);
                crate::leanh::lean_ctor_set(v___x_4056_, 1, v___x_4052_);
                crate::leanh::lean_ctor_set(v___x_4056_, 2, v___x_4055_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4056_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4053_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4056_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4053_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4056_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4054_,
                );
                v___x_4057_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2;
                v___x_4058_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4058_, 0, v___x_4056_);
                crate::leanh::lean_ctor_set(v___x_4058_, 1, v_a_4030_);
                crate::leanh::lean_ctor_set(v___x_4058_, 2, v___x_4057_);
                crate::leanh::lean_inc(v_ref_4028_);
                v___x_4059_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4059_, 0, v_ref_4028_);
                crate::leanh::lean_ctor_set(v___x_4059_, 1, v___x_4058_);
                v___x_4060_ = l_Lean_PersistentArray_push___redArg(v_traces_4048_, v___x_4059_);
                if v_isShared_4051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4050_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4050_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4071_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4060_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4047_,
                    );
                    v___x_4062_ = v_reuseFailAlloc_4071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4046_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4045_, 4, v___x_4062_);
                    v___x_4064_ = v___x_4045_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_env_4036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_nextMacroScope_4037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_ngen_4038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 3, v_auxDeclNGen_4039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 4, v___x_4062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 5, v_cache_4040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 6, v_messages_4041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 7, v_infoState_4042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 8, v_snapshotTasks_4043_);
                    v___x_4064_ = v_reuseFailAlloc_4070_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4065_ = lean_st_ref_set(v___y_4026_, v___x_4064_);
                v___x_4066_ = crate::leanh::lean_box(0);
                if v_isShared_4033_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4032_, 0, v___x_4066_);
                    v___x_4068_ = v___x_4032_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4066_);
                    v___x_4068_ = v_reuseFailAlloc_4069_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(
    mut v_cls_4075_: *mut crate::leanh::LeanObject,
    mut v_msg_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
    mut v___y_4081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4082_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(
        v_cls_4075_,
        v_msg_4076_,
        v___y_4077_,
        v___y_4078_,
        v___y_4079_,
        v___y_4080_,
    );
    crate::leanh::lean_dec(v___y_4080_);
    crate::leanh::lean_dec_ref(v___y_4079_);
    crate::leanh::lean_dec(v___y_4078_);
    crate::leanh::lean_dec_ref(v___y_4077_);
    return v_res_4082_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0;
    v___x_4085_ = l_Lean_stringToMessageData(v___x_4084_);
    return v___x_4085_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(
    mut v_traceClass_4087_: *mut crate::leanh::LeanObject,
    mut v_as_4088_: *mut crate::leanh::LeanObject,
    mut v_sz_4089_: usize,
    mut v_i_4090_: usize,
    mut v_b_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v_num_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: usize = 0;
    let mut v___x_4123_: usize = 0;
    let mut v_reuseFailAlloc_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4135_: u8 = 0;
    let mut v_isSharedCheck_4136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4097_ = lean_usize_dec_lt(v_i_4090_, v_sz_4089_);
                if v___x_4097_ == 0 {
                    crate::leanh::lean_dec(v_traceClass_4087_);
                    v___x_4098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4098_, 0, v_b_4091_);
                    return v___x_4098_;
                } else {
                    v_a_4099_ = lean_array_uget(v_as_4088_, v_i_4090_);
                    v_snd_4100_ = crate::leanh::lean_ctor_get(v_a_4099_, 1);
                    v_fst_4101_ = crate::leanh::lean_ctor_get(v_a_4099_, 0);
                    v_isSharedCheck_4136_ = (!crate::leanh::lean_is_exclusive(v_a_4099_)) as u8;
                    if v_isSharedCheck_4136_ == 0 {
                        v___x_4103_ = v_a_4099_;
                        v_isShared_4104_ = v_isSharedCheck_4136_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4100_);
                        crate::leanh::lean_inc(v_fst_4101_);
                        crate::leanh::lean_dec(v_a_4099_);
                        v___x_4103_ = crate::leanh::lean_box(0);
                        v_isShared_4104_ = v_isSharedCheck_4136_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_num_4105_ = crate::leanh::lean_ctor_get(v_snd_4100_, 0);
                v_den_4106_ = crate::leanh::lean_ctor_get(v_snd_4100_, 1);
                v_isSharedCheck_4135_ = (!crate::leanh::lean_is_exclusive(v_snd_4100_)) as u8;
                if v_isSharedCheck_4135_ == 0 {
                    v___x_4108_ = v_snd_4100_;
                    v_isShared_4109_ = v_isSharedCheck_4135_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_den_4106_);
                    crate::leanh::lean_inc(v_num_4105_);
                    crate::leanh::lean_dec(v_snd_4100_);
                    v___x_4108_ = crate::leanh::lean_box(0);
                    v_isShared_4109_ = v_isSharedCheck_4135_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4110_ = crate::leanh::lean_box(0);
                v___x_4111_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_4101_);
                v___x_4112_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
                if v_isShared_4109_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4108_, 7);
                    crate::leanh::lean_ctor_set(v___x_4108_, 1, v___x_4112_);
                    crate::leanh::lean_ctor_set(v___x_4108_, 0, v___x_4111_);
                    v___x_4114_ = v___x_4108_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4134_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4111_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 1, v___x_4112_);
                    v___x_4114_ = v_reuseFailAlloc_4134_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4126_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4127_ = lean_nat_dec_eq(v_den_4106_, v___x_4126_);
                if v___x_4127_ == 0 {
                    v___x_4128_ = l_Int_repr(v_num_4105_);
                    crate::leanh::lean_dec(v_num_4105_);
                    v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2;
                    v___x_4130_ = lean_string_append(v___x_4128_, v___x_4129_);
                    v___x_4131_ = l_Nat_reprFast(v_den_4106_);
                    v___x_4132_ = lean_string_append(v___x_4130_, v___x_4131_);
                    crate::leanh::lean_dec_ref(v___x_4131_);
                    v___y_4116_ = v___x_4132_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_den_4106_);
                    v___x_4133_ = l_Int_repr(v_num_4105_);
                    crate::leanh::lean_dec(v_num_4105_);
                    v___y_4116_ = v___x_4133_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4117_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4117_, 0, v___y_4116_);
                v___x_4118_ = l_Lean_MessageData_ofFormat(v___x_4117_);
                if v_isShared_4104_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4103_, 7);
                    crate::leanh::lean_ctor_set(v___x_4103_, 1, v___x_4118_);
                    crate::leanh::lean_ctor_set(v___x_4103_, 0, v___x_4114_);
                    v___x_4120_ = v___x_4103_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4125_, 1, v___x_4118_);
                    v___x_4120_ = v_reuseFailAlloc_4125_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_traceClass_4087_);
                v___x_4121_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(
                    v_traceClass_4087_,
                    v___x_4120_,
                    v___y_4092_,
                    v___y_4093_,
                    v___y_4094_,
                    v___y_4095_,
                );
                if crate::leanh::lean_obj_tag(v___x_4121_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4121_, 1);
                    v___x_4122_ = 1usize;
                    v___x_4123_ = lean_usize_add(v_i_4090_, v___x_4122_);
                    v_i_4090_ = v___x_4123_;
                    v_b_4091_ = v___x_4110_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceClass_4087_);
                    return v___x_4121_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(
    mut v_traceClass_4137_: *mut crate::leanh::LeanObject,
    mut v_as_4138_: *mut crate::leanh::LeanObject,
    mut v_sz_4139_: *mut crate::leanh::LeanObject,
    mut v_i_4140_: *mut crate::leanh::LeanObject,
    mut v_b_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4147_: usize = 0;
    let mut v_i_boxed_4148_: usize = 0;
    let mut v_res_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4147_ = crate::leanh::lean_unbox_usize(v_sz_4139_);
    crate::leanh::lean_dec(v_sz_4139_);
    v_i_boxed_4148_ = crate::leanh::lean_unbox_usize(v_i_4140_);
    crate::leanh::lean_dec(v_i_4140_);
    v_res_4149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_4137_, v_as_4138_, v_sz_boxed_4147_, v_i_boxed_4148_, v_b_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
    crate::leanh::lean_dec(v___y_4145_);
    crate::leanh::lean_dec_ref(v___y_4144_);
    crate::leanh::lean_dec(v___y_4143_);
    crate::leanh::lean_dec_ref(v___y_4142_);
    crate::leanh::lean_dec_ref(v_as_4138_);
    return v_res_4149_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_traceModel(
    mut v_traceClass_4153_: *mut crate::leanh::LeanObject,
    mut v_model_4154_: *mut crate::leanh::LeanObject,
    mut v_a_4155_: *mut crate::leanh::LeanObject,
    mut v_a_4156_: *mut crate::leanh::LeanObject,
    mut v_a_4157_: *mut crate::leanh::LeanObject,
    mut v_a_4158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4164_: u8 = 0;
    let mut v_inheritedTraceOptions_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: u8 = 0;
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4170_: usize = 0;
    let mut v___x_4171_: usize = 0;
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4175_: u8 = 0;
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4179_: u8 = 0;
    let mut v_unused_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4163_ = crate::leanh::lean_ctor_get(v_a_4157_, 2);
                v_hasTrace_4164_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_4163_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4164_ == 0 {
                    crate::leanh::lean_dec(v_traceClass_4153_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_4165_ = crate::leanh::lean_ctor_get(v_a_4157_, 13);
                    v___x_4166_ = l_Lean_Meta_Grind_Arith_traceModel___closed__1;
                    crate::leanh::lean_inc(v_traceClass_4153_);
                    v___x_4167_ = l_Lean_Name_append(v___x_4166_, v_traceClass_4153_);
                    v___x_4168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4165_,
                        v_options_4163_,
                        v___x_4167_,
                    );
                    crate::leanh::lean_dec(v___x_4167_);
                    if v___x_4168_ == 0 {
                        crate::leanh::lean_dec(v_traceClass_4153_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4169_ = crate::leanh::lean_box(0);
                        v_sz_4170_ = lean_array_size(v_model_4154_);
                        v___x_4171_ = 0usize;
                        v___x_4172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_4153_, v_model_4154_, v_sz_4170_, v___x_4171_, v___x_4169_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
                        if crate::leanh::lean_obj_tag(v___x_4172_) == 0 {
                            v_isSharedCheck_4179_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4172_)) as u8;
                            if v_isSharedCheck_4179_ == 0 {
                                v_unused_4180_ = crate::leanh::lean_ctor_get(v___x_4172_, 0);
                                crate::leanh::lean_dec(v_unused_4180_);
                                v___x_4174_ = v___x_4172_;
                                v_isShared_4175_ = v_isSharedCheck_4179_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4172_);
                                v___x_4174_ = crate::leanh::lean_box(0);
                                v_isShared_4175_ = v_isSharedCheck_4179_;
                                state = 2;
                                continue;
                            }
                        } else {
                            return v___x_4172_;
                        }
                    }
                }
            }
            1 => {
                v___x_4161_ = crate::leanh::lean_box(0);
                v___x_4162_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4162_, 0, v___x_4161_);
                return v___x_4162_;
            }
            2 => {
                if v_isShared_4175_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4174_, 0, v___x_4169_);
                    v___x_4177_ = v___x_4174_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4169_);
                    v___x_4177_ = v_reuseFailAlloc_4178_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_traceModel___boxed(
    mut v_traceClass_4181_: *mut crate::leanh::LeanObject,
    mut v_model_4182_: *mut crate::leanh::LeanObject,
    mut v_a_4183_: *mut crate::leanh::LeanObject,
    mut v_a_4184_: *mut crate::leanh::LeanObject,
    mut v_a_4185_: *mut crate::leanh::LeanObject,
    mut v_a_4186_: *mut crate::leanh::LeanObject,
    mut v_a_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Lean_Meta_Grind_Arith_traceModel(
        v_traceClass_4181_,
        v_model_4182_,
        v_a_4183_,
        v_a_4184_,
        v_a_4185_,
        v_a_4186_,
    );
    crate::leanh::lean_dec(v_a_4186_);
    crate::leanh::lean_dec_ref(v_a_4185_);
    crate::leanh::lean_dec(v_a_4184_);
    crate::leanh::lean_dec_ref(v_a_4183_);
    crate::leanh::lean_dec_ref(v_model_4182_);
    return v_res_4188_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Module_Envelope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
}
