// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.ModelUtil
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Arith.Util Init.Grind.Module.Envelope
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_ofInt, l_instDecidableEqRat_decEq};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Grind::Module::Envelope::{
    initialize_Init_Grind_Module_Envelope, runtime_initialize_Init_Grind_Module_Envelope,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::{lean_expr_eqv, lean_expr_lt};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_6, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__1_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__3_value) as *mut LeanObject,907667957179513571 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value: LeanStringObject<5> =
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
        m_data: [72, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value: LeanStringObject<5> =
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
        m_data: [104, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value)
                as *mut LeanObject,
            10393083817453678557 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value)
                as *mut LeanObject,
            10680564408669940870 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value: LeanStringObject<5> =
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
        m_data: [72, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value: LeanStringObject<5> =
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
        m_data: [104, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value)
                as *mut LeanObject,
            2929883540436775422 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value)
                as *mut LeanObject,
            1611444129324655608 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value: LeanStringObject<5> =
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
        m_data: [72, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value: LeanStringObject<5> =
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
        m_data: [104, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value)
                as *mut LeanObject,
            16856108565602861689 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value)
                as *mut LeanObject,
            4187025665268973031 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value)
                as *mut LeanObject,
            15703084674812832738 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value)
                as *mut LeanObject,
            13609749952674037527 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value: LeanStringObject<4> =
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
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value: LeanStringObject<4> =
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
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value)
                as *mut LeanObject,
            17185717442815859305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value: LeanStringObject<5> =
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
        m_data: [72, 68, 105, 118, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value: LeanStringObject<5> =
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
        m_data: [104, 68, 105, 118, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value)
                as *mut LeanObject,
            11858238400308895562 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value)
                as *mut LeanObject,
            6100819061652633370 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value: LeanStringObject<5> =
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
        m_data: [72, 77, 111, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value: LeanStringObject<5> =
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
        m_data: [104, 77, 111, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value)
                as *mut LeanObject,
            13744984671752750173 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value)
                as *mut LeanObject,
            9682224670061807480 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value: LeanStringObject<4> =
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
        m_data: [79, 110, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value: LeanStringObject<4> =
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
        m_data: [111, 110, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value)
                as *mut LeanObject,
            1389984430658442515 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value)
                as *mut LeanObject,
            9294582609080780319 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value: LeanStringObject<5> =
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
        m_data: [90, 101, 114, 111, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value: LeanStringObject<5> =
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
        m_data: [122, 101, 114, 111, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value)
                as *mut LeanObject,
            18263865437487147968 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value)
                as *mut LeanObject,
            2651253468108498348 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value: LeanStringObject<4> =
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
        m_data: [73, 110, 118, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value: LeanStringObject<4> =
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
        m_data: [105, 110, 118, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value)
                as *mut LeanObject,
            1412621069384631438 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value)
                as *mut LeanObject,
            10171450186735820607 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value)
                as *mut LeanObject,
            5779414593499529281 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value)
                as *mut LeanObject,
            7063772860359172143 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value)
                as *mut LeanObject,
            17636616155771105671 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value)
                as *mut LeanObject,
            15578568367168711682 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value)
                as *mut LeanObject,
            16822059798527729847 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value)
                as *mut LeanObject,
            2495166364501146107 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value: LeanStringObject<4> =
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
        m_data: [70, 105, 110, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value: LeanStringObject<4> =
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
        m_data: [118, 97, 108, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value)
                as *mut LeanObject,
            15815496672699636542 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value)
                as *mut LeanObject,
            7912375598873795493 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value: LeanStringObject<10> =
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
        m_data: [73, 110, 116, 77, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value: LeanStringObject<4> =
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
        m_data: [116, 111, 81, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value)
                as *mut LeanObject,
            7605204649477761179 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value)
                as *mut LeanObject,
            11314908490917688650 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value)
                as *mut LeanObject,
            6592053806809043044 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value)
        as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_finalizeModel___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Grind_Arith_finalizeModel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_traceModel___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_traceModel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_traceModel___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_traceModel___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_traceModel___closed__0_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_traceModel___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_traceModel___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__1(
    mut v_a_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Rat_ofInt(v_a_2095_);
    return v___x_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(
    mut v_a_2097_: *mut LeanObject,
    mut v_x_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2098_) == 0 {
                    v___x_2099_ = lean_box(0);
                    return v___x_2099_;
                } else {
                    v_key_2100_ = lean_ctor_get(v_x_2098_, 0);
                    v_value_2101_ = lean_ctor_get(v_x_2098_, 1);
                    v_tail_2102_ = lean_ctor_get(v_x_2098_, 2);
                    v___x_2103_ = lean_expr_eqv(v_key_2100_, v_a_2097_);
                    if v___x_2103_ == 0 {
                        v_x_2098_ = v_tail_2102_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2101_);
                        v___x_2105_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2105_, 0, v_value_2101_);
                        return v___x_2105_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg___boxed(
    mut v_a_2106_: *mut LeanObject,
    mut v_x_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2108_: *mut LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_2106_, v_x_2107_);
    lean_dec(v_x_2107_);
    lean_dec_ref(v_a_2106_);
    return v_res_2108_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(
    mut v_m_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2111_ = lean_ctor_get(v_m_2109_, 1);
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
    mut v_m_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2129_: *mut LeanObject = core::ptr::null_mut();
    v_res_2129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_2127_, v_a_2128_);
    lean_dec_ref(v_a_2128_);
    lean_dec_ref(v_m_2127_);
    return v_res_2129_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(
    mut v_a_2130_: *mut LeanObject,
    mut v_v_2131_: *mut LeanObject,
    mut v_other_2132_: *mut LeanObject,
) -> u8 {
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    v___x_2133_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_a_2130_, v_other_2132_);
    if lean_obj_tag(v___x_2133_) == 1 {
        let mut v_val_2134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: u8 = 0;
        v_val_2134_ = lean_ctor_get(v___x_2133_, 0);
        lean_inc(v_val_2134_);
        lean_dec_ref_known(v___x_2133_, 1);
        v___x_2135_ = l_Rat_ofInt(v_v_2131_);
        v___x_2136_ = l_instDecidableEqRat_decEq(v_val_2134_, v___x_2135_);
        lean_dec_ref(v___x_2135_);
        lean_dec(v_val_2134_);
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
        lean_dec(v___x_2133_);
        lean_dec(v_v_2131_);
        v___x_2139_ = 1;
        return v___x_2139_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq___boxed(
    mut v_a_2140_: *mut LeanObject,
    mut v_v_2141_: *mut LeanObject,
    mut v_other_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2143_: u8 = 0;
    let mut v_r_2144_: *mut LeanObject = core::ptr::null_mut();
    v_res_2143_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_2140_, v_v_2141_, v_other_2142_);
    lean_dec_ref(v_other_2142_);
    lean_dec_ref(v_a_2140_);
    v_r_2144_ = lean_box((v_res_2143_) as usize);
    return v_r_2144_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(
    mut v_00_u03b2_2145_: *mut LeanObject,
    mut v_m_2146_: *mut LeanObject,
    mut v_a_2147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    v___x_2148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_2146_, v_a_2147_);
    return v___x_2148_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___boxed(
    mut v_00_u03b2_2149_: *mut LeanObject,
    mut v_m_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2152_: *mut LeanObject = core::ptr::null_mut();
    v_res_2152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(v_00_u03b2_2149_, v_m_2150_, v_a_2151_);
    lean_dec_ref(v_a_2151_);
    lean_dec_ref(v_m_2150_);
    return v_res_2152_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(
    mut v_00_u03b2_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
    mut v_x_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    v___x_2156_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_2154_, v_x_2155_);
    return v___x_2156_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___boxed(
    mut v_00_u03b2_2157_: *mut LeanObject,
    mut v_a_2158_: *mut LeanObject,
    mut v_x_2159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2160_: *mut LeanObject = core::ptr::null_mut();
    v_res_2160_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(v_00_u03b2_2157_, v_a_2158_, v_x_2159_);
    lean_dec(v_x_2159_);
    lean_dec_ref(v_a_2158_);
    return v_res_2160_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(
    mut v_goal_2176_: *mut LeanObject,
    mut v_e_2177_: *mut LeanObject,
    mut v_a_2178_: *mut LeanObject,
    mut v_v_2179_: *mut LeanObject,
    mut v_as_x27_2180_: *mut LeanObject,
    mut v_b_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2187_: u8 = 0;
    let mut v___y_2188_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v_arg_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v_arg_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: u8 = 0;
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2218_: u8 = 0;
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v___y_2223_: u8 = 0;
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2180_) == 0 {
                    lean_dec(v_v_2179_);
                    lean_inc_ref(v_b_2181_);
                    return v_b_2181_;
                } else {
                    v_head_2182_ = lean_ctor_get(v_as_x27_2180_, 0);
                    v_tail_2183_ = lean_ctor_get(v_as_x27_2180_, 1);
                    v___x_2184_ = lean_box(0);
                    v___x_2185_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0;
                    lean_inc(v_head_2182_);
                    v___x_2193_ = l_Lean_Expr_cleanupAnnotations(v_head_2182_);
                    v___x_2194_ = l_Lean_Expr_isApp(v___x_2193_);
                    if v___x_2194_ == 0 {
                        lean_dec_ref(v___x_2193_);
                        v_as_x27_2180_ = v_tail_2183_;
                        v_b_2181_ = v___x_2185_;
                        state = 0;
                        continue;
                    } else {
                        v_arg_2196_ = lean_ctor_get(v___x_2193_, 1);
                        lean_inc_ref(v_arg_2196_);
                        v___x_2197_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2193_);
                        v___x_2198_ = l_Lean_Expr_isApp(v___x_2197_);
                        if v___x_2198_ == 0 {
                            lean_dec_ref(v___x_2197_);
                            lean_dec_ref(v_arg_2196_);
                            v_as_x27_2180_ = v_tail_2183_;
                            v_b_2181_ = v___x_2185_;
                            state = 0;
                            continue;
                        } else {
                            v_arg_2200_ = lean_ctor_get(v___x_2197_, 1);
                            lean_inc_ref(v_arg_2200_);
                            v___x_2201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2197_);
                            v___x_2202_ = l_Lean_Expr_isApp(v___x_2201_);
                            if v___x_2202_ == 0 {
                                lean_dec_ref(v___x_2201_);
                                lean_dec_ref(v_arg_2200_);
                                lean_dec_ref(v_arg_2196_);
                                v_as_x27_2180_ = v_tail_2183_;
                                v_b_2181_ = v___x_2185_;
                                state = 0;
                                continue;
                            } else {
                                v___x_2204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2201_);
                                v___x_2205_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2;
                                v___x_2206_ = l_Lean_Expr_isConstOf(v___x_2204_, v___x_2205_);
                                lean_dec_ref(v___x_2204_);
                                if v___x_2206_ == 0 {
                                    lean_dec_ref(v_arg_2200_);
                                    lean_dec_ref(v_arg_2196_);
                                    v_as_x27_2180_ = v_tail_2183_;
                                    v_b_2181_ = v___x_2185_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_2208_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(
                                        v_goal_2176_,
                                        v_head_2182_,
                                    );
                                    if lean_obj_tag(v___x_2208_) == 1 {
                                        v_val_2209_ = lean_ctor_get(v___x_2208_, 0);
                                        lean_inc(v_val_2209_);
                                        lean_dec_ref_known(v___x_2208_, 1);
                                        v___x_2210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4;
                                        v___x_2211_ =
                                            l_Lean_Expr_isConstOf(v_val_2209_, v___x_2210_);
                                        lean_dec(v_val_2209_);
                                        if v___x_2211_ == 0 {
                                            lean_dec_ref(v_arg_2200_);
                                            lean_dec_ref(v_arg_2196_);
                                            v_as_x27_2180_ = v_tail_2183_;
                                            v_b_2181_ = v___x_2185_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v___x_2213_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(
                                                v_goal_2176_,
                                                v_arg_2200_,
                                            );
                                            lean_dec_ref(v_arg_2200_);
                                            if lean_obj_tag(v___x_2213_) == 1 {
                                                v_val_2214_ = lean_ctor_get(v___x_2213_, 0);
                                                lean_inc(v_val_2214_);
                                                lean_dec_ref_known(v___x_2213_, 1);
                                                v___x_2215_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(
                                                    v_goal_2176_,
                                                    v_arg_2196_,
                                                );
                                                lean_dec_ref(v_arg_2196_);
                                                if lean_obj_tag(v___x_2215_) == 1 {
                                                    v_val_2216_ = lean_ctor_get(v___x_2215_, 0);
                                                    lean_inc(v_val_2216_);
                                                    lean_dec_ref_known(v___x_2215_, 1);
                                                    v___x_2225_ =
                                                        lean_expr_eqv(v_val_2214_, v_e_2177_);
                                                    if v___x_2225_ == 0 {
                                                        v___y_2223_ = v___x_2225_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_v_2179_);
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
                                                    lean_dec(v___x_2215_);
                                                    lean_dec(v_val_2214_);
                                                    v_as_x27_2180_ = v_tail_2183_;
                                                    v_b_2181_ = v___x_2185_;
                                                    state = 0;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v___x_2213_);
                                                lean_dec_ref(v_arg_2196_);
                                                v_as_x27_2180_ = v_tail_2183_;
                                                v_b_2181_ = v___x_2185_;
                                                state = 0;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_2208_);
                                        lean_dec_ref(v_arg_2200_);
                                        lean_dec_ref(v_arg_2196_);
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
                    lean_dec(v_v_2179_);
                    v___x_2190_ = lean_box((v___y_2187_) as usize);
                    v___x_2191_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2191_, 0, v___x_2190_);
                    v___x_2192_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2192_, 0, v___x_2191_);
                    lean_ctor_set(v___x_2192_, 1, v___x_2184_);
                    return v___x_2192_;
                }
            }
            2 => {
                v___x_2219_ = lean_expr_eqv(v_val_2216_, v_e_2177_);
                lean_dec(v_val_2216_);
                if v___x_2219_ == 0 {
                    lean_dec(v_val_2214_);
                    v___y_2187_ = v___y_2218_;
                    v___y_2188_ = v___x_2219_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_v_2179_);
                    v___x_2220_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_2178_, v_v_2179_, v_val_2214_);
                    lean_dec(v_val_2214_);
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
                    lean_dec(v_val_2216_);
                    lean_dec(v_val_2214_);
                    lean_dec(v_v_2179_);
                    v___x_2224_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6;
                    return v___x_2224_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(
    mut v_goal_2231_: *mut LeanObject,
    mut v_e_2232_: *mut LeanObject,
    mut v_a_2233_: *mut LeanObject,
    mut v_v_2234_: *mut LeanObject,
    mut v_as_x27_2235_: *mut LeanObject,
    mut v_b_2236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2237_: *mut LeanObject = core::ptr::null_mut();
    v_res_2237_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_2231_, v_e_2232_, v_a_2233_, v_v_2234_, v_as_x27_2235_, v_b_2236_);
    lean_dec_ref(v_b_2236_);
    lean_dec(v_as_x27_2235_);
    lean_dec_ref(v_a_2233_);
    lean_dec_ref(v_e_2232_);
    lean_dec_ref(v_goal_2231_);
    return v_res_2237_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2238_: *mut LeanObject,
    mut v_vals_2239_: *mut LeanObject,
    mut v_i_2240_: *mut LeanObject,
    mut v_k_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2242_ = lean_array_get_size(v_keys_2238_);
                v___x_2243_ = lean_nat_dec_lt(v_i_2240_, v___x_2242_);
                if v___x_2243_ == 0 {
                    lean_dec(v_i_2240_);
                    v___x_2244_ = lean_box(0);
                    return v___x_2244_;
                } else {
                    v_k_x27_2245_ = lean_array_fget_borrowed(v_keys_2238_, v_i_2240_);
                    v___x_2246_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2241_,
                            v_k_x27_2245_,
                        );
                    if v___x_2246_ == 0 {
                        v___x_2247_ = lean_unsigned_to_nat(1);
                        v___x_2248_ = lean_nat_add(v_i_2240_, v___x_2247_);
                        lean_dec(v_i_2240_);
                        v_i_2240_ = v___x_2248_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2250_ = lean_array_fget_borrowed(v_vals_2239_, v_i_2240_);
                        lean_dec(v_i_2240_);
                        lean_inc(v___x_2250_);
                        v___x_2251_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                        return v___x_2251_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2252_: *mut LeanObject,
    mut v_vals_2253_: *mut LeanObject,
    mut v_i_2254_: *mut LeanObject,
    mut v_k_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2256_: *mut LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_2252_, v_vals_2253_, v_i_2254_, v_k_2255_);
    lean_dec_ref(v_k_2255_);
    lean_dec_ref(v_vals_2253_);
    lean_dec_ref(v_keys_2252_);
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
    v___x_2261_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0);
    v___x_2262_ = lean_usize_sub(v___x_2261_, v___x_2260_);
    return v___x_2262_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(
    mut v_x_2263_: *mut LeanObject,
    mut v_x_2264_: usize,
    mut v_x_2265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: usize = 0;
    let mut v___x_2269_: usize = 0;
    let mut v___x_2270_: usize = 0;
    let mut v_j_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: usize = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2263_) == 0 {
                    v_es_2266_ = lean_ctor_get(v_x_2263_, 0);
                    v___x_2267_ = lean_box(2);
                    v___x_2268_ = 5usize;
                    v___x_2269_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1);
                    v___x_2270_ = lean_usize_land(v_x_2264_, v___x_2269_);
                    v_j_2271_ = lean_usize_to_nat(v___x_2270_);
                    v___x_2272_ = lean_array_get_borrowed(v___x_2267_, v_es_2266_, v_j_2271_);
                    lean_dec(v_j_2271_);
                    match lean_obj_tag(v___x_2272_) {
                        0 => {
                            v_key_2273_ = lean_ctor_get(v___x_2272_, 0);
                            v_val_2274_ = lean_ctor_get(v___x_2272_, 1);
                            v___x_2275_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2265_, v_key_2273_);
                            if v___x_2275_ == 0 {
                                v___x_2276_ = lean_box(0);
                                return v___x_2276_;
                            } else {
                                lean_inc(v_val_2274_);
                                v___x_2277_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2277_, 0, v_val_2274_);
                                return v___x_2277_;
                            }
                        }
                        1 => {
                            v_node_2278_ = lean_ctor_get(v___x_2272_, 0);
                            v___x_2279_ = lean_usize_shift_right(v_x_2264_, v___x_2268_);
                            v_x_2263_ = v_node_2278_;
                            v_x_2264_ = v___x_2279_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2281_ = lean_box(0);
                            return v___x_2281_;
                        }
                    }
                } else {
                    v_ks_2282_ = lean_ctor_get(v_x_2263_, 0);
                    v_vs_2283_ = lean_ctor_get(v_x_2263_, 1);
                    v___x_2284_ = lean_unsigned_to_nat(0);
                    v___x_2285_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_2282_, v_vs_2283_, v___x_2284_, v_x_2265_);
                    return v___x_2285_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(
    mut v_x_2286_: *mut LeanObject,
    mut v_x_2287_: *mut LeanObject,
    mut v_x_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2615__boxed_2289_: usize = 0;
    let mut v_res_2290_: *mut LeanObject = core::ptr::null_mut();
    v_x_2615__boxed_2289_ = lean_unbox_usize(v_x_2287_);
    lean_dec(v_x_2287_);
    v_res_2290_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_2286_, v_x_2615__boxed_2289_, v_x_2288_);
    lean_dec_ref(v_x_2288_);
    lean_dec_ref(v_x_2286_);
    return v_res_2290_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(
    mut v_x_2291_: *mut LeanObject,
    mut v_x_2292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2293_: u64 = 0;
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2292_);
    v___x_2294_ = lean_uint64_to_usize(v___x_2293_);
    v___x_2295_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_2291_, v___x_2294_, v_x_2292_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(
    mut v_x_2296_: *mut LeanObject,
    mut v_x_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2298_: *mut LeanObject = core::ptr::null_mut();
    v_res_2298_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_2296_, v_x_2297_);
    lean_dec_ref(v_x_2297_);
    lean_dec_ref(v_x_2296_);
    return v_res_2298_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(
    mut v_goal_2299_: *mut LeanObject,
    mut v_a_2300_: *mut LeanObject,
    mut v_e_2301_: *mut LeanObject,
    mut v_v_2302_: *mut LeanObject,
) -> u8 {
    let mut v_toGoalState_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parents_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    v_toGoalState_2303_ = lean_ctor_get(v_goal_2299_, 0);
    v_parents_2304_ = lean_ctor_get(v_toGoalState_2303_, 3);
    v___x_2305_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_parents_2304_, v_e_2301_);
    if lean_obj_tag(v___x_2305_) == 1 {
        let mut v_val_2306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_2310_: *mut LeanObject = core::ptr::null_mut();
        v_val_2306_ = lean_ctor_get(v___x_2305_, 0);
        lean_inc(v_val_2306_);
        lean_dec_ref_known(v___x_2305_, 1);
        v___x_2307_ = l_Lean_Meta_Grind_ParentSet_elems(v_val_2306_);
        lean_dec(v_val_2306_);
        v___x_2308_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0;
        v___x_2309_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_2299_, v_e_2301_, v_a_2300_, v_v_2302_, v___x_2307_, v___x_2308_);
        lean_dec(v___x_2307_);
        v_fst_2310_ = lean_ctor_get(v___x_2309_, 0);
        lean_inc(v_fst_2310_);
        lean_dec_ref(v___x_2309_);
        if lean_obj_tag(v_fst_2310_) == 0 {
            let mut v___x_2311_: u8 = 0;
            v___x_2311_ = 1;
            return v___x_2311_;
        } else {
            let mut v_val_2312_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2313_: u8 = 0;
            v_val_2312_ = lean_ctor_get(v_fst_2310_, 0);
            lean_inc(v_val_2312_);
            lean_dec_ref_known(v_fst_2310_, 1);
            v___x_2313_ = (lean_unbox(v_val_2312_) as u8);
            lean_dec(v_val_2312_);
            return v___x_2313_;
        }
    } else {
        let mut v___x_2314_: u8 = 0;
        lean_dec(v___x_2305_);
        lean_dec(v_v_2302_);
        v___x_2314_ = 1;
        return v___x_2314_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(
    mut v_goal_2315_: *mut LeanObject,
    mut v_a_2316_: *mut LeanObject,
    mut v_e_2317_: *mut LeanObject,
    mut v_v_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2319_: u8 = 0;
    let mut v_r_2320_: *mut LeanObject = core::ptr::null_mut();
    v_res_2319_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(
            v_goal_2315_,
            v_a_2316_,
            v_e_2317_,
            v_v_2318_,
        );
    lean_dec_ref(v_e_2317_);
    lean_dec_ref(v_a_2316_);
    lean_dec_ref(v_goal_2315_);
    v_r_2320_ = lean_box((v_res_2319_) as usize);
    return v_r_2320_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(
    mut v_00_u03b2_2321_: *mut LeanObject,
    mut v_x_2322_: *mut LeanObject,
    mut v_x_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    v___x_2324_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_2322_, v_x_2323_);
    return v___x_2324_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(
    mut v_00_u03b2_2325_: *mut LeanObject,
    mut v_x_2326_: *mut LeanObject,
    mut v_x_2327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2328_: *mut LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(v_00_u03b2_2325_, v_x_2326_, v_x_2327_);
    lean_dec_ref(v_x_2327_);
    lean_dec_ref(v_x_2326_);
    return v_res_2328_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(
    mut v_goal_2329_: *mut LeanObject,
    mut v_e_2330_: *mut LeanObject,
    mut v_a_2331_: *mut LeanObject,
    mut v_v_2332_: *mut LeanObject,
    mut v_as_2333_: *mut LeanObject,
    mut v_as_x27_2334_: *mut LeanObject,
    mut v_b_2335_: *mut LeanObject,
    mut v_a_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    v___x_2337_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_2329_, v_e_2330_, v_a_2331_, v_v_2332_, v_as_x27_2334_, v_b_2335_);
    return v___x_2337_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(
    mut v_goal_2338_: *mut LeanObject,
    mut v_e_2339_: *mut LeanObject,
    mut v_a_2340_: *mut LeanObject,
    mut v_v_2341_: *mut LeanObject,
    mut v_as_2342_: *mut LeanObject,
    mut v_as_x27_2343_: *mut LeanObject,
    mut v_b_2344_: *mut LeanObject,
    mut v_a_2345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2346_: *mut LeanObject = core::ptr::null_mut();
    v_res_2346_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(v_goal_2338_, v_e_2339_, v_a_2340_, v_v_2341_, v_as_2342_, v_as_x27_2343_, v_b_2344_, v_a_2345_);
    lean_dec_ref(v_b_2344_);
    lean_dec(v_as_x27_2343_);
    lean_dec(v_as_2342_);
    lean_dec_ref(v_a_2340_);
    lean_dec_ref(v_e_2339_);
    lean_dec_ref(v_goal_2338_);
    return v_res_2346_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(
    mut v_00_u03b2_2347_: *mut LeanObject,
    mut v_x_2348_: *mut LeanObject,
    mut v_x_2349_: usize,
    mut v_x_2350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    v___x_2351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_2348_, v_x_2349_, v_x_2350_);
    return v___x_2351_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(
    mut v_00_u03b2_2352_: *mut LeanObject,
    mut v_x_2353_: *mut LeanObject,
    mut v_x_2354_: *mut LeanObject,
    mut v_x_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2716__boxed_2356_: usize = 0;
    let mut v_res_2357_: *mut LeanObject = core::ptr::null_mut();
    v_x_2716__boxed_2356_ = lean_unbox_usize(v_x_2354_);
    lean_dec(v_x_2354_);
    v_res_2357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_2352_, v_x_2353_, v_x_2716__boxed_2356_, v_x_2355_);
    lean_dec_ref(v_x_2355_);
    lean_dec_ref(v_x_2353_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2358_: *mut LeanObject,
    mut v_keys_2359_: *mut LeanObject,
    mut v_vals_2360_: *mut LeanObject,
    mut v_heq_2361_: *mut LeanObject,
    mut v_i_2362_: *mut LeanObject,
    mut v_k_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2364_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_2359_, v_vals_2360_, v_i_2362_, v_k_2363_);
    return v___x_2364_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2365_: *mut LeanObject,
    mut v_keys_2366_: *mut LeanObject,
    mut v_vals_2367_: *mut LeanObject,
    mut v_heq_2368_: *mut LeanObject,
    mut v_i_2369_: *mut LeanObject,
    mut v_k_2370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2371_: *mut LeanObject = core::ptr::null_mut();
    v_res_2371_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(v_00_u03b2_2365_, v_keys_2366_, v_vals_2367_, v_heq_2368_, v_i_2369_, v_k_2370_);
    lean_dec_ref(v_k_2370_);
    lean_dec_ref(v_vals_2367_);
    lean_dec_ref(v_keys_2366_);
    return v_res_2371_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(
    mut v_a_2372_: *mut LeanObject,
    mut v_x_2373_: *mut LeanObject,
) -> u8 {
    let mut v___x_2374_: u8 = 0;
    let mut v_key_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2373_) == 0 {
                    v___x_2374_ = 0;
                    return v___x_2374_;
                } else {
                    v_key_2375_ = lean_ctor_get(v_x_2373_, 0);
                    v_tail_2376_ = lean_ctor_get(v_x_2373_, 2);
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
    mut v_a_2379_: *mut LeanObject,
    mut v_x_2380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2381_: u8 = 0;
    let mut v_r_2382_: *mut LeanObject = core::ptr::null_mut();
    v_res_2381_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_2379_, v_x_2380_);
    lean_dec(v_x_2380_);
    lean_dec(v_a_2379_);
    v_r_2382_ = lean_box((v_res_2381_) as usize);
    return v_r_2382_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v_natZero_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_2384_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_2383_ = lean_unsigned_to_nat(0);
    v_intZero_2384_ = lean_nat_to_int(v_natZero_2383_);
    return v_intZero_2384_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(
    mut v_m_2385_: *mut LeanObject,
    mut v_a_2386_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: u8 = 0;
    let mut v_intZero_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_2405_: u8 = 0;
    let mut v_a_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: u64 = 0;
    let mut v_abs_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2387_ = lean_ctor_get(v_m_2385_, 1);
                v___x_2388_ = lean_array_get_size(v_buckets_2387_);
                v_intZero_2404_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
                v_isNeg_2405_ = lean_int_dec_lt(v_a_2386_, v_intZero_2404_);
                if v_isNeg_2405_ == 0 {
                    v_a_2406_ = lean_nat_abs(v_a_2386_);
                    v___x_2407_ = lean_unsigned_to_nat(2);
                    v___x_2408_ = lean_nat_mul(v___x_2407_, v_a_2406_);
                    lean_dec(v_a_2406_);
                    v___x_2409_ = lean_uint64_of_nat(v___x_2408_);
                    lean_dec(v___x_2408_);
                    v___y_2390_ = v___x_2409_;
                    state = 1;
                    continue;
                } else {
                    v_abs_2410_ = lean_nat_abs(v_a_2386_);
                    v_one_2411_ = lean_unsigned_to_nat(1);
                    v_a_2412_ = lean_nat_sub(v_abs_2410_, v_one_2411_);
                    lean_dec(v_abs_2410_);
                    v___x_2413_ = lean_unsigned_to_nat(2);
                    v___x_2414_ = lean_nat_mul(v___x_2413_, v_a_2412_);
                    lean_dec(v_a_2412_);
                    v___x_2415_ = lean_nat_add(v___x_2414_, v_one_2411_);
                    lean_dec(v___x_2414_);
                    v___x_2416_ = lean_uint64_of_nat(v___x_2415_);
                    lean_dec(v___x_2415_);
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
    mut v_m_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2419_: u8 = 0;
    let mut v_r_2420_: *mut LeanObject = core::ptr::null_mut();
    v_res_2419_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_2417_, v_a_2418_);
    lean_dec(v_a_2418_);
    lean_dec_ref(v_m_2417_);
    v_r_2420_ = lean_box((v_res_2419_) as usize);
    return v_r_2420_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0()
-> *mut LeanObject {
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    v___x_2421_ = lean_unsigned_to_nat(1);
    v___x_2422_ = lean_nat_to_int(v___x_2421_);
    return v___x_2422_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(
    mut v_goal_2423_: *mut LeanObject,
    mut v_a_2424_: *mut LeanObject,
    mut v_e_2425_: *mut LeanObject,
    mut v_alreadyUsed_2426_: *mut LeanObject,
    mut v_next_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2428_: u8 = 0;
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_alreadyUsed_2426_, v_next_2427_);
                if v___x_2428_ == 0 {
                    lean_inc(v_next_2427_);
                    v___x_2429_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_2423_, v_a_2424_, v_e_2425_, v_next_2427_);
                    if v___x_2429_ == 0 {
                        v___x_2430_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                        v___x_2431_ = lean_int_add(v_next_2427_, v___x_2430_);
                        lean_dec(v_next_2427_);
                        v_next_2427_ = v___x_2431_;
                        state = 0;
                        continue;
                    } else {
                        return v_next_2427_;
                    }
                } else {
                    v___x_2433_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                    v___x_2434_ = lean_int_add(v_next_2427_, v___x_2433_);
                    lean_dec(v_next_2427_);
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
    mut v_goal_2436_: *mut LeanObject,
    mut v_a_2437_: *mut LeanObject,
    mut v_e_2438_: *mut LeanObject,
    mut v_alreadyUsed_2439_: *mut LeanObject,
    mut v_next_2440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2441_: *mut LeanObject = core::ptr::null_mut();
    v_res_2441_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_2436_, v_a_2437_, v_e_2438_, v_alreadyUsed_2439_, v_next_2440_);
    lean_dec_ref(v_alreadyUsed_2439_);
    lean_dec_ref(v_e_2438_);
    lean_dec_ref(v_a_2437_);
    lean_dec_ref(v_goal_2436_);
    return v_res_2441_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(
    mut v_00_u03b2_2442_: *mut LeanObject,
    mut v_m_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
) -> u8 {
    let mut v___x_2445_: u8 = 0;
    v___x_2445_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_2443_, v_a_2444_);
    return v___x_2445_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(
    mut v_00_u03b2_2446_: *mut LeanObject,
    mut v_m_2447_: *mut LeanObject,
    mut v_a_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2449_: u8 = 0;
    let mut v_r_2450_: *mut LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(v_00_u03b2_2446_, v_m_2447_, v_a_2448_);
    lean_dec(v_a_2448_);
    lean_dec_ref(v_m_2447_);
    v_r_2450_ = lean_box((v_res_2449_) as usize);
    return v_r_2450_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(
    mut v_00_u03b2_2451_: *mut LeanObject,
    mut v_a_2452_: *mut LeanObject,
    mut v_x_2453_: *mut LeanObject,
) -> u8 {
    let mut v___x_2454_: u8 = 0;
    v___x_2454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_2452_, v_x_2453_);
    return v___x_2454_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
    mut v_x_2457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2458_: u8 = 0;
    let mut v_r_2459_: *mut LeanObject = core::ptr::null_mut();
    v_res_2458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(v_00_u03b2_2455_, v_a_2456_, v_x_2457_);
    lean_dec(v_x_2457_);
    lean_dec(v_a_2456_);
    v_r_2459_ = lean_box((v_res_2458_) as usize);
    return v_r_2459_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_pickUnusedValue(
    mut v_goal_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
    mut v_e_2462_: *mut LeanObject,
    mut v_next_2463_: *mut LeanObject,
    mut v_alreadyUsed_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    v___x_2465_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_2460_, v_a_2461_, v_e_2462_, v_alreadyUsed_2464_, v_next_2463_);
    return v___x_2465_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(
    mut v_goal_2466_: *mut LeanObject,
    mut v_a_2467_: *mut LeanObject,
    mut v_e_2468_: *mut LeanObject,
    mut v_next_2469_: *mut LeanObject,
    mut v_alreadyUsed_2470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2471_: *mut LeanObject = core::ptr::null_mut();
    v_res_2471_ = l_Lean_Meta_Grind_Arith_pickUnusedValue(
        v_goal_2466_,
        v_a_2467_,
        v_e_2468_,
        v_next_2469_,
        v_alreadyUsed_2470_,
    );
    lean_dec_ref(v_alreadyUsed_2470_);
    lean_dec_ref(v_e_2468_);
    lean_dec_ref(v_a_2467_);
    lean_dec_ref(v_goal_2466_);
    return v_res_2471_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isInterpretedTerm(mut v_e_2555_: *mut LeanObject) -> u8 {
    let mut v___y_2557_: u8 = 0;
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: u8 = 0;
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: u8 = 0;
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u8 = 0;
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: u8 = 0;
    let mut v_a_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: u8 = 0;
    let mut v___x_2593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2555_);
                v___x_2592_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_2555_);
                if v___x_2592_ == 0 {
                    lean_inc_ref(v_e_2555_);
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
                                                                                        if lean_obj_tag(v_e_2555_) == 9 {
v_a_2590_ = lean_ctor_get(v_e_2555_, 0);
lean_inc_ref(v_a_2590_);
lean_dec_ref_known(v_e_2555_, 1);
if lean_obj_tag(v_a_2590_) == 0 {
lean_dec_ref_known(v_a_2590_, 1);
v___x_2591_ = 1;
return v___x_2591_;
} else {
lean_dec_ref(v_a_2590_);
return v___x_2589_;
}
} else {
lean_dec_ref(v_e_2555_);
return v___x_2589_;
}
                                                                                    } else {
                                                                                        lean_dec_ref(v_e_2555_);
                                                                                        return v___x_2589_;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_e_2555_,
                                                                                    );
                                                                                    return v___x_2587_;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_e_2555_,
                                                                                );
                                                                                return v___x_2585_;
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(v_e_2555_);
                                                                            return v___x_2583_;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_e_2555_);
                                                                        return v___x_2581_;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_e_2555_);
                                                                    return v___x_2580_;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_e_2555_);
                                                                return v___x_2579_;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_e_2555_);
                                                            return v___x_2577_;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_e_2555_);
                                                        return v___x_2575_;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_e_2555_);
                                                    return v___x_2573_;
                                                }
                                            } else {
                                                lean_dec_ref(v_e_2555_);
                                                return v___x_2571_;
                                            }
                                        } else {
                                            lean_dec_ref(v_e_2555_);
                                            return v___x_2569_;
                                        }
                                    } else {
                                        lean_dec_ref(v_e_2555_);
                                        return v___x_2567_;
                                    }
                                } else {
                                    lean_dec_ref(v_e_2555_);
                                    return v___x_2565_;
                                }
                            } else {
                                lean_dec_ref(v_e_2555_);
                                return v___x_2563_;
                            }
                        } else {
                            lean_dec_ref(v_e_2555_);
                            return v___x_2561_;
                        }
                    } else {
                        lean_dec_ref(v_e_2555_);
                        return v___x_2559_;
                    }
                } else {
                    lean_dec_ref(v_e_2555_);
                    return v___y_2557_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(
    mut v_e_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2595_: u8 = 0;
    let mut v_r_2596_: *mut LeanObject = core::ptr::null_mut();
    v_res_2595_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_2594_);
    v_r_2596_ = lean_box((v_res_2595_) as usize);
    return v_r_2596_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_2597_: *mut LeanObject,
    mut v_x_2598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2598_) == 0 {
                    return v_x_2597_;
                } else {
                    v_key_2599_ = lean_ctor_get(v_x_2598_, 0);
                    v_value_2600_ = lean_ctor_get(v_x_2598_, 1);
                    v_tail_2601_ = lean_ctor_get(v_x_2598_, 2);
                    v_isSharedCheck_2624_ = (!lean_is_exclusive(v_x_2598_)) as u8;
                    if v_isSharedCheck_2624_ == 0 {
                        v___x_2603_ = v_x_2598_;
                        v_isShared_2604_ = v_isSharedCheck_2624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2601_);
                        lean_inc(v_value_2600_);
                        lean_inc(v_key_2599_);
                        lean_dec(v_x_2598_);
                        v___x_2603_ = lean_box(0);
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
                lean_inc(v___x_2618_);
                if v_isShared_2604_ == 0 {
                    lean_ctor_set(v___x_2603_, 2, v___x_2618_);
                    v___x_2620_ = v___x_2603_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_key_2599_);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_value_2600_);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 2, v___x_2618_);
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
    mut v_i_2625_: *mut LeanObject,
    mut v_source_2626_: *mut LeanObject,
    mut v_target_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v_es_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2628_ = lean_array_get_size(v_source_2626_);
                v___x_2629_ = lean_nat_dec_lt(v_i_2625_, v___x_2628_);
                if v___x_2629_ == 0 {
                    lean_dec_ref(v_source_2626_);
                    lean_dec(v_i_2625_);
                    return v_target_2627_;
                } else {
                    v_es_2630_ = lean_array_fget(v_source_2626_, v_i_2625_);
                    v___x_2631_ = lean_box(0);
                    v_source_2632_ = lean_array_fset(v_source_2626_, v_i_2625_, v___x_2631_);
                    v_target_2633_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_2627_, v_es_2630_);
                    v___x_2634_ = lean_unsigned_to_nat(1);
                    v___x_2635_ = lean_nat_add(v_i_2625_, v___x_2634_);
                    lean_dec(v_i_2625_);
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
    mut v_data_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v___x_2638_ = lean_array_get_size(v_data_2637_);
    v___x_2639_ = lean_unsigned_to_nat(2);
    v_nbuckets_2640_ = lean_nat_mul(v___x_2638_, v___x_2639_);
    v___x_2641_ = lean_unsigned_to_nat(0);
    v___x_2642_ = lean_box(0);
    v___x_2643_ = lean_mk_array(v_nbuckets_2640_, v___x_2642_);
    v___x_2644_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_2641_, v_data_2637_, v___x_2643_);
    return v___x_2644_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(
    mut v_a_2645_: *mut LeanObject,
    mut v_b_2646_: *mut LeanObject,
    mut v_x_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2647_) == 0 {
                    lean_dec(v_b_2646_);
                    lean_dec_ref(v_a_2645_);
                    return v_x_2647_;
                } else {
                    v_key_2648_ = lean_ctor_get(v_x_2647_, 0);
                    v_value_2649_ = lean_ctor_get(v_x_2647_, 1);
                    v_tail_2650_ = lean_ctor_get(v_x_2647_, 2);
                    v_isSharedCheck_2662_ = (!lean_is_exclusive(v_x_2647_)) as u8;
                    if v_isSharedCheck_2662_ == 0 {
                        v___x_2652_ = v_x_2647_;
                        v_isShared_2653_ = v_isSharedCheck_2662_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2650_);
                        lean_inc(v_value_2649_);
                        lean_inc(v_key_2648_);
                        lean_dec(v_x_2647_);
                        v___x_2652_ = lean_box(0);
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
                        lean_ctor_set(v___x_2652_, 2, v___x_2655_);
                        v___x_2657_ = v___x_2652_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_key_2648_);
                        lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_value_2649_);
                        lean_ctor_set(v_reuseFailAlloc_2658_, 2, v___x_2655_);
                        v___x_2657_ = v_reuseFailAlloc_2658_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2649_);
                    lean_dec(v_key_2648_);
                    if v_isShared_2653_ == 0 {
                        lean_ctor_set(v___x_2652_, 1, v_b_2646_);
                        lean_ctor_set(v___x_2652_, 0, v_a_2645_);
                        v___x_2660_ = v___x_2652_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2645_);
                        lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_b_2646_);
                        lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_tail_2650_);
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
    mut v_a_2663_: *mut LeanObject,
    mut v_x_2664_: *mut LeanObject,
) -> u8 {
    let mut v___x_2665_: u8 = 0;
    let mut v_key_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2664_) == 0 {
                    v___x_2665_ = 0;
                    return v___x_2665_;
                } else {
                    v_key_2666_ = lean_ctor_get(v_x_2664_, 0);
                    v_tail_2667_ = lean_ctor_get(v_x_2664_, 2);
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
    mut v_a_2670_: *mut LeanObject,
    mut v_x_2671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2672_: u8 = 0;
    let mut v_r_2673_: *mut LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_2670_, v_x_2671_);
    lean_dec(v_x_2671_);
    lean_dec_ref(v_a_2670_);
    v_r_2673_ = lean_box((v_res_2672_) as usize);
    return v_r_2673_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(
    mut v_m_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
    mut v_b_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: u8 = 0;
    let mut v_val_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2677_ = lean_ctor_get(v_m_2674_, 0);
                v_buckets_2678_ = lean_ctor_get(v_m_2674_, 1);
                v_isSharedCheck_2721_ = (!lean_is_exclusive(v_m_2674_)) as u8;
                if v_isSharedCheck_2721_ == 0 {
                    v___x_2680_ = v_m_2674_;
                    v_isShared_2681_ = v_isSharedCheck_2721_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2678_);
                    lean_inc(v_size_2677_);
                    lean_dec(v_m_2674_);
                    v___x_2680_ = lean_box(0);
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
                    v___x_2697_ = lean_unsigned_to_nat(1);
                    v_size_x27_2698_ = lean_nat_add(v_size_2677_, v___x_2697_);
                    lean_dec(v_size_2677_);
                    lean_inc(v_bkt_2695_);
                    v___x_2699_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2699_, 0, v_a_2675_);
                    lean_ctor_set(v___x_2699_, 1, v_b_2676_);
                    lean_ctor_set(v___x_2699_, 2, v_bkt_2695_);
                    v_buckets_x27_2700_ =
                        lean_array_uset(v_buckets_2678_, v___x_2694_, v___x_2699_);
                    v___x_2701_ = lean_unsigned_to_nat(4);
                    v___x_2702_ = lean_nat_mul(v_size_x27_2698_, v___x_2701_);
                    v___x_2703_ = lean_unsigned_to_nat(3);
                    v___x_2704_ = lean_nat_div(v___x_2702_, v___x_2703_);
                    lean_dec(v___x_2702_);
                    v___x_2705_ = lean_array_get_size(v_buckets_x27_2700_);
                    v___x_2706_ = lean_nat_dec_le(v___x_2704_, v___x_2705_);
                    lean_dec(v___x_2704_);
                    if v___x_2706_ == 0 {
                        v_val_2707_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_2700_);
                        if v_isShared_2681_ == 0 {
                            lean_ctor_set(v___x_2680_, 1, v_val_2707_);
                            lean_ctor_set(v___x_2680_, 0, v_size_x27_2698_);
                            v___x_2709_ = v___x_2680_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_size_x27_2698_);
                            lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_val_2707_);
                            v___x_2709_ = v_reuseFailAlloc_2710_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2681_ == 0 {
                            lean_ctor_set(v___x_2680_, 1, v_buckets_x27_2700_);
                            lean_ctor_set(v___x_2680_, 0, v_size_x27_2698_);
                            v___x_2712_ = v___x_2680_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_size_x27_2698_);
                            lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_buckets_x27_2700_);
                            v___x_2712_ = v_reuseFailAlloc_2713_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2695_);
                    v___x_2714_ = lean_box(0);
                    v_buckets_x27_2715_ =
                        lean_array_uset(v_buckets_2678_, v___x_2694_, v___x_2714_);
                    v___x_2716_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_2675_, v_b_2676_, v_bkt_2695_);
                    v___x_2717_ = lean_array_uset(v_buckets_x27_2715_, v___x_2694_, v___x_2716_);
                    if v_isShared_2681_ == 0 {
                        lean_ctor_set(v___x_2680_, 1, v___x_2717_);
                        v___x_2719_ = v___x_2680_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_size_2677_);
                        lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2717_);
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
    mut v_v_2722_: *mut LeanObject,
    mut v_as_x27_2723_: *mut LeanObject,
    mut v_b_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2723_) == 0 {
                    lean_dec_ref(v_v_2722_);
                    return v_b_2724_;
                } else {
                    v_head_2725_ = lean_ctor_get(v_as_x27_2723_, 0);
                    v_tail_2726_ = lean_ctor_get(v_as_x27_2723_, 1);
                    lean_inc_ref(v_v_2722_);
                    lean_inc(v_head_2725_);
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
    mut v_v_2729_: *mut LeanObject,
    mut v_as_x27_2730_: *mut LeanObject,
    mut v_b_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2732_: *mut LeanObject = core::ptr::null_mut();
    v_res_2732_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(
        v_v_2729_,
        v_as_x27_2730_,
        v_b_2731_,
    );
    lean_dec(v_as_x27_2730_);
    return v_res_2732_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_assignEqc(
    mut v_goal_2733_: *mut LeanObject,
    mut v_e_2734_: *mut LeanObject,
    mut v_v_2735_: *mut LeanObject,
    mut v_a_2736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2737_: u8 = 0;
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    v___x_2737_ = 0;
    v___x_2738_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_2733_, v_e_2734_, v___x_2737_);
    v___x_2739_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(
        v_v_2735_,
        v___x_2738_,
        v_a_2736_,
    );
    lean_dec(v___x_2738_);
    return v___x_2739_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_assignEqc___boxed(
    mut v_goal_2740_: *mut LeanObject,
    mut v_e_2741_: *mut LeanObject,
    mut v_v_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2744_: *mut LeanObject = core::ptr::null_mut();
    v_res_2744_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_2740_, v_e_2741_, v_v_2742_, v_a_2743_);
    lean_dec_ref(v_goal_2740_);
    return v_res_2744_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(
    mut v_00_u03b2_2745_: *mut LeanObject,
    mut v_m_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
    mut v_b_2748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    v___x_2749_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_2746_, v_a_2747_, v_b_2748_);
    return v___x_2749_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(
    mut v_v_2750_: *mut LeanObject,
    mut v_as_2751_: *mut LeanObject,
    mut v_as_x27_2752_: *mut LeanObject,
    mut v_b_2753_: *mut LeanObject,
    mut v_a_2754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    v___x_2755_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(
        v_v_2750_,
        v_as_x27_2752_,
        v_b_2753_,
    );
    return v___x_2755_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(
    mut v_v_2756_: *mut LeanObject,
    mut v_as_2757_: *mut LeanObject,
    mut v_as_x27_2758_: *mut LeanObject,
    mut v_b_2759_: *mut LeanObject,
    mut v_a_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2761_: *mut LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(
        v_v_2756_,
        v_as_2757_,
        v_as_x27_2758_,
        v_b_2759_,
        v_a_2760_,
    );
    lean_dec(v_as_x27_2758_);
    lean_dec(v_as_2757_);
    return v_res_2761_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(
    mut v_00_u03b2_2762_: *mut LeanObject,
    mut v_a_2763_: *mut LeanObject,
    mut v_x_2764_: *mut LeanObject,
) -> u8 {
    let mut v___x_2765_: u8 = 0;
    v___x_2765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_2763_, v_x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(
    mut v_00_u03b2_2766_: *mut LeanObject,
    mut v_a_2767_: *mut LeanObject,
    mut v_x_2768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2769_: u8 = 0;
    let mut v_r_2770_: *mut LeanObject = core::ptr::null_mut();
    v_res_2769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_2766_, v_a_2767_, v_x_2768_);
    lean_dec(v_x_2768_);
    lean_dec_ref(v_a_2767_);
    v_r_2770_ = lean_box((v_res_2769_) as usize);
    return v_r_2770_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(
    mut v_00_u03b2_2771_: *mut LeanObject,
    mut v_data_2772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    v___x_2773_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_2772_);
    return v___x_2773_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(
    mut v_00_u03b2_2774_: *mut LeanObject,
    mut v_a_2775_: *mut LeanObject,
    mut v_b_2776_: *mut LeanObject,
    mut v_x_2777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_2775_, v_b_2776_, v_x_2777_);
    return v___x_2778_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2779_: *mut LeanObject,
    mut v_i_2780_: *mut LeanObject,
    mut v_source_2781_: *mut LeanObject,
    mut v_target_2782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    v___x_2783_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_2780_, v_source_2781_, v_target_2782_);
    return v___x_2783_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2784_: *mut LeanObject,
    mut v_x_2785_: *mut LeanObject,
    mut v_x_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    v___x_2787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2785_, v_x_2786_);
    return v___x_2787_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_x_2788_: *mut LeanObject,
    mut v_x_2789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_2817_: u8 = 0;
    let mut v_a_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u64 = 0;
    let mut v_abs_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u64 = 0;
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2789_) == 0 {
                    return v_x_2788_;
                } else {
                    v_key_2790_ = lean_ctor_get(v_x_2789_, 0);
                    v_value_2791_ = lean_ctor_get(v_x_2789_, 1);
                    v_tail_2792_ = lean_ctor_get(v_x_2789_, 2);
                    v_isSharedCheck_2829_ = (!lean_is_exclusive(v_x_2789_)) as u8;
                    if v_isSharedCheck_2829_ == 0 {
                        v___x_2794_ = v_x_2789_;
                        v_isShared_2795_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2792_);
                        lean_inc(v_value_2791_);
                        lean_inc(v_key_2790_);
                        lean_dec(v_x_2789_);
                        v___x_2794_ = lean_box(0);
                        v_isShared_2795_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2796_ = lean_array_get_size(v_x_2788_);
                v_intZero_2816_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
                v_isNeg_2817_ = lean_int_dec_lt(v_key_2790_, v_intZero_2816_);
                if v_isNeg_2817_ == 0 {
                    v_a_2818_ = lean_nat_abs(v_key_2790_);
                    v___x_2819_ = lean_unsigned_to_nat(2);
                    v___x_2820_ = lean_nat_mul(v___x_2819_, v_a_2818_);
                    lean_dec(v_a_2818_);
                    v___x_2821_ = lean_uint64_of_nat(v___x_2820_);
                    lean_dec(v___x_2820_);
                    v___y_2798_ = v___x_2821_;
                    state = 2;
                    continue;
                } else {
                    v_abs_2822_ = lean_nat_abs(v_key_2790_);
                    v_one_2823_ = lean_unsigned_to_nat(1);
                    v_a_2824_ = lean_nat_sub(v_abs_2822_, v_one_2823_);
                    lean_dec(v_abs_2822_);
                    v___x_2825_ = lean_unsigned_to_nat(2);
                    v___x_2826_ = lean_nat_mul(v___x_2825_, v_a_2824_);
                    lean_dec(v_a_2824_);
                    v___x_2827_ = lean_nat_add(v___x_2826_, v_one_2823_);
                    lean_dec(v___x_2826_);
                    v___x_2828_ = lean_uint64_of_nat(v___x_2827_);
                    lean_dec(v___x_2827_);
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
                lean_inc(v___x_2810_);
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 2, v___x_2810_);
                    v___x_2812_ = v___x_2794_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_key_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_value_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 2, v___x_2810_);
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
    mut v_i_2830_: *mut LeanObject,
    mut v_source_2831_: *mut LeanObject,
    mut v_target_2832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    let mut v_es_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2833_ = lean_array_get_size(v_source_2831_);
                v___x_2834_ = lean_nat_dec_lt(v_i_2830_, v___x_2833_);
                if v___x_2834_ == 0 {
                    lean_dec_ref(v_source_2831_);
                    lean_dec(v_i_2830_);
                    return v_target_2832_;
                } else {
                    v_es_2835_ = lean_array_fget(v_source_2831_, v_i_2830_);
                    v___x_2836_ = lean_box(0);
                    v_source_2837_ = lean_array_fset(v_source_2831_, v_i_2830_, v___x_2836_);
                    v_target_2838_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_2832_, v_es_2835_);
                    v___x_2839_ = lean_unsigned_to_nat(1);
                    v___x_2840_ = lean_nat_add(v_i_2830_, v___x_2839_);
                    lean_dec(v_i_2830_);
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
    mut v_data_2842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    v___x_2843_ = lean_array_get_size(v_data_2842_);
    v___x_2844_ = lean_unsigned_to_nat(2);
    v_nbuckets_2845_ = lean_nat_mul(v___x_2843_, v___x_2844_);
    v___x_2846_ = lean_unsigned_to_nat(0);
    v___x_2847_ = lean_box(0);
    v___x_2848_ = lean_mk_array(v_nbuckets_2845_, v___x_2847_);
    v___x_2849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_2846_, v_data_2842_, v___x_2848_);
    return v___x_2849_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(
    mut v_m_2850_: *mut LeanObject,
    mut v_a_2851_: *mut LeanObject,
    mut v_b_2852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: u8 = 0;
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2873_: u8 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: u8 = 0;
    let mut v_val_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut v_unused_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_2895_: u8 = 0;
    let mut v_a_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u64 = 0;
    let mut v_abs_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2853_ = lean_ctor_get(v_m_2850_, 0);
                v_buckets_2854_ = lean_ctor_get(v_m_2850_, 1);
                v___x_2855_ = lean_array_get_size(v_buckets_2854_);
                v_intZero_2894_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
                v_isNeg_2895_ = lean_int_dec_lt(v_a_2851_, v_intZero_2894_);
                if v_isNeg_2895_ == 0 {
                    v_a_2896_ = lean_nat_abs(v_a_2851_);
                    v___x_2897_ = lean_unsigned_to_nat(2);
                    v___x_2898_ = lean_nat_mul(v___x_2897_, v_a_2896_);
                    lean_dec(v_a_2896_);
                    v___x_2899_ = lean_uint64_of_nat(v___x_2898_);
                    lean_dec(v___x_2898_);
                    v___y_2857_ = v___x_2899_;
                    state = 1;
                    continue;
                } else {
                    v_abs_2900_ = lean_nat_abs(v_a_2851_);
                    v_one_2901_ = lean_unsigned_to_nat(1);
                    v_a_2902_ = lean_nat_sub(v_abs_2900_, v_one_2901_);
                    lean_dec(v_abs_2900_);
                    v___x_2903_ = lean_unsigned_to_nat(2);
                    v___x_2904_ = lean_nat_mul(v___x_2903_, v_a_2902_);
                    lean_dec(v_a_2902_);
                    v___x_2905_ = lean_nat_add(v___x_2904_, v_one_2901_);
                    lean_dec(v___x_2904_);
                    v___x_2906_ = lean_uint64_of_nat(v___x_2905_);
                    lean_dec(v___x_2905_);
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
                    lean_inc_ref(v_buckets_2854_);
                    lean_inc(v_size_2853_);
                    v_isSharedCheck_2891_ = (!lean_is_exclusive(v_m_2850_)) as u8;
                    if v_isSharedCheck_2891_ == 0 {
                        v_unused_2892_ = lean_ctor_get(v_m_2850_, 1);
                        lean_dec(v_unused_2892_);
                        v_unused_2893_ = lean_ctor_get(v_m_2850_, 0);
                        lean_dec(v_unused_2893_);
                        v___x_2872_ = v_m_2850_;
                        v_isShared_2873_ = v_isSharedCheck_2891_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_2850_);
                        v___x_2872_ = lean_box(0);
                        v_isShared_2873_ = v_isSharedCheck_2891_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2852_);
                    lean_dec(v_a_2851_);
                    return v_m_2850_;
                }
            }
            2 => {
                v___x_2874_ = lean_unsigned_to_nat(1);
                v_size_x27_2875_ = lean_nat_add(v_size_2853_, v___x_2874_);
                lean_dec(v_size_2853_);
                lean_inc(v_bkt_2869_);
                v___x_2876_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2876_, 0, v_a_2851_);
                lean_ctor_set(v___x_2876_, 1, v_b_2852_);
                lean_ctor_set(v___x_2876_, 2, v_bkt_2869_);
                v_buckets_x27_2877_ = lean_array_uset(v_buckets_2854_, v___x_2868_, v___x_2876_);
                v___x_2878_ = lean_unsigned_to_nat(4);
                v___x_2879_ = lean_nat_mul(v_size_x27_2875_, v___x_2878_);
                v___x_2880_ = lean_unsigned_to_nat(3);
                v___x_2881_ = lean_nat_div(v___x_2879_, v___x_2880_);
                lean_dec(v___x_2879_);
                v___x_2882_ = lean_array_get_size(v_buckets_x27_2877_);
                v___x_2883_ = lean_nat_dec_le(v___x_2881_, v___x_2882_);
                lean_dec(v___x_2881_);
                if v___x_2883_ == 0 {
                    v_val_2884_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_2877_);
                    if v_isShared_2873_ == 0 {
                        lean_ctor_set(v___x_2872_, 1, v_val_2884_);
                        lean_ctor_set(v___x_2872_, 0, v_size_x27_2875_);
                        v___x_2886_ = v___x_2872_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_size_x27_2875_);
                        lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_val_2884_);
                        v___x_2886_ = v_reuseFailAlloc_2887_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2873_ == 0 {
                        lean_ctor_set(v___x_2872_, 1, v_buckets_x27_2877_);
                        lean_ctor_set(v___x_2872_, 0, v_size_x27_2875_);
                        v___x_2889_ = v___x_2872_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_size_x27_2875_);
                        lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_buckets_x27_2877_);
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
    mut v_goal_2907_: *mut LeanObject,
    mut v_isTarget_2908_: *mut LeanObject,
    mut v_as_2909_: *mut LeanObject,
    mut v_sz_2910_: usize,
    mut v_i_2911_: usize,
    mut v_b_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
    mut v___y_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2923_: u8 = 0;
    let mut v_a_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_fst_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: usize = 0;
    let mut v_reuseFailAlloc_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: u8 = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v_isSharedCheck_2991_: u8 = 0;
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut v_unused_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_unused_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2918_ = lean_usize_dec_lt(v_i_2911_, v_sz_2910_);
                if v___x_2918_ == 0 {
                    lean_dec_ref(v_isTarget_2908_);
                    v___x_2919_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2919_, 0, v_b_2912_);
                    return v___x_2919_;
                } else {
                    v_snd_2920_ = lean_ctor_get(v_b_2912_, 1);
                    v_isSharedCheck_3002_ = (!lean_is_exclusive(v_b_2912_)) as u8;
                    if v_isSharedCheck_3002_ == 0 {
                        v_unused_3003_ = lean_ctor_get(v_b_2912_, 0);
                        lean_dec(v_unused_3003_);
                        v___x_2922_ = v_b_2912_;
                        v_isShared_2923_ = v_isSharedCheck_3002_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2920_);
                        lean_dec(v_b_2912_);
                        v___x_2922_ = lean_box(0);
                        v_isShared_2923_ = v_isSharedCheck_3002_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2924_ = lean_array_uget_borrowed(v_as_2909_, v_i_2911_);
                lean_inc(v_a_2924_);
                v___x_2925_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_2907_,
                    v_a_2924_,
                    v___y_2913_,
                    v___y_2914_,
                    v___y_2915_,
                    v___y_2916_,
                );
                if lean_obj_tag(v___x_2925_) == 0 {
                    v_snd_2926_ = lean_ctor_get(v_snd_2920_, 1);
                    lean_inc(v_snd_2926_);
                    v_a_2927_ = lean_ctor_get(v___x_2925_, 0);
                    lean_inc(v_a_2927_);
                    lean_dec_ref_known(v___x_2925_, 1);
                    v_fst_2928_ = lean_ctor_get(v_snd_2920_, 0);
                    v_isSharedCheck_2992_ = (!lean_is_exclusive(v_snd_2920_)) as u8;
                    if v_isSharedCheck_2992_ == 0 {
                        v_unused_2993_ = lean_ctor_get(v_snd_2920_, 1);
                        lean_dec(v_unused_2993_);
                        v___x_2930_ = v_snd_2920_;
                        v_isShared_2931_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_2928_);
                        lean_dec(v_snd_2920_);
                        v___x_2930_ = lean_box(0);
                        v_isShared_2931_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2922_);
                    lean_dec(v_snd_2920_);
                    lean_dec_ref(v_isTarget_2908_);
                    v_a_2994_ = lean_ctor_get(v___x_2925_, 0);
                    v_isSharedCheck_3001_ = (!lean_is_exclusive(v___x_2925_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2996_ = v___x_2925_;
                        v_isShared_2997_ = v_isSharedCheck_3001_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2994_);
                        lean_dec(v___x_2925_);
                        v___x_2996_ = lean_box(0);
                        v_isShared_2997_ = v_isSharedCheck_3001_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_2932_ = lean_ctor_get(v_snd_2926_, 0);
                v_snd_2933_ = lean_ctor_get(v_snd_2926_, 1);
                v_isSharedCheck_2991_ = (!lean_is_exclusive(v_snd_2926_)) as u8;
                if v_isSharedCheck_2991_ == 0 {
                    v___x_2935_ = v_snd_2926_;
                    v_isShared_2936_ = v_isSharedCheck_2991_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_2933_);
                    lean_inc(v_fst_2932_);
                    lean_dec(v_snd_2926_);
                    v___x_2935_ = lean_box(0);
                    v_isShared_2936_ = v_isSharedCheck_2991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2937_ = lean_box(0);
                v___x_2946_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2927_);
                if v___x_2946_ == 0 {
                    lean_dec(v_a_2927_);
                    if v_isShared_2931_ == 0 {
                        lean_ctor_set(v___x_2930_, 1, v_snd_2933_);
                        lean_ctor_set(v___x_2930_, 0, v_fst_2932_);
                        v___x_2948_ = v___x_2930_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_fst_2932_);
                        lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_snd_2933_);
                        v___x_2948_ = v_reuseFailAlloc_2952_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_isTarget_2908_);
                    lean_inc(v___y_2916_);
                    lean_inc_ref(v___y_2915_);
                    lean_inc(v___y_2914_);
                    lean_inc_ref(v___y_2913_);
                    lean_inc(v_a_2927_);
                    v___x_2953_ = lean_apply_6(
                        v_isTarget_2908_,
                        v_a_2927_,
                        v___y_2913_,
                        v___y_2914_,
                        v___y_2915_,
                        v___y_2916_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2953_) == 0 {
                        v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
                        lean_inc(v_a_2954_);
                        lean_dec_ref_known(v___x_2953_, 1);
                        v___x_2955_ = (lean_unbox(v_a_2954_) as u8);
                        lean_dec(v_a_2954_);
                        if v___x_2955_ == 0 {
                            lean_dec(v_a_2927_);
                            if v_isShared_2931_ == 0 {
                                lean_ctor_set(v___x_2930_, 1, v_snd_2933_);
                                lean_ctor_set(v___x_2930_, 0, v_fst_2932_);
                                v___x_2957_ = v___x_2930_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_fst_2932_);
                                lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_snd_2933_);
                                v___x_2957_ = v_reuseFailAlloc_2961_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_self_2962_ = lean_ctor_get(v_a_2927_, 0);
                            lean_inc_ref(v_self_2962_);
                            lean_dec(v_a_2927_);
                            v___x_2963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_2933_, v_self_2962_);
                            if lean_obj_tag(v___x_2963_) == 0 {
                                v___x_2964_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_2907_, v_snd_2933_, v_self_2962_, v_fst_2932_, v_fst_2928_);
                                lean_inc_n(v___x_2964_, 2);
                                v___x_2965_ = l_Rat_ofInt(v___x_2964_);
                                v___x_2966_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_2907_,
                                    v_self_2962_,
                                    v___x_2965_,
                                    v_snd_2933_,
                                );
                                v___x_2967_ = lean_box(0);
                                v___x_2968_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_2932_, v___x_2964_, v___x_2967_);
                                v___x_2969_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                                v___x_2970_ = lean_int_add(v___x_2964_, v___x_2969_);
                                lean_dec(v___x_2964_);
                                if v_isShared_2931_ == 0 {
                                    lean_ctor_set(v___x_2930_, 1, v___x_2966_);
                                    lean_ctor_set(v___x_2930_, 0, v___x_2968_);
                                    v___x_2972_ = v___x_2930_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2968_);
                                    lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___x_2966_);
                                    v___x_2972_ = v_reuseFailAlloc_2976_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v___x_2963_, 1);
                                lean_dec_ref(v_self_2962_);
                                if v_isShared_2931_ == 0 {
                                    lean_ctor_set(v___x_2930_, 1, v_snd_2933_);
                                    lean_ctor_set(v___x_2930_, 0, v_fst_2932_);
                                    v___x_2978_ = v___x_2930_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_fst_2932_);
                                    lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_snd_2933_);
                                    v___x_2978_ = v_reuseFailAlloc_2982_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_2935_);
                        lean_dec(v_snd_2933_);
                        lean_dec(v_fst_2932_);
                        lean_del_object(v___x_2930_);
                        lean_dec(v_fst_2928_);
                        lean_dec(v_a_2927_);
                        lean_del_object(v___x_2922_);
                        lean_dec_ref(v_isTarget_2908_);
                        v_a_2983_ = lean_ctor_get(v___x_2953_, 0);
                        v_isSharedCheck_2990_ = (!lean_is_exclusive(v___x_2953_)) as u8;
                        if v_isSharedCheck_2990_ == 0 {
                            v___x_2985_ = v___x_2953_;
                            v_isShared_2986_ = v_isSharedCheck_2990_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2983_);
                            lean_dec(v___x_2953_);
                            v___x_2985_ = lean_box(0);
                            v_isShared_2986_ = v_isSharedCheck_2990_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_2936_ == 0 {
                    lean_ctor_set(v___x_2935_, 1, v_a_2939_);
                    lean_ctor_set(v___x_2935_, 0, v___x_2937_);
                    v___x_2941_ = v___x_2935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2937_);
                    lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_a_2939_);
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
                    lean_ctor_set(v___x_2922_, 1, v___x_2948_);
                    lean_ctor_set(v___x_2922_, 0, v_fst_2928_);
                    v___x_2950_ = v___x_2922_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_fst_2928_);
                    lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2948_);
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
                    lean_ctor_set(v___x_2922_, 1, v___x_2957_);
                    lean_ctor_set(v___x_2922_, 0, v_fst_2928_);
                    v___x_2959_ = v___x_2922_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_fst_2928_);
                    lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2957_);
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
                    lean_ctor_set(v___x_2922_, 1, v___x_2972_);
                    lean_ctor_set(v___x_2922_, 0, v___x_2970_);
                    v___x_2974_ = v___x_2922_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2970_);
                    lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2972_);
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
                    lean_ctor_set(v___x_2922_, 1, v___x_2978_);
                    lean_ctor_set(v___x_2922_, 0, v_fst_2928_);
                    v___x_2980_ = v___x_2922_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_fst_2928_);
                    lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2978_);
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
                    v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
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
                    v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
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
    mut v_goal_3004_: *mut LeanObject,
    mut v_isTarget_3005_: *mut LeanObject,
    mut v_as_3006_: *mut LeanObject,
    mut v_sz_3007_: *mut LeanObject,
    mut v_i_3008_: *mut LeanObject,
    mut v_b_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
    mut v___y_3014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3015_: usize = 0;
    let mut v_i_boxed_3016_: usize = 0;
    let mut v_res_3017_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3015_ = lean_unbox_usize(v_sz_3007_);
    lean_dec(v_sz_3007_);
    v_i_boxed_3016_ = lean_unbox_usize(v_i_3008_);
    lean_dec(v_i_3008_);
    v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_3004_, v_isTarget_3005_, v_as_3006_, v_sz_boxed_3015_, v_i_boxed_3016_, v_b_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
    lean_dec(v___y_3013_);
    lean_dec_ref(v___y_3012_);
    lean_dec(v___y_3011_);
    lean_dec_ref(v___y_3010_);
    lean_dec_ref(v_as_3006_);
    lean_dec_ref(v_goal_3004_);
    return v_res_3017_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(
    mut v_goal_3018_: *mut LeanObject,
    mut v_isTarget_3019_: *mut LeanObject,
    mut v_as_3020_: *mut LeanObject,
    mut v_sz_3021_: usize,
    mut v_i_3022_: usize,
    mut v_b_3023_: *mut LeanObject,
    mut v___y_3024_: *mut LeanObject,
    mut v___y_3025_: *mut LeanObject,
    mut v___y_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3029_: u8 = 0;
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v_a_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3042_: u8 = 0;
    let mut v_fst_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: usize = 0;
    let mut v___x_3054_: usize = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut v_isSharedCheck_3103_: u8 = 0;
    let mut v_unused_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3108_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_unused_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3029_ = lean_usize_dec_lt(v_i_3022_, v_sz_3021_);
                if v___x_3029_ == 0 {
                    lean_dec_ref(v_isTarget_3019_);
                    v___x_3030_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3030_, 0, v_b_3023_);
                    return v___x_3030_;
                } else {
                    v_snd_3031_ = lean_ctor_get(v_b_3023_, 1);
                    v_isSharedCheck_3113_ = (!lean_is_exclusive(v_b_3023_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v_unused_3114_ = lean_ctor_get(v_b_3023_, 0);
                        lean_dec(v_unused_3114_);
                        v___x_3033_ = v_b_3023_;
                        v_isShared_3034_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3031_);
                        lean_dec(v_b_3023_);
                        v___x_3033_ = lean_box(0);
                        v_isShared_3034_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3035_ = lean_array_uget_borrowed(v_as_3020_, v_i_3022_);
                lean_inc(v_a_3035_);
                v___x_3036_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3018_,
                    v_a_3035_,
                    v___y_3024_,
                    v___y_3025_,
                    v___y_3026_,
                    v___y_3027_,
                );
                if lean_obj_tag(v___x_3036_) == 0 {
                    v_snd_3037_ = lean_ctor_get(v_snd_3031_, 1);
                    lean_inc(v_snd_3037_);
                    v_a_3038_ = lean_ctor_get(v___x_3036_, 0);
                    lean_inc(v_a_3038_);
                    lean_dec_ref_known(v___x_3036_, 1);
                    v_fst_3039_ = lean_ctor_get(v_snd_3031_, 0);
                    v_isSharedCheck_3103_ = (!lean_is_exclusive(v_snd_3031_)) as u8;
                    if v_isSharedCheck_3103_ == 0 {
                        v_unused_3104_ = lean_ctor_get(v_snd_3031_, 1);
                        lean_dec(v_unused_3104_);
                        v___x_3041_ = v_snd_3031_;
                        v_isShared_3042_ = v_isSharedCheck_3103_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_3039_);
                        lean_dec(v_snd_3031_);
                        v___x_3041_ = lean_box(0);
                        v_isShared_3042_ = v_isSharedCheck_3103_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3033_);
                    lean_dec(v_snd_3031_);
                    lean_dec_ref(v_isTarget_3019_);
                    v_a_3105_ = lean_ctor_get(v___x_3036_, 0);
                    v_isSharedCheck_3112_ = (!lean_is_exclusive(v___x_3036_)) as u8;
                    if v_isSharedCheck_3112_ == 0 {
                        v___x_3107_ = v___x_3036_;
                        v_isShared_3108_ = v_isSharedCheck_3112_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3105_);
                        lean_dec(v___x_3036_);
                        v___x_3107_ = lean_box(0);
                        v_isShared_3108_ = v_isSharedCheck_3112_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3043_ = lean_ctor_get(v_snd_3037_, 0);
                v_snd_3044_ = lean_ctor_get(v_snd_3037_, 1);
                v_isSharedCheck_3102_ = (!lean_is_exclusive(v_snd_3037_)) as u8;
                if v_isSharedCheck_3102_ == 0 {
                    v___x_3046_ = v_snd_3037_;
                    v_isShared_3047_ = v_isSharedCheck_3102_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_3044_);
                    lean_inc(v_fst_3043_);
                    lean_dec(v_snd_3037_);
                    v___x_3046_ = lean_box(0);
                    v_isShared_3047_ = v_isSharedCheck_3102_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3048_ = lean_box(0);
                v___x_3057_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3038_);
                if v___x_3057_ == 0 {
                    lean_dec(v_a_3038_);
                    if v_isShared_3042_ == 0 {
                        lean_ctor_set(v___x_3041_, 1, v_snd_3044_);
                        lean_ctor_set(v___x_3041_, 0, v_fst_3043_);
                        v___x_3059_ = v___x_3041_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_fst_3043_);
                        lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_snd_3044_);
                        v___x_3059_ = v_reuseFailAlloc_3063_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_isTarget_3019_);
                    lean_inc(v___y_3027_);
                    lean_inc_ref(v___y_3026_);
                    lean_inc(v___y_3025_);
                    lean_inc_ref(v___y_3024_);
                    lean_inc(v_a_3038_);
                    v___x_3064_ = lean_apply_6(
                        v_isTarget_3019_,
                        v_a_3038_,
                        v___y_3024_,
                        v___y_3025_,
                        v___y_3026_,
                        v___y_3027_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3064_) == 0 {
                        v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
                        lean_inc(v_a_3065_);
                        lean_dec_ref_known(v___x_3064_, 1);
                        v___x_3066_ = (lean_unbox(v_a_3065_) as u8);
                        lean_dec(v_a_3065_);
                        if v___x_3066_ == 0 {
                            lean_dec(v_a_3038_);
                            if v_isShared_3042_ == 0 {
                                lean_ctor_set(v___x_3041_, 1, v_snd_3044_);
                                lean_ctor_set(v___x_3041_, 0, v_fst_3043_);
                                v___x_3068_ = v___x_3041_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_fst_3043_);
                                lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_snd_3044_);
                                v___x_3068_ = v_reuseFailAlloc_3072_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_self_3073_ = lean_ctor_get(v_a_3038_, 0);
                            lean_inc_ref(v_self_3073_);
                            lean_dec(v_a_3038_);
                            v___x_3074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_3044_, v_self_3073_);
                            if lean_obj_tag(v___x_3074_) == 0 {
                                v___x_3075_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_3018_, v_snd_3044_, v_self_3073_, v_fst_3043_, v_fst_3039_);
                                lean_inc_n(v___x_3075_, 2);
                                v___x_3076_ = l_Rat_ofInt(v___x_3075_);
                                v___x_3077_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3018_,
                                    v_self_3073_,
                                    v___x_3076_,
                                    v_snd_3044_,
                                );
                                v___x_3078_ = lean_box(0);
                                v___x_3079_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_3043_, v___x_3075_, v___x_3078_);
                                v___x_3080_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                                v___x_3081_ = lean_int_add(v___x_3075_, v___x_3080_);
                                lean_dec(v___x_3075_);
                                if v_isShared_3042_ == 0 {
                                    lean_ctor_set(v___x_3041_, 1, v___x_3077_);
                                    lean_ctor_set(v___x_3041_, 0, v___x_3079_);
                                    v___x_3083_ = v___x_3041_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3079_);
                                    lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3077_);
                                    v___x_3083_ = v_reuseFailAlloc_3087_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v___x_3074_, 1);
                                lean_dec_ref(v_self_3073_);
                                if v_isShared_3042_ == 0 {
                                    lean_ctor_set(v___x_3041_, 1, v_snd_3044_);
                                    lean_ctor_set(v___x_3041_, 0, v_fst_3043_);
                                    v___x_3089_ = v___x_3041_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_fst_3043_);
                                    lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_snd_3044_);
                                    v___x_3089_ = v_reuseFailAlloc_3093_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_3046_);
                        lean_dec(v_snd_3044_);
                        lean_dec(v_fst_3043_);
                        lean_del_object(v___x_3041_);
                        lean_dec(v_fst_3039_);
                        lean_dec(v_a_3038_);
                        lean_del_object(v___x_3033_);
                        lean_dec_ref(v_isTarget_3019_);
                        v_a_3094_ = lean_ctor_get(v___x_3064_, 0);
                        v_isSharedCheck_3101_ = (!lean_is_exclusive(v___x_3064_)) as u8;
                        if v_isSharedCheck_3101_ == 0 {
                            v___x_3096_ = v___x_3064_;
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_3094_);
                            lean_dec(v___x_3064_);
                            v___x_3096_ = lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3047_ == 0 {
                    lean_ctor_set(v___x_3046_, 1, v_a_3050_);
                    lean_ctor_set(v___x_3046_, 0, v___x_3048_);
                    v___x_3052_ = v___x_3046_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3048_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_a_3050_);
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
                    lean_ctor_set(v___x_3033_, 1, v___x_3059_);
                    lean_ctor_set(v___x_3033_, 0, v_fst_3039_);
                    v___x_3061_ = v___x_3033_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_fst_3039_);
                    lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3059_);
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
                    lean_ctor_set(v___x_3033_, 1, v___x_3068_);
                    lean_ctor_set(v___x_3033_, 0, v_fst_3039_);
                    v___x_3070_ = v___x_3033_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_fst_3039_);
                    lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_3068_);
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
                    lean_ctor_set(v___x_3033_, 1, v___x_3083_);
                    lean_ctor_set(v___x_3033_, 0, v___x_3081_);
                    v___x_3085_ = v___x_3033_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3081_);
                    lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3083_);
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
                    lean_ctor_set(v___x_3033_, 1, v___x_3089_);
                    lean_ctor_set(v___x_3033_, 0, v_fst_3039_);
                    v___x_3091_ = v___x_3033_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_fst_3039_);
                    lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3089_);
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
                    v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
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
                    v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
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
    mut v_goal_3115_: *mut LeanObject,
    mut v_isTarget_3116_: *mut LeanObject,
    mut v_as_3117_: *mut LeanObject,
    mut v_sz_3118_: *mut LeanObject,
    mut v_i_3119_: *mut LeanObject,
    mut v_b_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3126_: usize = 0;
    let mut v_i_boxed_3127_: usize = 0;
    let mut v_res_3128_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3126_ = lean_unbox_usize(v_sz_3118_);
    lean_dec(v_sz_3118_);
    v_i_boxed_3127_ = lean_unbox_usize(v_i_3119_);
    lean_dec(v_i_3119_);
    v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_3115_, v_isTarget_3116_, v_as_3117_, v_sz_boxed_3126_, v_i_boxed_3127_, v_b_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
    lean_dec(v___y_3124_);
    lean_dec_ref(v___y_3123_);
    lean_dec(v___y_3122_);
    lean_dec_ref(v___y_3121_);
    lean_dec_ref(v_as_3117_);
    lean_dec_ref(v_goal_3115_);
    return v_res_3128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(
    mut v_goal_3129_: *mut LeanObject,
    mut v_isTarget_3130_: *mut LeanObject,
    mut v_as_3131_: *mut LeanObject,
    mut v_sz_3132_: usize,
    mut v_i_3133_: usize,
    mut v_b_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3145_: u8 = 0;
    let mut v_a_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3153_: u8 = 0;
    let mut v_fst_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3158_: u8 = 0;
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: usize = 0;
    let mut v___x_3165_: usize = 0;
    let mut v_reuseFailAlloc_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut v_unused_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v_isSharedCheck_3224_: u8 = 0;
    let mut v_unused_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3140_ = lean_usize_dec_lt(v_i_3133_, v_sz_3132_);
                if v___x_3140_ == 0 {
                    lean_dec_ref(v_isTarget_3130_);
                    v___x_3141_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3141_, 0, v_b_3134_);
                    return v___x_3141_;
                } else {
                    v_snd_3142_ = lean_ctor_get(v_b_3134_, 1);
                    v_isSharedCheck_3224_ = (!lean_is_exclusive(v_b_3134_)) as u8;
                    if v_isSharedCheck_3224_ == 0 {
                        v_unused_3225_ = lean_ctor_get(v_b_3134_, 0);
                        lean_dec(v_unused_3225_);
                        v___x_3144_ = v_b_3134_;
                        v_isShared_3145_ = v_isSharedCheck_3224_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3142_);
                        lean_dec(v_b_3134_);
                        v___x_3144_ = lean_box(0);
                        v_isShared_3145_ = v_isSharedCheck_3224_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3146_ = lean_array_uget_borrowed(v_as_3131_, v_i_3133_);
                lean_inc(v_a_3146_);
                v___x_3147_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3129_,
                    v_a_3146_,
                    v___y_3135_,
                    v___y_3136_,
                    v___y_3137_,
                    v___y_3138_,
                );
                if lean_obj_tag(v___x_3147_) == 0 {
                    v_snd_3148_ = lean_ctor_get(v_snd_3142_, 1);
                    lean_inc(v_snd_3148_);
                    v_a_3149_ = lean_ctor_get(v___x_3147_, 0);
                    lean_inc(v_a_3149_);
                    lean_dec_ref_known(v___x_3147_, 1);
                    v_fst_3150_ = lean_ctor_get(v_snd_3142_, 0);
                    v_isSharedCheck_3214_ = (!lean_is_exclusive(v_snd_3142_)) as u8;
                    if v_isSharedCheck_3214_ == 0 {
                        v_unused_3215_ = lean_ctor_get(v_snd_3142_, 1);
                        lean_dec(v_unused_3215_);
                        v___x_3152_ = v_snd_3142_;
                        v_isShared_3153_ = v_isSharedCheck_3214_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_3150_);
                        lean_dec(v_snd_3142_);
                        v___x_3152_ = lean_box(0);
                        v_isShared_3153_ = v_isSharedCheck_3214_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3144_);
                    lean_dec(v_snd_3142_);
                    lean_dec_ref(v_isTarget_3130_);
                    v_a_3216_ = lean_ctor_get(v___x_3147_, 0);
                    v_isSharedCheck_3223_ = (!lean_is_exclusive(v___x_3147_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3218_ = v___x_3147_;
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3216_);
                        lean_dec(v___x_3147_);
                        v___x_3218_ = lean_box(0);
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3154_ = lean_ctor_get(v_snd_3148_, 0);
                v_snd_3155_ = lean_ctor_get(v_snd_3148_, 1);
                v_isSharedCheck_3213_ = (!lean_is_exclusive(v_snd_3148_)) as u8;
                if v_isSharedCheck_3213_ == 0 {
                    v___x_3157_ = v_snd_3148_;
                    v_isShared_3158_ = v_isSharedCheck_3213_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_3155_);
                    lean_inc(v_fst_3154_);
                    lean_dec(v_snd_3148_);
                    v___x_3157_ = lean_box(0);
                    v_isShared_3158_ = v_isSharedCheck_3213_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3159_ = lean_box(0);
                v___x_3168_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3149_);
                if v___x_3168_ == 0 {
                    lean_dec(v_a_3149_);
                    if v_isShared_3153_ == 0 {
                        lean_ctor_set(v___x_3152_, 1, v_snd_3155_);
                        lean_ctor_set(v___x_3152_, 0, v_fst_3154_);
                        v___x_3170_ = v___x_3152_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_fst_3154_);
                        lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_snd_3155_);
                        v___x_3170_ = v_reuseFailAlloc_3174_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_isTarget_3130_);
                    lean_inc(v___y_3138_);
                    lean_inc_ref(v___y_3137_);
                    lean_inc(v___y_3136_);
                    lean_inc_ref(v___y_3135_);
                    lean_inc(v_a_3149_);
                    v___x_3175_ = lean_apply_6(
                        v_isTarget_3130_,
                        v_a_3149_,
                        v___y_3135_,
                        v___y_3136_,
                        v___y_3137_,
                        v___y_3138_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3175_) == 0 {
                        v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
                        lean_inc(v_a_3176_);
                        lean_dec_ref_known(v___x_3175_, 1);
                        v___x_3177_ = (lean_unbox(v_a_3176_) as u8);
                        lean_dec(v_a_3176_);
                        if v___x_3177_ == 0 {
                            lean_dec(v_a_3149_);
                            if v_isShared_3153_ == 0 {
                                lean_ctor_set(v___x_3152_, 1, v_snd_3155_);
                                lean_ctor_set(v___x_3152_, 0, v_fst_3154_);
                                v___x_3179_ = v___x_3152_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_fst_3154_);
                                lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_snd_3155_);
                                v___x_3179_ = v_reuseFailAlloc_3183_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_self_3184_ = lean_ctor_get(v_a_3149_, 0);
                            lean_inc_ref(v_self_3184_);
                            lean_dec(v_a_3149_);
                            v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_3155_, v_self_3184_);
                            if lean_obj_tag(v___x_3185_) == 0 {
                                v___x_3186_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_3129_, v_snd_3155_, v_self_3184_, v_fst_3154_, v_fst_3150_);
                                lean_inc_n(v___x_3186_, 2);
                                v___x_3187_ = l_Rat_ofInt(v___x_3186_);
                                v___x_3188_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3129_,
                                    v_self_3184_,
                                    v___x_3187_,
                                    v_snd_3155_,
                                );
                                v___x_3189_ = lean_box(0);
                                v___x_3190_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_3154_, v___x_3186_, v___x_3189_);
                                v___x_3191_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                                v___x_3192_ = lean_int_add(v___x_3186_, v___x_3191_);
                                lean_dec(v___x_3186_);
                                if v_isShared_3153_ == 0 {
                                    lean_ctor_set(v___x_3152_, 1, v___x_3188_);
                                    lean_ctor_set(v___x_3152_, 0, v___x_3190_);
                                    v___x_3194_ = v___x_3152_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3190_);
                                    lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___x_3188_);
                                    v___x_3194_ = v_reuseFailAlloc_3198_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v___x_3185_, 1);
                                lean_dec_ref(v_self_3184_);
                                if v_isShared_3153_ == 0 {
                                    lean_ctor_set(v___x_3152_, 1, v_snd_3155_);
                                    lean_ctor_set(v___x_3152_, 0, v_fst_3154_);
                                    v___x_3200_ = v___x_3152_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_fst_3154_);
                                    lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_snd_3155_);
                                    v___x_3200_ = v_reuseFailAlloc_3204_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_3157_);
                        lean_dec(v_snd_3155_);
                        lean_dec(v_fst_3154_);
                        lean_del_object(v___x_3152_);
                        lean_dec(v_fst_3150_);
                        lean_dec(v_a_3149_);
                        lean_del_object(v___x_3144_);
                        lean_dec_ref(v_isTarget_3130_);
                        v_a_3205_ = lean_ctor_get(v___x_3175_, 0);
                        v_isSharedCheck_3212_ = (!lean_is_exclusive(v___x_3175_)) as u8;
                        if v_isSharedCheck_3212_ == 0 {
                            v___x_3207_ = v___x_3175_;
                            v_isShared_3208_ = v_isSharedCheck_3212_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_3205_);
                            lean_dec(v___x_3175_);
                            v___x_3207_ = lean_box(0);
                            v_isShared_3208_ = v_isSharedCheck_3212_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3158_ == 0 {
                    lean_ctor_set(v___x_3157_, 1, v_a_3161_);
                    lean_ctor_set(v___x_3157_, 0, v___x_3159_);
                    v___x_3163_ = v___x_3157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3159_);
                    lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_a_3161_);
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
                    lean_ctor_set(v___x_3144_, 1, v___x_3170_);
                    lean_ctor_set(v___x_3144_, 0, v_fst_3150_);
                    v___x_3172_ = v___x_3144_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_fst_3150_);
                    lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___x_3170_);
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
                    lean_ctor_set(v___x_3144_, 1, v___x_3179_);
                    lean_ctor_set(v___x_3144_, 0, v_fst_3150_);
                    v___x_3181_ = v___x_3144_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_fst_3150_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3179_);
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
                    lean_ctor_set(v___x_3144_, 1, v___x_3194_);
                    lean_ctor_set(v___x_3144_, 0, v___x_3192_);
                    v___x_3196_ = v___x_3144_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3192_);
                    lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3194_);
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
                    lean_ctor_set(v___x_3144_, 1, v___x_3200_);
                    lean_ctor_set(v___x_3144_, 0, v_fst_3150_);
                    v___x_3202_ = v___x_3144_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_fst_3150_);
                    lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___x_3200_);
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
                    v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
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
                    v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
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
    mut v_goal_3226_: *mut LeanObject,
    mut v_isTarget_3227_: *mut LeanObject,
    mut v_as_3228_: *mut LeanObject,
    mut v_sz_3229_: *mut LeanObject,
    mut v_i_3230_: *mut LeanObject,
    mut v_b_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3237_: usize = 0;
    let mut v_i_boxed_3238_: usize = 0;
    let mut v_res_3239_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3237_ = lean_unbox_usize(v_sz_3229_);
    lean_dec(v_sz_3229_);
    v_i_boxed_3238_ = lean_unbox_usize(v_i_3230_);
    lean_dec(v_i_3230_);
    v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_3226_, v_isTarget_3227_, v_as_3228_, v_sz_boxed_3237_, v_i_boxed_3238_, v_b_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
    lean_dec(v___y_3235_);
    lean_dec_ref(v___y_3234_);
    lean_dec(v___y_3233_);
    lean_dec_ref(v___y_3232_);
    lean_dec_ref(v_as_3228_);
    lean_dec_ref(v_goal_3226_);
    return v_res_3239_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(
    mut v_goal_3240_: *mut LeanObject,
    mut v_isTarget_3241_: *mut LeanObject,
    mut v_as_3242_: *mut LeanObject,
    mut v_sz_3243_: usize,
    mut v_i_3244_: usize,
    mut v_b_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v_a_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v_fst_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3319_: u8 = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3323_: u8 = 0;
    let mut v_isSharedCheck_3324_: u8 = 0;
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_unused_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3330_: u8 = 0;
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3334_: u8 = 0;
    let mut v_isSharedCheck_3335_: u8 = 0;
    let mut v_unused_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3251_ = lean_usize_dec_lt(v_i_3244_, v_sz_3243_);
                if v___x_3251_ == 0 {
                    lean_dec_ref(v_isTarget_3241_);
                    v___x_3252_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3252_, 0, v_b_3245_);
                    return v___x_3252_;
                } else {
                    v_snd_3253_ = lean_ctor_get(v_b_3245_, 1);
                    v_isSharedCheck_3335_ = (!lean_is_exclusive(v_b_3245_)) as u8;
                    if v_isSharedCheck_3335_ == 0 {
                        v_unused_3336_ = lean_ctor_get(v_b_3245_, 0);
                        lean_dec(v_unused_3336_);
                        v___x_3255_ = v_b_3245_;
                        v_isShared_3256_ = v_isSharedCheck_3335_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3253_);
                        lean_dec(v_b_3245_);
                        v___x_3255_ = lean_box(0);
                        v_isShared_3256_ = v_isSharedCheck_3335_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3257_ = lean_array_uget_borrowed(v_as_3242_, v_i_3244_);
                lean_inc(v_a_3257_);
                v___x_3258_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3240_,
                    v_a_3257_,
                    v___y_3246_,
                    v___y_3247_,
                    v___y_3248_,
                    v___y_3249_,
                );
                if lean_obj_tag(v___x_3258_) == 0 {
                    v_snd_3259_ = lean_ctor_get(v_snd_3253_, 1);
                    lean_inc(v_snd_3259_);
                    v_a_3260_ = lean_ctor_get(v___x_3258_, 0);
                    lean_inc(v_a_3260_);
                    lean_dec_ref_known(v___x_3258_, 1);
                    v_fst_3261_ = lean_ctor_get(v_snd_3253_, 0);
                    v_isSharedCheck_3325_ = (!lean_is_exclusive(v_snd_3253_)) as u8;
                    if v_isSharedCheck_3325_ == 0 {
                        v_unused_3326_ = lean_ctor_get(v_snd_3253_, 1);
                        lean_dec(v_unused_3326_);
                        v___x_3263_ = v_snd_3253_;
                        v_isShared_3264_ = v_isSharedCheck_3325_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_3261_);
                        lean_dec(v_snd_3253_);
                        v___x_3263_ = lean_box(0);
                        v_isShared_3264_ = v_isSharedCheck_3325_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3255_);
                    lean_dec(v_snd_3253_);
                    lean_dec_ref(v_isTarget_3241_);
                    v_a_3327_ = lean_ctor_get(v___x_3258_, 0);
                    v_isSharedCheck_3334_ = (!lean_is_exclusive(v___x_3258_)) as u8;
                    if v_isSharedCheck_3334_ == 0 {
                        v___x_3329_ = v___x_3258_;
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3327_);
                        lean_dec(v___x_3258_);
                        v___x_3329_ = lean_box(0);
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3265_ = lean_ctor_get(v_snd_3259_, 0);
                v_snd_3266_ = lean_ctor_get(v_snd_3259_, 1);
                v_isSharedCheck_3324_ = (!lean_is_exclusive(v_snd_3259_)) as u8;
                if v_isSharedCheck_3324_ == 0 {
                    v___x_3268_ = v_snd_3259_;
                    v_isShared_3269_ = v_isSharedCheck_3324_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_3266_);
                    lean_inc(v_fst_3265_);
                    lean_dec(v_snd_3259_);
                    v___x_3268_ = lean_box(0);
                    v_isShared_3269_ = v_isSharedCheck_3324_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3270_ = lean_box(0);
                v___x_3279_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3260_);
                if v___x_3279_ == 0 {
                    lean_dec(v_a_3260_);
                    if v_isShared_3264_ == 0 {
                        lean_ctor_set(v___x_3263_, 1, v_snd_3266_);
                        lean_ctor_set(v___x_3263_, 0, v_fst_3265_);
                        v___x_3281_ = v___x_3263_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_fst_3265_);
                        lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_snd_3266_);
                        v___x_3281_ = v_reuseFailAlloc_3285_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_isTarget_3241_);
                    lean_inc(v___y_3249_);
                    lean_inc_ref(v___y_3248_);
                    lean_inc(v___y_3247_);
                    lean_inc_ref(v___y_3246_);
                    lean_inc(v_a_3260_);
                    v___x_3286_ = lean_apply_6(
                        v_isTarget_3241_,
                        v_a_3260_,
                        v___y_3246_,
                        v___y_3247_,
                        v___y_3248_,
                        v___y_3249_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3286_) == 0 {
                        v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
                        lean_inc(v_a_3287_);
                        lean_dec_ref_known(v___x_3286_, 1);
                        v___x_3288_ = (lean_unbox(v_a_3287_) as u8);
                        lean_dec(v_a_3287_);
                        if v___x_3288_ == 0 {
                            lean_dec(v_a_3260_);
                            if v_isShared_3264_ == 0 {
                                lean_ctor_set(v___x_3263_, 1, v_snd_3266_);
                                lean_ctor_set(v___x_3263_, 0, v_fst_3265_);
                                v___x_3290_ = v___x_3263_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_fst_3265_);
                                lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_snd_3266_);
                                v___x_3290_ = v_reuseFailAlloc_3294_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_self_3295_ = lean_ctor_get(v_a_3260_, 0);
                            lean_inc_ref(v_self_3295_);
                            lean_dec(v_a_3260_);
                            v___x_3296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_3266_, v_self_3295_);
                            if lean_obj_tag(v___x_3296_) == 0 {
                                v___x_3297_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_3240_, v_snd_3266_, v_self_3295_, v_fst_3265_, v_fst_3261_);
                                lean_inc_n(v___x_3297_, 2);
                                v___x_3298_ = l_Rat_ofInt(v___x_3297_);
                                v___x_3299_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3240_,
                                    v_self_3295_,
                                    v___x_3298_,
                                    v_snd_3266_,
                                );
                                v___x_3300_ = lean_box(0);
                                v___x_3301_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_3265_, v___x_3297_, v___x_3300_);
                                v___x_3302_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
                                v___x_3303_ = lean_int_add(v___x_3297_, v___x_3302_);
                                lean_dec(v___x_3297_);
                                if v_isShared_3264_ == 0 {
                                    lean_ctor_set(v___x_3263_, 1, v___x_3299_);
                                    lean_ctor_set(v___x_3263_, 0, v___x_3301_);
                                    v___x_3305_ = v___x_3263_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3301_);
                                    lean_ctor_set(v_reuseFailAlloc_3309_, 1, v___x_3299_);
                                    v___x_3305_ = v_reuseFailAlloc_3309_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v___x_3296_, 1);
                                lean_dec_ref(v_self_3295_);
                                if v_isShared_3264_ == 0 {
                                    lean_ctor_set(v___x_3263_, 1, v_snd_3266_);
                                    lean_ctor_set(v___x_3263_, 0, v_fst_3265_);
                                    v___x_3311_ = v___x_3263_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_fst_3265_);
                                    lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_snd_3266_);
                                    v___x_3311_ = v_reuseFailAlloc_3315_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_3268_);
                        lean_dec(v_snd_3266_);
                        lean_dec(v_fst_3265_);
                        lean_del_object(v___x_3263_);
                        lean_dec(v_fst_3261_);
                        lean_dec(v_a_3260_);
                        lean_del_object(v___x_3255_);
                        lean_dec_ref(v_isTarget_3241_);
                        v_a_3316_ = lean_ctor_get(v___x_3286_, 0);
                        v_isSharedCheck_3323_ = (!lean_is_exclusive(v___x_3286_)) as u8;
                        if v_isSharedCheck_3323_ == 0 {
                            v___x_3318_ = v___x_3286_;
                            v_isShared_3319_ = v_isSharedCheck_3323_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_3316_);
                            lean_dec(v___x_3286_);
                            v___x_3318_ = lean_box(0);
                            v_isShared_3319_ = v_isSharedCheck_3323_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3269_ == 0 {
                    lean_ctor_set(v___x_3268_, 1, v_a_3272_);
                    lean_ctor_set(v___x_3268_, 0, v___x_3270_);
                    v___x_3274_ = v___x_3268_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3270_);
                    lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_a_3272_);
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
                    lean_ctor_set(v___x_3255_, 1, v___x_3281_);
                    lean_ctor_set(v___x_3255_, 0, v_fst_3261_);
                    v___x_3283_ = v___x_3255_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_fst_3261_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 1, v___x_3281_);
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
                    lean_ctor_set(v___x_3255_, 1, v___x_3290_);
                    lean_ctor_set(v___x_3255_, 0, v_fst_3261_);
                    v___x_3292_ = v___x_3255_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_fst_3261_);
                    lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3290_);
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
                    lean_ctor_set(v___x_3255_, 1, v___x_3305_);
                    lean_ctor_set(v___x_3255_, 0, v___x_3303_);
                    v___x_3307_ = v___x_3255_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3303_);
                    lean_ctor_set(v_reuseFailAlloc_3308_, 1, v___x_3305_);
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
                    lean_ctor_set(v___x_3255_, 1, v___x_3311_);
                    lean_ctor_set(v___x_3255_, 0, v_fst_3261_);
                    v___x_3313_ = v___x_3255_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_fst_3261_);
                    lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3311_);
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
                    v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
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
                    v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
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
    mut v_goal_3337_: *mut LeanObject,
    mut v_isTarget_3338_: *mut LeanObject,
    mut v_as_3339_: *mut LeanObject,
    mut v_sz_3340_: *mut LeanObject,
    mut v_i_3341_: *mut LeanObject,
    mut v_b_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3348_: usize = 0;
    let mut v_i_boxed_3349_: usize = 0;
    let mut v_res_3350_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3348_ = lean_unbox_usize(v_sz_3340_);
    lean_dec(v_sz_3340_);
    v_i_boxed_3349_ = lean_unbox_usize(v_i_3341_);
    lean_dec(v_i_3341_);
    v_res_3350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_3337_, v_isTarget_3338_, v_as_3339_, v_sz_boxed_3348_, v_i_boxed_3349_, v_b_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
    lean_dec(v___y_3346_);
    lean_dec_ref(v___y_3345_);
    lean_dec(v___y_3344_);
    lean_dec_ref(v___y_3343_);
    lean_dec_ref(v_as_3339_);
    lean_dec_ref(v_goal_3337_);
    return v_res_3350_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(
    mut v_init_3351_: *mut LeanObject,
    mut v_goal_3352_: *mut LeanObject,
    mut v_isTarget_3353_: *mut LeanObject,
    mut v_n_3354_: *mut LeanObject,
    mut v_b_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
    mut v___y_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3364_: usize = 0;
    let mut v___x_3365_: usize = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v_fst_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_a_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut v_vs_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3393_: usize = 0;
    let mut v___x_3394_: usize = 0;
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v_fst_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3410_: u8 = 0;
    let mut v_a_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_3354_) == 0 {
                    v_cs_3361_ = lean_ctor_get(v_n_3354_, 0);
                    v___x_3362_ = lean_box(0);
                    v___x_3363_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3363_, 0, v___x_3362_);
                    lean_ctor_set(v___x_3363_, 1, v_b_3355_);
                    v_sz_3364_ = lean_array_size(v_cs_3361_);
                    v___x_3365_ = 0usize;
                    v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_3351_, v_goal_3352_, v_isTarget_3353_, v_cs_3361_, v_sz_3364_, v___x_3365_, v___x_3363_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
                    if lean_obj_tag(v___x_3366_) == 0 {
                        v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
                        v_isSharedCheck_3381_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                        if v_isSharedCheck_3381_ == 0 {
                            v___x_3369_ = v___x_3366_;
                            v_isShared_3370_ = v_isSharedCheck_3381_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3367_);
                            lean_dec(v___x_3366_);
                            v___x_3369_ = lean_box(0);
                            v_isShared_3370_ = v_isSharedCheck_3381_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3382_ = lean_ctor_get(v___x_3366_, 0);
                        v_isSharedCheck_3389_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                        if v_isSharedCheck_3389_ == 0 {
                            v___x_3384_ = v___x_3366_;
                            v_isShared_3385_ = v_isSharedCheck_3389_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3382_);
                            lean_dec(v___x_3366_);
                            v___x_3384_ = lean_box(0);
                            v_isShared_3385_ = v_isSharedCheck_3389_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3390_ = lean_ctor_get(v_n_3354_, 0);
                    v___x_3391_ = lean_box(0);
                    v___x_3392_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3392_, 0, v___x_3391_);
                    lean_ctor_set(v___x_3392_, 1, v_b_3355_);
                    v_sz_3393_ = lean_array_size(v_vs_3390_);
                    v___x_3394_ = 0usize;
                    v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_3352_, v_isTarget_3353_, v_vs_3390_, v_sz_3393_, v___x_3394_, v___x_3392_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
                    if lean_obj_tag(v___x_3395_) == 0 {
                        v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
                        v_isSharedCheck_3410_ = (!lean_is_exclusive(v___x_3395_)) as u8;
                        if v_isSharedCheck_3410_ == 0 {
                            v___x_3398_ = v___x_3395_;
                            v_isShared_3399_ = v_isSharedCheck_3410_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3396_);
                            lean_dec(v___x_3395_);
                            v___x_3398_ = lean_box(0);
                            v_isShared_3399_ = v_isSharedCheck_3410_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3411_ = lean_ctor_get(v___x_3395_, 0);
                        v_isSharedCheck_3418_ = (!lean_is_exclusive(v___x_3395_)) as u8;
                        if v_isSharedCheck_3418_ == 0 {
                            v___x_3413_ = v___x_3395_;
                            v_isShared_3414_ = v_isSharedCheck_3418_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3411_);
                            lean_dec(v___x_3395_);
                            v___x_3413_ = lean_box(0);
                            v_isShared_3414_ = v_isSharedCheck_3418_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3371_ = lean_ctor_get(v_a_3367_, 0);
                if lean_obj_tag(v_fst_3371_) == 0 {
                    v_snd_3372_ = lean_ctor_get(v_a_3367_, 1);
                    lean_inc(v_snd_3372_);
                    lean_dec(v_a_3367_);
                    v___x_3373_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3373_, 0, v_snd_3372_);
                    if v_isShared_3370_ == 0 {
                        lean_ctor_set(v___x_3369_, 0, v___x_3373_);
                        v___x_3375_ = v___x_3369_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
                        v___x_3375_ = v_reuseFailAlloc_3376_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3371_);
                    lean_dec(v_a_3367_);
                    v_val_3377_ = lean_ctor_get(v_fst_3371_, 0);
                    lean_inc(v_val_3377_);
                    lean_dec_ref_known(v_fst_3371_, 1);
                    if v_isShared_3370_ == 0 {
                        lean_ctor_set(v___x_3369_, 0, v_val_3377_);
                        v___x_3379_ = v___x_3369_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_val_3377_);
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
                    v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
                    v___x_3387_ = v_reuseFailAlloc_3388_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3387_;
            }
            6 => {
                v_fst_3400_ = lean_ctor_get(v_a_3396_, 0);
                if lean_obj_tag(v_fst_3400_) == 0 {
                    v_snd_3401_ = lean_ctor_get(v_a_3396_, 1);
                    lean_inc(v_snd_3401_);
                    lean_dec(v_a_3396_);
                    v___x_3402_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3402_, 0, v_snd_3401_);
                    if v_isShared_3399_ == 0 {
                        lean_ctor_set(v___x_3398_, 0, v___x_3402_);
                        v___x_3404_ = v___x_3398_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
                        v___x_3404_ = v_reuseFailAlloc_3405_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3400_);
                    lean_dec(v_a_3396_);
                    v_val_3406_ = lean_ctor_get(v_fst_3400_, 0);
                    lean_inc(v_val_3406_);
                    lean_dec_ref_known(v_fst_3400_, 1);
                    if v_isShared_3399_ == 0 {
                        lean_ctor_set(v___x_3398_, 0, v_val_3406_);
                        v___x_3408_ = v___x_3398_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_val_3406_);
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
                    v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
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
    mut v_init_3419_: *mut LeanObject,
    mut v_goal_3420_: *mut LeanObject,
    mut v_isTarget_3421_: *mut LeanObject,
    mut v_as_3422_: *mut LeanObject,
    mut v_sz_3423_: usize,
    mut v_i_3424_: usize,
    mut v_b_3425_: *mut LeanObject,
    mut v___y_3426_: *mut LeanObject,
    mut v___y_3427_: *mut LeanObject,
    mut v___y_3428_: *mut LeanObject,
    mut v___y_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v_a_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: usize = 0;
    let mut v___x_3455_: usize = 0;
    let mut v_reuseFailAlloc_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3458_: u8 = 0;
    let mut v_a_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3466_: u8 = 0;
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v_unused_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3431_ = lean_usize_dec_lt(v_i_3424_, v_sz_3423_);
                if v___x_3431_ == 0 {
                    lean_dec_ref(v_isTarget_3421_);
                    v___x_3432_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3432_, 0, v_b_3425_);
                    return v___x_3432_;
                } else {
                    v_snd_3433_ = lean_ctor_get(v_b_3425_, 1);
                    v_isSharedCheck_3467_ = (!lean_is_exclusive(v_b_3425_)) as u8;
                    if v_isSharedCheck_3467_ == 0 {
                        v_unused_3468_ = lean_ctor_get(v_b_3425_, 0);
                        lean_dec(v_unused_3468_);
                        v___x_3435_ = v_b_3425_;
                        v_isShared_3436_ = v_isSharedCheck_3467_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3433_);
                        lean_dec(v_b_3425_);
                        v___x_3435_ = lean_box(0);
                        v_isShared_3436_ = v_isSharedCheck_3467_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3437_ = lean_array_uget_borrowed(v_as_3422_, v_i_3424_);
                lean_inc(v_snd_3433_);
                lean_inc_ref(v_isTarget_3421_);
                v___x_3438_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_3419_, v_goal_3420_, v_isTarget_3421_, v_a_3437_, v_snd_3433_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
                if lean_obj_tag(v___x_3438_) == 0 {
                    v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
                    v_isSharedCheck_3458_ = (!lean_is_exclusive(v___x_3438_)) as u8;
                    if v_isSharedCheck_3458_ == 0 {
                        v___x_3441_ = v___x_3438_;
                        v_isShared_3442_ = v_isSharedCheck_3458_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3439_);
                        lean_dec(v___x_3438_);
                        v___x_3441_ = lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3458_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3435_);
                    lean_dec(v_snd_3433_);
                    lean_dec_ref(v_isTarget_3421_);
                    v_a_3459_ = lean_ctor_get(v___x_3438_, 0);
                    v_isSharedCheck_3466_ = (!lean_is_exclusive(v___x_3438_)) as u8;
                    if v_isSharedCheck_3466_ == 0 {
                        v___x_3461_ = v___x_3438_;
                        v_isShared_3462_ = v_isSharedCheck_3466_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3459_);
                        lean_dec(v___x_3438_);
                        v___x_3461_ = lean_box(0);
                        v_isShared_3462_ = v_isSharedCheck_3466_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3439_) == 0 {
                    lean_dec_ref(v_isTarget_3421_);
                    v___x_3443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3443_, 0, v_a_3439_);
                    if v_isShared_3436_ == 0 {
                        lean_ctor_set(v___x_3435_, 0, v___x_3443_);
                        v___x_3445_ = v___x_3435_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3443_);
                        lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_snd_3433_);
                        v___x_3445_ = v_reuseFailAlloc_3449_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3441_);
                    lean_dec(v_snd_3433_);
                    v_a_3450_ = lean_ctor_get(v_a_3439_, 0);
                    lean_inc(v_a_3450_);
                    lean_dec_ref_known(v_a_3439_, 1);
                    v___x_3451_ = lean_box(0);
                    if v_isShared_3436_ == 0 {
                        lean_ctor_set(v___x_3435_, 1, v_a_3450_);
                        lean_ctor_set(v___x_3435_, 0, v___x_3451_);
                        v___x_3453_ = v___x_3435_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3451_);
                        lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_a_3450_);
                        v___x_3453_ = v_reuseFailAlloc_3457_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3442_ == 0 {
                    lean_ctor_set(v___x_3441_, 0, v___x_3445_);
                    v___x_3447_ = v___x_3441_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
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
                    v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
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
    mut v_init_3469_: *mut LeanObject,
    mut v_goal_3470_: *mut LeanObject,
    mut v_isTarget_3471_: *mut LeanObject,
    mut v_as_3472_: *mut LeanObject,
    mut v_sz_3473_: *mut LeanObject,
    mut v_i_3474_: *mut LeanObject,
    mut v_b_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3481_: usize = 0;
    let mut v_i_boxed_3482_: usize = 0;
    let mut v_res_3483_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3481_ = lean_unbox_usize(v_sz_3473_);
    lean_dec(v_sz_3473_);
    v_i_boxed_3482_ = lean_unbox_usize(v_i_3474_);
    lean_dec(v_i_3474_);
    v_res_3483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_3469_, v_goal_3470_, v_isTarget_3471_, v_as_3472_, v_sz_boxed_3481_, v_i_boxed_3482_, v_b_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
    lean_dec(v___y_3479_);
    lean_dec_ref(v___y_3478_);
    lean_dec(v___y_3477_);
    lean_dec_ref(v___y_3476_);
    lean_dec_ref(v_as_3472_);
    lean_dec_ref(v_goal_3470_);
    lean_dec_ref(v_init_3469_);
    return v_res_3483_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(
    mut v_init_3484_: *mut LeanObject,
    mut v_goal_3485_: *mut LeanObject,
    mut v_isTarget_3486_: *mut LeanObject,
    mut v_n_3487_: *mut LeanObject,
    mut v_b_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3494_: *mut LeanObject = core::ptr::null_mut();
    v_res_3494_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_3484_, v_goal_3485_, v_isTarget_3486_, v_n_3487_, v_b_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
    lean_dec(v___y_3492_);
    lean_dec_ref(v___y_3491_);
    lean_dec(v___y_3490_);
    lean_dec_ref(v___y_3489_);
    lean_dec_ref(v_n_3487_);
    lean_dec_ref(v_goal_3485_);
    lean_dec_ref(v_init_3484_);
    return v_res_3494_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(
    mut v_goal_3495_: *mut LeanObject,
    mut v_isTarget_3496_: *mut LeanObject,
    mut v_t_3497_: *mut LeanObject,
    mut v_init_3498_: *mut LeanObject,
    mut v___y_3499_: *mut LeanObject,
    mut v___y_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
    mut v___y_3502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v_a_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3518_: usize = 0;
    let mut v___x_3519_: usize = 0;
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v_fst_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut v_a_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut v_a_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3547_: u8 = 0;
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3504_ = lean_ctor_get(v_t_3497_, 0);
                v_tail_3505_ = lean_ctor_get(v_t_3497_, 1);
                lean_inc_ref(v_isTarget_3496_);
                lean_inc_ref(v_init_3498_);
                v___x_3506_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_3498_, v_goal_3495_, v_isTarget_3496_, v_root_3504_, v_init_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
                lean_dec_ref(v_init_3498_);
                if lean_obj_tag(v___x_3506_) == 0 {
                    v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3543_ = (!lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3543_ == 0 {
                        v___x_3509_ = v___x_3506_;
                        v_isShared_3510_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3507_);
                        lean_dec(v___x_3506_);
                        v___x_3509_ = lean_box(0);
                        v_isShared_3510_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_isTarget_3496_);
                    v_a_3544_ = lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3551_ = (!lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3551_ == 0 {
                        v___x_3546_ = v___x_3506_;
                        v_isShared_3547_ = v_isSharedCheck_3551_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3544_);
                        lean_dec(v___x_3506_);
                        v___x_3546_ = lean_box(0);
                        v_isShared_3547_ = v_isSharedCheck_3551_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3507_) == 0 {
                    lean_dec_ref(v_isTarget_3496_);
                    v_a_3511_ = lean_ctor_get(v_a_3507_, 0);
                    lean_inc(v_a_3511_);
                    lean_dec_ref_known(v_a_3507_, 1);
                    if v_isShared_3510_ == 0 {
                        lean_ctor_set(v___x_3509_, 0, v_a_3511_);
                        v___x_3513_ = v___x_3509_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3511_);
                        v___x_3513_ = v_reuseFailAlloc_3514_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3509_);
                    v_a_3515_ = lean_ctor_get(v_a_3507_, 0);
                    lean_inc(v_a_3515_);
                    lean_dec_ref_known(v_a_3507_, 1);
                    v___x_3516_ = lean_box(0);
                    v___x_3517_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3517_, 0, v___x_3516_);
                    lean_ctor_set(v___x_3517_, 1, v_a_3515_);
                    v_sz_3518_ = lean_array_size(v_tail_3505_);
                    v___x_3519_ = 0usize;
                    v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_3495_, v_isTarget_3496_, v_tail_3505_, v_sz_3518_, v___x_3519_, v___x_3517_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
                    if lean_obj_tag(v___x_3520_) == 0 {
                        v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
                        v_isSharedCheck_3534_ = (!lean_is_exclusive(v___x_3520_)) as u8;
                        if v_isSharedCheck_3534_ == 0 {
                            v___x_3523_ = v___x_3520_;
                            v_isShared_3524_ = v_isSharedCheck_3534_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3521_);
                            lean_dec(v___x_3520_);
                            v___x_3523_ = lean_box(0);
                            v_isShared_3524_ = v_isSharedCheck_3534_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3535_ = lean_ctor_get(v___x_3520_, 0);
                        v_isSharedCheck_3542_ = (!lean_is_exclusive(v___x_3520_)) as u8;
                        if v_isSharedCheck_3542_ == 0 {
                            v___x_3537_ = v___x_3520_;
                            v_isShared_3538_ = v_isSharedCheck_3542_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3535_);
                            lean_dec(v___x_3520_);
                            v___x_3537_ = lean_box(0);
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
                v_fst_3525_ = lean_ctor_get(v_a_3521_, 0);
                if lean_obj_tag(v_fst_3525_) == 0 {
                    v_snd_3526_ = lean_ctor_get(v_a_3521_, 1);
                    lean_inc(v_snd_3526_);
                    lean_dec(v_a_3521_);
                    if v_isShared_3524_ == 0 {
                        lean_ctor_set(v___x_3523_, 0, v_snd_3526_);
                        v___x_3528_ = v___x_3523_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_snd_3526_);
                        v___x_3528_ = v_reuseFailAlloc_3529_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3525_);
                    lean_dec(v_a_3521_);
                    v_val_3530_ = lean_ctor_get(v_fst_3525_, 0);
                    lean_inc(v_val_3530_);
                    lean_dec_ref_known(v_fst_3525_, 1);
                    if v_isShared_3524_ == 0 {
                        lean_ctor_set(v___x_3523_, 0, v_val_3530_);
                        v___x_3532_ = v___x_3523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_val_3530_);
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
                    v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
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
                    v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
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
    mut v_goal_3552_: *mut LeanObject,
    mut v_isTarget_3553_: *mut LeanObject,
    mut v_t_3554_: *mut LeanObject,
    mut v_init_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
    mut v___y_3560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3561_: *mut LeanObject = core::ptr::null_mut();
    v_res_3561_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_3552_, v_isTarget_3553_, v_t_3554_, v_init_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
    lean_dec(v___y_3559_);
    lean_dec_ref(v___y_3558_);
    lean_dec(v___y_3557_);
    lean_dec_ref(v___y_3556_);
    lean_dec_ref(v_t_3554_);
    lean_dec_ref(v_goal_3552_);
    return v_res_3561_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(
    mut v_a_3562_: *mut LeanObject,
    mut v_a_3563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3562_) == 0 {
                    v___x_3565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3565_, 0, v_a_3563_);
                    v___x_3566_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3566_, 0, v___x_3565_);
                    return v___x_3566_;
                } else {
                    v_value_3567_ = lean_ctor_get(v_a_3562_, 1);
                    lean_inc(v_value_3567_);
                    v_tail_3568_ = lean_ctor_get(v_a_3562_, 2);
                    lean_inc(v_tail_3568_);
                    lean_dec_ref_known(v_a_3562_, 3);
                    v_num_3569_ = lean_ctor_get(v_value_3567_, 0);
                    lean_inc(v_num_3569_);
                    v_den_3570_ = lean_ctor_get(v_value_3567_, 1);
                    lean_inc(v_den_3570_);
                    lean_dec(v_value_3567_);
                    v___x_3571_ = lean_unsigned_to_nat(1);
                    v___x_3572_ = lean_nat_dec_eq(v_den_3570_, v___x_3571_);
                    lean_dec(v_den_3570_);
                    if v___x_3572_ == 0 {
                        lean_dec(v_num_3569_);
                        v_a_3562_ = v_tail_3568_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3574_ = lean_box(0);
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
    mut v_a_3577_: *mut LeanObject,
    mut v_a_3578_: *mut LeanObject,
    mut v___y_3579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3580_: *mut LeanObject = core::ptr::null_mut();
    v_res_3580_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_3577_, v_a_3578_);
    return v_res_3580_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(
    mut v_as_3581_: *mut LeanObject,
    mut v_sz_3582_: usize,
    mut v_i_3583_: usize,
    mut v_b_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
    mut v___y_3587_: *mut LeanObject,
    mut v___y_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v_a_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: usize = 0;
    let mut v___x_3604_: usize = 0;
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut v_a_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3590_ = lean_usize_dec_lt(v_i_3583_, v_sz_3582_);
                if v___x_3590_ == 0 {
                    v___x_3591_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3591_, 0, v_b_3584_);
                    return v___x_3591_;
                } else {
                    v_a_3592_ = lean_array_uget_borrowed(v_as_3581_, v_i_3583_);
                    lean_inc(v_a_3592_);
                    v___x_3593_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_3592_, v_b_3584_);
                    if lean_obj_tag(v___x_3593_) == 0 {
                        v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
                        v_isSharedCheck_3606_ = (!lean_is_exclusive(v___x_3593_)) as u8;
                        if v_isSharedCheck_3606_ == 0 {
                            v___x_3596_ = v___x_3593_;
                            v_isShared_3597_ = v_isSharedCheck_3606_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3594_);
                            lean_dec(v___x_3593_);
                            v___x_3596_ = lean_box(0);
                            v_isShared_3597_ = v_isSharedCheck_3606_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3607_ = lean_ctor_get(v___x_3593_, 0);
                        v_isSharedCheck_3614_ = (!lean_is_exclusive(v___x_3593_)) as u8;
                        if v_isSharedCheck_3614_ == 0 {
                            v___x_3609_ = v___x_3593_;
                            v_isShared_3610_ = v_isSharedCheck_3614_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3607_);
                            lean_dec(v___x_3593_);
                            v___x_3609_ = lean_box(0);
                            v_isShared_3610_ = v_isSharedCheck_3614_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3594_) == 0 {
                    v_a_3598_ = lean_ctor_get(v_a_3594_, 0);
                    lean_inc(v_a_3598_);
                    lean_dec_ref_known(v_a_3594_, 1);
                    if v_isShared_3597_ == 0 {
                        lean_ctor_set(v___x_3596_, 0, v_a_3598_);
                        v___x_3600_ = v___x_3596_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3598_);
                        v___x_3600_ = v_reuseFailAlloc_3601_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3596_);
                    v_a_3602_ = lean_ctor_get(v_a_3594_, 0);
                    lean_inc(v_a_3602_);
                    lean_dec_ref_known(v_a_3594_, 1);
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
                    v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
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
    mut v_as_3615_: *mut LeanObject,
    mut v_sz_3616_: *mut LeanObject,
    mut v_i_3617_: *mut LeanObject,
    mut v_b_3618_: *mut LeanObject,
    mut v___y_3619_: *mut LeanObject,
    mut v___y_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3624_: usize = 0;
    let mut v_i_boxed_3625_: usize = 0;
    let mut v_res_3626_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3624_ = lean_unbox_usize(v_sz_3616_);
    lean_dec(v_sz_3616_);
    v_i_boxed_3625_ = lean_unbox_usize(v_i_3617_);
    lean_dec(v_i_3617_);
    v_res_3626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_3615_, v_sz_boxed_3624_, v_i_boxed_3625_, v_b_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
    lean_dec(v___y_3622_);
    lean_dec_ref(v___y_3621_);
    lean_dec(v___y_3620_);
    lean_dec_ref(v___y_3619_);
    lean_dec_ref(v_as_3615_);
    return v_res_3626_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0()
-> *mut LeanObject {
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    v___x_3627_ = lean_box(0);
    v___x_3628_ = lean_unsigned_to_nat(16);
    v___x_3629_ = lean_mk_array(v___x_3628_, v___x_3627_);
    return v___x_3629_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1()
-> *mut LeanObject {
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_used_3632_: *mut LeanObject = core::ptr::null_mut();
    v___x_3630_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
    v___x_3631_ = lean_unsigned_to_nat(0);
    v_used_3632_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_used_3632_, 0, v___x_3631_);
    lean_ctor_set(v_used_3632_, 1, v___x_3630_);
    return v_used_3632_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(
    mut v_goal_3633_: *mut LeanObject,
    mut v_isTarget_3634_: *mut LeanObject,
    mut v_model_3635_: *mut LeanObject,
    mut v_a_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
    mut v_a_3638_: *mut LeanObject,
    mut v_a_3639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_used_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3643_: usize = 0;
    let mut v___x_3644_: usize = 0;
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprs_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextVal_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v_snd_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_a_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v_a_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3674_: u8 = 0;
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3641_ = lean_ctor_get(v_model_3635_, 1);
                v_used_3642_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
                v_sz_3643_ = lean_array_size(v_buckets_3641_);
                v___x_3644_ = 0usize;
                v___x_3645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_3641_, v_sz_3643_, v___x_3644_, v_used_3642_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
                if lean_obj_tag(v___x_3645_) == 0 {
                    v_toGoalState_3646_ = lean_ctor_get(v_goal_3633_, 0);
                    v_a_3647_ = lean_ctor_get(v___x_3645_, 0);
                    lean_inc(v_a_3647_);
                    lean_dec_ref_known(v___x_3645_, 1);
                    v_exprs_3648_ = lean_ctor_get(v_toGoalState_3646_, 2);
                    v_nextVal_3649_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
                    v___x_3650_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3650_, 0, v_a_3647_);
                    lean_ctor_set(v___x_3650_, 1, v_model_3635_);
                    v___x_3651_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3651_, 0, v_nextVal_3649_);
                    lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                    v___x_3652_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_3633_, v_isTarget_3634_, v_exprs_3648_, v___x_3651_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
                    if lean_obj_tag(v___x_3652_) == 0 {
                        v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
                        v_isSharedCheck_3662_ = (!lean_is_exclusive(v___x_3652_)) as u8;
                        if v_isSharedCheck_3662_ == 0 {
                            v___x_3655_ = v___x_3652_;
                            v_isShared_3656_ = v_isSharedCheck_3662_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3653_);
                            lean_dec(v___x_3652_);
                            v___x_3655_ = lean_box(0);
                            v_isShared_3656_ = v_isSharedCheck_3662_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3663_ = lean_ctor_get(v___x_3652_, 0);
                        v_isSharedCheck_3670_ = (!lean_is_exclusive(v___x_3652_)) as u8;
                        if v_isSharedCheck_3670_ == 0 {
                            v___x_3665_ = v___x_3652_;
                            v_isShared_3666_ = v_isSharedCheck_3670_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3663_);
                            lean_dec(v___x_3652_);
                            v___x_3665_ = lean_box(0);
                            v_isShared_3666_ = v_isSharedCheck_3670_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_model_3635_);
                    lean_dec_ref(v_isTarget_3634_);
                    v_a_3671_ = lean_ctor_get(v___x_3645_, 0);
                    v_isSharedCheck_3678_ = (!lean_is_exclusive(v___x_3645_)) as u8;
                    if v_isSharedCheck_3678_ == 0 {
                        v___x_3673_ = v___x_3645_;
                        v_isShared_3674_ = v_isSharedCheck_3678_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3671_);
                        lean_dec(v___x_3645_);
                        v___x_3673_ = lean_box(0);
                        v_isShared_3674_ = v_isSharedCheck_3678_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3657_ = lean_ctor_get(v_a_3653_, 1);
                lean_inc(v_snd_3657_);
                lean_dec(v_a_3653_);
                v_snd_3658_ = lean_ctor_get(v_snd_3657_, 1);
                lean_inc(v_snd_3658_);
                lean_dec(v_snd_3657_);
                if v_isShared_3656_ == 0 {
                    lean_ctor_set(v___x_3655_, 0, v_snd_3658_);
                    v___x_3660_ = v___x_3655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_snd_3658_);
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
                    v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
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
                    v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
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
    mut v_goal_3679_: *mut LeanObject,
    mut v_isTarget_3680_: *mut LeanObject,
    mut v_model_3681_: *mut LeanObject,
    mut v_a_3682_: *mut LeanObject,
    mut v_a_3683_: *mut LeanObject,
    mut v_a_3684_: *mut LeanObject,
    mut v_a_3685_: *mut LeanObject,
    mut v_a_3686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3687_: *mut LeanObject = core::ptr::null_mut();
    v_res_3687_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_3679_, v_isTarget_3680_, v_model_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
    lean_dec(v_a_3685_);
    lean_dec_ref(v_a_3684_);
    lean_dec(v_a_3683_);
    lean_dec_ref(v_a_3682_);
    lean_dec_ref(v_goal_3679_);
    return v_res_3687_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(
    mut v_00_u03b2_3688_: *mut LeanObject,
    mut v_m_3689_: *mut LeanObject,
    mut v_a_3690_: *mut LeanObject,
    mut v_b_3691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    v___x_3692_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_3689_, v_a_3690_, v_b_3691_);
    return v___x_3692_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(
    mut v_a_3693_: *mut LeanObject,
    mut v_a_3694_: *mut LeanObject,
    mut v___y_3695_: *mut LeanObject,
    mut v___y_3696_: *mut LeanObject,
    mut v___y_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    v___x_3700_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_3693_, v_a_3694_);
    return v___x_3700_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(
    mut v_a_3701_: *mut LeanObject,
    mut v_a_3702_: *mut LeanObject,
    mut v___y_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3708_: *mut LeanObject = core::ptr::null_mut();
    v_res_3708_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_3701_, v_a_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
    lean_dec(v___y_3706_);
    lean_dec_ref(v___y_3705_);
    lean_dec(v___y_3704_);
    lean_dec_ref(v___y_3703_);
    return v_res_3708_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(
    mut v_00_u03b2_3709_: *mut LeanObject,
    mut v_data_3710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    v___x_3711_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_3710_);
    return v___x_3711_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3712_: *mut LeanObject,
    mut v_i_3713_: *mut LeanObject,
    mut v_source_3714_: *mut LeanObject,
    mut v_target_3715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    v___x_3716_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_3713_, v_source_3714_, v_target_3715_);
    return v___x_3716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b2_3717_: *mut LeanObject,
    mut v_x_3718_: *mut LeanObject,
    mut v_x_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v___x_3720_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_3718_, v_x_3719_);
    return v___x_3720_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(
    mut v_goal_3721_: *mut LeanObject,
    mut v_hi_3722_: *mut LeanObject,
    mut v_pivot_3723_: *mut LeanObject,
    mut v_as_3724_: *mut LeanObject,
    mut v_i_3725_: *mut LeanObject,
    mut v_k_3726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3728_: u8 = 0;
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_u2081_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_u2082_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: u8 = 0;
    let mut v___x_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3737_ = lean_nat_dec_lt(v_k_3726_, v_hi_3722_);
                if v___x_3737_ == 0 {
                    lean_dec(v_k_3726_);
                    v___x_3738_ = lean_array_fswap(v_as_3724_, v_i_3725_, v_hi_3722_);
                    v___x_3739_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3739_, 0, v_i_3725_);
                    lean_ctor_set(v___x_3739_, 1, v___x_3738_);
                    return v___x_3739_;
                } else {
                    v___x_3740_ = lean_array_fget_borrowed(v_as_3724_, v_k_3726_);
                    v_fst_3741_ = lean_ctor_get(v___x_3740_, 0);
                    v_fst_3742_ = lean_ctor_get(v_pivot_3723_, 0);
                    v_g_u2081_3743_ =
                        l_Lean_Meta_Grind_Goal_getGeneration(v_goal_3721_, v_fst_3741_);
                    v_g_u2082_3744_ =
                        l_Lean_Meta_Grind_Goal_getGeneration(v_goal_3721_, v_fst_3742_);
                    v___x_3745_ = lean_nat_dec_eq(v_g_u2081_3743_, v_g_u2082_3744_);
                    if v___x_3745_ == 0 {
                        v___x_3746_ = lean_nat_dec_lt(v_g_u2081_3743_, v_g_u2082_3744_);
                        lean_dec(v_g_u2082_3744_);
                        lean_dec(v_g_u2081_3743_);
                        v___y_3728_ = v___x_3746_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_g_u2082_3744_);
                        lean_dec(v_g_u2081_3743_);
                        v___x_3747_ = lean_expr_lt(v_fst_3741_, v_fst_3742_);
                        v___y_3728_ = v___x_3747_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3728_ == 0 {
                    v___x_3729_ = lean_unsigned_to_nat(1);
                    v___x_3730_ = lean_nat_add(v_k_3726_, v___x_3729_);
                    lean_dec(v_k_3726_);
                    v_k_3726_ = v___x_3730_;
                    state = 0;
                    continue;
                } else {
                    v___x_3732_ = lean_array_fswap(v_as_3724_, v_i_3725_, v_k_3726_);
                    v___x_3733_ = lean_unsigned_to_nat(1);
                    v___x_3734_ = lean_nat_add(v_i_3725_, v___x_3733_);
                    lean_dec(v_i_3725_);
                    v___x_3735_ = lean_nat_add(v_k_3726_, v___x_3733_);
                    lean_dec(v_k_3726_);
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
    mut v_goal_3748_: *mut LeanObject,
    mut v_hi_3749_: *mut LeanObject,
    mut v_pivot_3750_: *mut LeanObject,
    mut v_as_3751_: *mut LeanObject,
    mut v_i_3752_: *mut LeanObject,
    mut v_k_3753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3754_: *mut LeanObject = core::ptr::null_mut();
    v_res_3754_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_3748_, v_hi_3749_, v_pivot_3750_, v_as_3751_, v_i_3752_, v_k_3753_);
    lean_dec_ref(v_pivot_3750_);
    lean_dec(v_hi_3749_);
    lean_dec_ref(v_goal_3748_);
    return v_res_3754_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(
    mut v_goal_3755_: *mut LeanObject,
    mut v_x_3756_: *mut LeanObject,
    mut v_x_3757_: *mut LeanObject,
) -> u8 {
    let mut v_fst_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_u2081_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_u2082_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: u8 = 0;
    v_fst_3758_ = lean_ctor_get(v_x_3756_, 0);
    v_fst_3759_ = lean_ctor_get(v_x_3757_, 0);
    v_g_u2081_3760_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_3755_, v_fst_3758_);
    v_g_u2082_3761_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_3755_, v_fst_3759_);
    v___x_3762_ = lean_nat_dec_eq(v_g_u2081_3760_, v_g_u2082_3761_);
    if v___x_3762_ == 0 {
        let mut v___x_3763_: u8 = 0;
        v___x_3763_ = lean_nat_dec_lt(v_g_u2081_3760_, v_g_u2082_3761_);
        lean_dec(v_g_u2082_3761_);
        lean_dec(v_g_u2081_3760_);
        return v___x_3763_;
    } else {
        let mut v___x_3764_: u8 = 0;
        lean_dec(v_g_u2082_3761_);
        lean_dec(v_g_u2081_3760_);
        v___x_3764_ = lean_expr_lt(v_fst_3758_, v_fst_3759_);
        return v___x_3764_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(
    mut v_goal_3765_: *mut LeanObject,
    mut v_x_3766_: *mut LeanObject,
    mut v_x_3767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3768_: u8 = 0;
    let mut v_r_3769_: *mut LeanObject = core::ptr::null_mut();
    v_res_3768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_3765_, v_x_3766_, v_x_3767_);
    lean_dec_ref(v_x_3767_);
    lean_dec_ref(v_x_3766_);
    lean_dec_ref(v_goal_3765_);
    v_r_3769_ = lean_box((v_res_3768_) as usize);
    return v_r_3769_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(
    mut v_goal_3770_: *mut LeanObject,
    mut v_n_3771_: *mut LeanObject,
    mut v_as_3772_: *mut LeanObject,
    mut v_lo_3773_: *mut LeanObject,
    mut v_hi_3774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: u8 = 0;
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: u8 = 0;
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3786_ = lean_nat_dec_lt(v_lo_3773_, v_hi_3774_);
                if v___x_3786_ == 0 {
                    lean_dec(v_lo_3773_);
                    return v_as_3772_;
                } else {
                    v___x_3787_ = lean_nat_add(v_lo_3773_, v_hi_3774_);
                    v___x_3788_ = lean_unsigned_to_nat(1);
                    v_mid_3789_ = lean_nat_shiftr(v___x_3787_, v___x_3788_);
                    lean_dec(v___x_3787_);
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
                lean_inc_n(v_lo_3773_, 2);
                v___x_3778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_3770_, v_hi_3774_, v_pivot_3777_, v___y_3776_, v_lo_3773_, v_lo_3773_);
                lean_dec(v_pivot_3777_);
                v_fst_3779_ = lean_ctor_get(v___x_3778_, 0);
                lean_inc(v_fst_3779_);
                v_snd_3780_ = lean_ctor_get(v___x_3778_, 1);
                lean_inc(v_snd_3780_);
                lean_dec_ref(v___x_3778_);
                v___x_3781_ = lean_nat_dec_le(v_hi_3774_, v_fst_3779_);
                if v___x_3781_ == 0 {
                    v___x_3782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3770_, v_n_3771_, v_snd_3780_, v_lo_3773_, v_fst_3779_);
                    v___x_3783_ = lean_unsigned_to_nat(1);
                    v___x_3784_ = lean_nat_add(v_fst_3779_, v___x_3783_);
                    lean_dec(v_fst_3779_);
                    v_as_3772_ = v___x_3782_;
                    v_lo_3773_ = v___x_3784_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_3779_);
                    lean_dec(v_lo_3773_);
                    return v_snd_3780_;
                }
            }
            2 => {
                v___x_3792_ = lean_array_fget_borrowed(v___y_3791_, v_mid_3789_);
                v___x_3793_ = lean_array_fget_borrowed(v___y_3791_, v_hi_3774_);
                v___x_3794_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_3770_, v___x_3792_, v___x_3793_);
                if v___x_3794_ == 0 {
                    lean_dec(v_mid_3789_);
                    v___y_3776_ = v___y_3791_;
                    state = 1;
                    continue;
                } else {
                    v___x_3795_ = lean_array_fswap(v___y_3791_, v_mid_3789_, v_hi_3774_);
                    lean_dec(v_mid_3789_);
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
    mut v_goal_3806_: *mut LeanObject,
    mut v_n_3807_: *mut LeanObject,
    mut v_as_3808_: *mut LeanObject,
    mut v_lo_3809_: *mut LeanObject,
    mut v_hi_3810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3811_: *mut LeanObject = core::ptr::null_mut();
    v_res_3811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3806_, v_n_3807_, v_as_3808_, v_lo_3809_, v_hi_3810_);
    lean_dec(v_hi_3810_);
    lean_dec(v_n_3807_);
    lean_dec_ref(v_goal_3806_);
    return v_res_3811_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(
    mut v_goal_3812_: *mut LeanObject,
    mut v_m_3813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3814_ = lean_array_get_size(v_m_3813_);
                v___x_3815_ = lean_unsigned_to_nat(0);
                v___x_3816_ = lean_nat_dec_eq(v___x_3814_, v___x_3815_);
                if v___x_3816_ == 0 {
                    v___x_3817_ = lean_unsigned_to_nat(1);
                    v___x_3818_ = lean_nat_sub(v___x_3814_, v___x_3817_);
                    v___x_3824_ = lean_nat_dec_le(v___x_3815_, v___x_3818_);
                    if v___x_3824_ == 0 {
                        lean_inc(v___x_3818_);
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
                    lean_dec(v___x_3818_);
                    lean_inc(v___y_3820_);
                    v___x_3822_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3812_, v___x_3814_, v_m_3813_, v___y_3820_, v___y_3820_);
                    lean_dec(v___y_3820_);
                    return v___x_3822_;
                } else {
                    v___x_3823_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3812_, v___x_3814_, v_m_3813_, v___y_3820_, v___x_3818_);
                    lean_dec(v___x_3818_);
                    return v___x_3823_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(
    mut v_goal_3825_: *mut LeanObject,
    mut v_m_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3827_: *mut LeanObject = core::ptr::null_mut();
    v_res_3827_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(
            v_goal_3825_,
            v_m_3826_,
        );
    lean_dec_ref(v_goal_3825_);
    return v_res_3827_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(
    mut v_goal_3828_: *mut LeanObject,
    mut v_n_3829_: *mut LeanObject,
    mut v_as_3830_: *mut LeanObject,
    mut v_lo_3831_: *mut LeanObject,
    mut v_hi_3832_: *mut LeanObject,
    mut v_w_3833_: *mut LeanObject,
    mut v_hlo_3834_: *mut LeanObject,
    mut v_hhi_3835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    v___x_3836_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_3828_, v_n_3829_, v_as_3830_, v_lo_3831_, v_hi_3832_);
    return v___x_3836_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(
    mut v_goal_3837_: *mut LeanObject,
    mut v_n_3838_: *mut LeanObject,
    mut v_as_3839_: *mut LeanObject,
    mut v_lo_3840_: *mut LeanObject,
    mut v_hi_3841_: *mut LeanObject,
    mut v_w_3842_: *mut LeanObject,
    mut v_hlo_3843_: *mut LeanObject,
    mut v_hhi_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3845_: *mut LeanObject = core::ptr::null_mut();
    v_res_3845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_3837_, v_n_3838_, v_as_3839_, v_lo_3840_, v_hi_3841_, v_w_3842_, v_hlo_3843_, v_hhi_3844_);
    lean_dec(v_hi_3841_);
    lean_dec(v_n_3838_);
    lean_dec_ref(v_goal_3837_);
    return v_res_3845_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(
    mut v_goal_3846_: *mut LeanObject,
    mut v_n_3847_: *mut LeanObject,
    mut v_lo_3848_: *mut LeanObject,
    mut v_hi_3849_: *mut LeanObject,
    mut v_hhi_3850_: *mut LeanObject,
    mut v_pivot_3851_: *mut LeanObject,
    mut v_as_3852_: *mut LeanObject,
    mut v_i_3853_: *mut LeanObject,
    mut v_k_3854_: *mut LeanObject,
    mut v_ilo_3855_: *mut LeanObject,
    mut v_ik_3856_: *mut LeanObject,
    mut v_w_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    v___x_3858_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_3846_, v_hi_3849_, v_pivot_3851_, v_as_3852_, v_i_3853_, v_k_3854_);
    return v___x_3858_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(
    mut v_goal_3859_: *mut LeanObject,
    mut v_n_3860_: *mut LeanObject,
    mut v_lo_3861_: *mut LeanObject,
    mut v_hi_3862_: *mut LeanObject,
    mut v_hhi_3863_: *mut LeanObject,
    mut v_pivot_3864_: *mut LeanObject,
    mut v_as_3865_: *mut LeanObject,
    mut v_i_3866_: *mut LeanObject,
    mut v_k_3867_: *mut LeanObject,
    mut v_ilo_3868_: *mut LeanObject,
    mut v_ik_3869_: *mut LeanObject,
    mut v_w_3870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3871_: *mut LeanObject = core::ptr::null_mut();
    v_res_3871_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_3859_, v_n_3860_, v_lo_3861_, v_hi_3862_, v_hhi_3863_, v_pivot_3864_, v_as_3865_, v_i_3866_, v_k_3867_, v_ilo_3868_, v_ik_3869_, v_w_3870_);
    lean_dec_ref(v_pivot_3864_);
    lean_dec(v_hi_3862_);
    lean_dec(v_lo_3861_);
    lean_dec(v_n_3860_);
    lean_dec_ref(v_goal_3859_);
    return v_res_3871_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: u8 = 0;
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3872_) == 0 {
                    v___x_3875_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3875_, 0, v_a_3873_);
                    v___x_3876_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3876_, 0, v___x_3875_);
                    return v___x_3876_;
                } else {
                    v_key_3877_ = lean_ctor_get(v_a_3872_, 0);
                    lean_inc_n(v_key_3877_, 2);
                    v_value_3878_ = lean_ctor_get(v_a_3872_, 1);
                    lean_inc(v_value_3878_);
                    v_tail_3879_ = lean_ctor_get(v_a_3872_, 2);
                    lean_inc(v_tail_3879_);
                    lean_dec_ref_known(v_a_3872_, 3);
                    v___x_3880_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_3877_);
                    if v___x_3880_ == 0 {
                        v___x_3881_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3881_, 0, v_key_3877_);
                        lean_ctor_set(v___x_3881_, 1, v_value_3878_);
                        v___x_3882_ = lean_array_push(v_a_3873_, v___x_3881_);
                        v_a_3872_ = v_tail_3879_;
                        v_a_3873_ = v___x_3882_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_value_3878_);
                        lean_dec(v_key_3877_);
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
    mut v_a_3885_: *mut LeanObject,
    mut v_a_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3888_: *mut LeanObject = core::ptr::null_mut();
    v_res_3888_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_3885_, v_a_3886_);
    return v_res_3888_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(
    mut v_as_3889_: *mut LeanObject,
    mut v_sz_3890_: usize,
    mut v_i_3891_: usize,
    mut v_b_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
    mut v___y_3896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3905_: u8 = 0;
    let mut v_a_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: usize = 0;
    let mut v___x_3912_: usize = 0;
    let mut v_isSharedCheck_3914_: u8 = 0;
    let mut v_a_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3898_ = lean_usize_dec_lt(v_i_3891_, v_sz_3890_);
                if v___x_3898_ == 0 {
                    v___x_3899_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3899_, 0, v_b_3892_);
                    return v___x_3899_;
                } else {
                    v_a_3900_ = lean_array_uget_borrowed(v_as_3889_, v_i_3891_);
                    lean_inc(v_a_3900_);
                    v___x_3901_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_3900_, v_b_3892_);
                    if lean_obj_tag(v___x_3901_) == 0 {
                        v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
                        v_isSharedCheck_3914_ = (!lean_is_exclusive(v___x_3901_)) as u8;
                        if v_isSharedCheck_3914_ == 0 {
                            v___x_3904_ = v___x_3901_;
                            v_isShared_3905_ = v_isSharedCheck_3914_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3902_);
                            lean_dec(v___x_3901_);
                            v___x_3904_ = lean_box(0);
                            v_isShared_3905_ = v_isSharedCheck_3914_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3915_ = lean_ctor_get(v___x_3901_, 0);
                        v_isSharedCheck_3922_ = (!lean_is_exclusive(v___x_3901_)) as u8;
                        if v_isSharedCheck_3922_ == 0 {
                            v___x_3917_ = v___x_3901_;
                            v_isShared_3918_ = v_isSharedCheck_3922_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3915_);
                            lean_dec(v___x_3901_);
                            v___x_3917_ = lean_box(0);
                            v_isShared_3918_ = v_isSharedCheck_3922_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3902_) == 0 {
                    v_a_3906_ = lean_ctor_get(v_a_3902_, 0);
                    lean_inc(v_a_3906_);
                    lean_dec_ref_known(v_a_3902_, 1);
                    if v_isShared_3905_ == 0 {
                        lean_ctor_set(v___x_3904_, 0, v_a_3906_);
                        v___x_3908_ = v___x_3904_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3906_);
                        v___x_3908_ = v_reuseFailAlloc_3909_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3904_);
                    v_a_3910_ = lean_ctor_get(v_a_3902_, 0);
                    lean_inc(v_a_3910_);
                    lean_dec_ref_known(v_a_3902_, 1);
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
                    v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
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
    mut v_as_3923_: *mut LeanObject,
    mut v_sz_3924_: *mut LeanObject,
    mut v_i_3925_: *mut LeanObject,
    mut v_b_3926_: *mut LeanObject,
    mut v___y_3927_: *mut LeanObject,
    mut v___y_3928_: *mut LeanObject,
    mut v___y_3929_: *mut LeanObject,
    mut v___y_3930_: *mut LeanObject,
    mut v___y_3931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3932_: usize = 0;
    let mut v_i_boxed_3933_: usize = 0;
    let mut v_res_3934_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3932_ = lean_unbox_usize(v_sz_3924_);
    lean_dec(v_sz_3924_);
    v_i_boxed_3933_ = lean_unbox_usize(v_i_3925_);
    lean_dec(v_i_3925_);
    v_res_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_3923_, v_sz_boxed_3932_, v_i_boxed_3933_, v_b_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
    lean_dec(v___y_3930_);
    lean_dec_ref(v___y_3929_);
    lean_dec(v___y_3928_);
    lean_dec_ref(v___y_3927_);
    lean_dec_ref(v_as_3923_);
    return v_res_3934_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_finalizeModel(
    mut v_goal_3937_: *mut LeanObject,
    mut v_isTarget_3938_: *mut LeanObject,
    mut v_model_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
    mut v_a_3942_: *mut LeanObject,
    mut v_a_3943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3949_: usize = 0;
    let mut v___x_3950_: usize = 0;
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3945_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_3937_, v_isTarget_3938_, v_model_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
                if lean_obj_tag(v___x_3945_) == 0 {
                    v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
                    lean_inc(v_a_3946_);
                    lean_dec_ref_known(v___x_3945_, 1);
                    v_buckets_3947_ = lean_ctor_get(v_a_3946_, 1);
                    lean_inc_ref(v_buckets_3947_);
                    lean_dec(v_a_3946_);
                    v___x_3948_ = l_Lean_Meta_Grind_Arith_finalizeModel___closed__0;
                    v_sz_3949_ = lean_array_size(v_buckets_3947_);
                    v___x_3950_ = 0usize;
                    v___x_3951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_3947_, v_sz_3949_, v___x_3950_, v___x_3948_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
                    lean_dec_ref(v_buckets_3947_);
                    if lean_obj_tag(v___x_3951_) == 0 {
                        v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
                        v_isSharedCheck_3960_ = (!lean_is_exclusive(v___x_3951_)) as u8;
                        if v_isSharedCheck_3960_ == 0 {
                            v___x_3954_ = v___x_3951_;
                            v_isShared_3955_ = v_isSharedCheck_3960_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3952_);
                            lean_dec(v___x_3951_);
                            v___x_3954_ = lean_box(0);
                            v_isShared_3955_ = v_isSharedCheck_3960_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3951_;
                    }
                } else {
                    v_a_3961_ = lean_ctor_get(v___x_3945_, 0);
                    v_isSharedCheck_3968_ = (!lean_is_exclusive(v___x_3945_)) as u8;
                    if v_isSharedCheck_3968_ == 0 {
                        v___x_3963_ = v___x_3945_;
                        v_isShared_3964_ = v_isSharedCheck_3968_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3961_);
                        lean_dec(v___x_3945_);
                        v___x_3963_ = lean_box(0);
                        v_isShared_3964_ = v_isSharedCheck_3968_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3956_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_3937_, v_a_3952_);
                if v_isShared_3955_ == 0 {
                    lean_ctor_set(v___x_3954_, 0, v___x_3956_);
                    v___x_3958_ = v___x_3954_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
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
                    v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
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
    mut v_goal_3969_: *mut LeanObject,
    mut v_isTarget_3970_: *mut LeanObject,
    mut v_model_3971_: *mut LeanObject,
    mut v_a_3972_: *mut LeanObject,
    mut v_a_3973_: *mut LeanObject,
    mut v_a_3974_: *mut LeanObject,
    mut v_a_3975_: *mut LeanObject,
    mut v_a_3976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3977_: *mut LeanObject = core::ptr::null_mut();
    v_res_3977_ = l_Lean_Meta_Grind_Arith_finalizeModel(
        v_goal_3969_,
        v_isTarget_3970_,
        v_model_3971_,
        v_a_3972_,
        v_a_3973_,
        v_a_3974_,
        v_a_3975_,
    );
    lean_dec(v_a_3975_);
    lean_dec_ref(v_a_3974_);
    lean_dec(v_a_3973_);
    lean_dec_ref(v_a_3972_);
    lean_dec_ref(v_goal_3969_);
    return v_res_3977_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(
    mut v_a_3978_: *mut LeanObject,
    mut v_a_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    v___x_3985_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_3978_, v_a_3979_);
    return v___x_3985_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(
    mut v_a_3986_: *mut LeanObject,
    mut v_a_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3993_: *mut LeanObject = core::ptr::null_mut();
    v_res_3993_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_3986_, v_a_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
    lean_dec(v___y_3991_);
    lean_dec_ref(v___y_3990_);
    lean_dec(v___y_3989_);
    lean_dec_ref(v___y_3988_);
    return v_res_3993_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(
    mut v_msgData_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
    mut v___y_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    v___x_4000_ = lean_st_ref_get(v___y_3998_);
    v_env_4001_ = lean_ctor_get(v___x_4000_, 0);
    lean_inc_ref(v_env_4001_);
    lean_dec(v___x_4000_);
    v___x_4002_ = lean_st_ref_get(v___y_3996_);
    v_mctx_4003_ = lean_ctor_get(v___x_4002_, 0);
    lean_inc_ref(v_mctx_4003_);
    lean_dec(v___x_4002_);
    v_lctx_4004_ = lean_ctor_get(v___y_3995_, 2);
    v_options_4005_ = lean_ctor_get(v___y_3997_, 2);
    lean_inc_ref(v_options_4005_);
    lean_inc_ref(v_lctx_4004_);
    v___x_4006_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4006_, 0, v_env_4001_);
    lean_ctor_set(v___x_4006_, 1, v_mctx_4003_);
    lean_ctor_set(v___x_4006_, 2, v_lctx_4004_);
    lean_ctor_set(v___x_4006_, 3, v_options_4005_);
    v___x_4007_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4007_, 0, v___x_4006_);
    lean_ctor_set(v___x_4007_, 1, v_msgData_3994_);
    v___x_4008_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4008_, 0, v___x_4007_);
    return v___x_4008_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(
    mut v_msgData_4009_: *mut LeanObject,
    mut v___y_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
    mut v___y_4014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4015_: *mut LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
    lean_dec(v___y_4013_);
    lean_dec_ref(v___y_4012_);
    lean_dec(v___y_4011_);
    lean_dec_ref(v___y_4010_);
    return v_res_4015_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0()
-> f64 {
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: f64 = 0.0;
    v___x_4016_ = lean_unsigned_to_nat(0);
    v___x_4017_ = lean_float_of_nat(v___x_4016_);
    return v___x_4017_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(
    mut v_cls_4021_: *mut LeanObject,
    mut v_msg_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v_tid_4047_: u64 = 0;
    let mut v_traces_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4051_: u8 = 0;
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: f64 = 0.0;
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_isSharedCheck_4073_: u8 = 0;
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4028_ = lean_ctor_get(v___y_4025_, 5);
                v___x_4029_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
                v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
                v_isSharedCheck_4074_ = (!lean_is_exclusive(v___x_4029_)) as u8;
                if v_isSharedCheck_4074_ == 0 {
                    v___x_4032_ = v___x_4029_;
                    v_isShared_4033_ = v_isSharedCheck_4074_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4030_);
                    lean_dec(v___x_4029_);
                    v___x_4032_ = lean_box(0);
                    v_isShared_4033_ = v_isSharedCheck_4074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4034_ = lean_st_ref_take(v___y_4026_);
                v_traceState_4035_ = lean_ctor_get(v___x_4034_, 4);
                v_env_4036_ = lean_ctor_get(v___x_4034_, 0);
                v_nextMacroScope_4037_ = lean_ctor_get(v___x_4034_, 1);
                v_ngen_4038_ = lean_ctor_get(v___x_4034_, 2);
                v_auxDeclNGen_4039_ = lean_ctor_get(v___x_4034_, 3);
                v_cache_4040_ = lean_ctor_get(v___x_4034_, 5);
                v_messages_4041_ = lean_ctor_get(v___x_4034_, 6);
                v_infoState_4042_ = lean_ctor_get(v___x_4034_, 7);
                v_snapshotTasks_4043_ = lean_ctor_get(v___x_4034_, 8);
                v_isSharedCheck_4073_ = (!lean_is_exclusive(v___x_4034_)) as u8;
                if v_isSharedCheck_4073_ == 0 {
                    v___x_4045_ = v___x_4034_;
                    v_isShared_4046_ = v_isSharedCheck_4073_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4043_);
                    lean_inc(v_infoState_4042_);
                    lean_inc(v_messages_4041_);
                    lean_inc(v_cache_4040_);
                    lean_inc(v_traceState_4035_);
                    lean_inc(v_auxDeclNGen_4039_);
                    lean_inc(v_ngen_4038_);
                    lean_inc(v_nextMacroScope_4037_);
                    lean_inc(v_env_4036_);
                    lean_dec(v___x_4034_);
                    v___x_4045_ = lean_box(0);
                    v_isShared_4046_ = v_isSharedCheck_4073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4047_ = lean_ctor_get_uint64(
                    v_traceState_4035_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4048_ = lean_ctor_get(v_traceState_4035_, 0);
                v_isSharedCheck_4072_ = (!lean_is_exclusive(v_traceState_4035_)) as u8;
                if v_isSharedCheck_4072_ == 0 {
                    v___x_4050_ = v_traceState_4035_;
                    v_isShared_4051_ = v_isSharedCheck_4072_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4048_);
                    lean_dec(v_traceState_4035_);
                    v___x_4050_ = lean_box(0);
                    v_isShared_4051_ = v_isSharedCheck_4072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4052_ = lean_box(0);
                v___x_4053_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
                v___x_4054_ = 0;
                v___x_4055_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1;
                v___x_4056_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4056_, 0, v_cls_4021_);
                lean_ctor_set(v___x_4056_, 1, v___x_4052_);
                lean_ctor_set(v___x_4056_, 2, v___x_4055_);
                lean_ctor_set_float(
                    v___x_4056_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4053_,
                );
                lean_ctor_set_float(
                    v___x_4056_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4053_,
                );
                lean_ctor_set_uint8(
                    v___x_4056_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4054_,
                );
                v___x_4057_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2;
                v___x_4058_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4058_, 0, v___x_4056_);
                lean_ctor_set(v___x_4058_, 1, v_a_4030_);
                lean_ctor_set(v___x_4058_, 2, v___x_4057_);
                lean_inc(v_ref_4028_);
                v___x_4059_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4059_, 0, v_ref_4028_);
                lean_ctor_set(v___x_4059_, 1, v___x_4058_);
                v___x_4060_ = l_Lean_PersistentArray_push___redArg(v_traces_4048_, v___x_4059_);
                if v_isShared_4051_ == 0 {
                    lean_ctor_set(v___x_4050_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4050_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4060_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4071_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4047_,
                    );
                    v___x_4062_ = v_reuseFailAlloc_4071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4046_ == 0 {
                    lean_ctor_set(v___x_4045_, 4, v___x_4062_);
                    v___x_4064_ = v___x_4045_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_env_4036_);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_nextMacroScope_4037_);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_ngen_4038_);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 3, v_auxDeclNGen_4039_);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 4, v___x_4062_);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 5, v_cache_4040_);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 6, v_messages_4041_);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 7, v_infoState_4042_);
                    lean_ctor_set(v_reuseFailAlloc_4070_, 8, v_snapshotTasks_4043_);
                    v___x_4064_ = v_reuseFailAlloc_4070_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4065_ = lean_st_ref_set(v___y_4026_, v___x_4064_);
                v___x_4066_ = lean_box(0);
                if v_isShared_4033_ == 0 {
                    lean_ctor_set(v___x_4032_, 0, v___x_4066_);
                    v___x_4068_ = v___x_4032_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4066_);
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
    mut v_cls_4075_: *mut LeanObject,
    mut v_msg_4076_: *mut LeanObject,
    mut v___y_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
    mut v___y_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4082_: *mut LeanObject = core::ptr::null_mut();
    v_res_4082_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(
        v_cls_4075_,
        v_msg_4076_,
        v___y_4077_,
        v___y_4078_,
        v___y_4079_,
        v___y_4080_,
    );
    lean_dec(v___y_4080_);
    lean_dec_ref(v___y_4079_);
    lean_dec(v___y_4078_);
    lean_dec_ref(v___y_4077_);
    return v_res_4082_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0;
    v___x_4085_ = l_Lean_stringToMessageData(v___x_4084_);
    return v___x_4085_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(
    mut v_traceClass_4087_: *mut LeanObject,
    mut v_as_4088_: *mut LeanObject,
    mut v_sz_4089_: usize,
    mut v_i_4090_: usize,
    mut v_b_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
    mut v___y_4093_: *mut LeanObject,
    mut v___y_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v_num_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: usize = 0;
    let mut v___x_4123_: usize = 0;
    let mut v_reuseFailAlloc_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4135_: u8 = 0;
    let mut v_isSharedCheck_4136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4097_ = lean_usize_dec_lt(v_i_4090_, v_sz_4089_);
                if v___x_4097_ == 0 {
                    lean_dec(v_traceClass_4087_);
                    v___x_4098_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4098_, 0, v_b_4091_);
                    return v___x_4098_;
                } else {
                    v_a_4099_ = lean_array_uget(v_as_4088_, v_i_4090_);
                    v_snd_4100_ = lean_ctor_get(v_a_4099_, 1);
                    v_fst_4101_ = lean_ctor_get(v_a_4099_, 0);
                    v_isSharedCheck_4136_ = (!lean_is_exclusive(v_a_4099_)) as u8;
                    if v_isSharedCheck_4136_ == 0 {
                        v___x_4103_ = v_a_4099_;
                        v_isShared_4104_ = v_isSharedCheck_4136_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4100_);
                        lean_inc(v_fst_4101_);
                        lean_dec(v_a_4099_);
                        v___x_4103_ = lean_box(0);
                        v_isShared_4104_ = v_isSharedCheck_4136_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_num_4105_ = lean_ctor_get(v_snd_4100_, 0);
                v_den_4106_ = lean_ctor_get(v_snd_4100_, 1);
                v_isSharedCheck_4135_ = (!lean_is_exclusive(v_snd_4100_)) as u8;
                if v_isSharedCheck_4135_ == 0 {
                    v___x_4108_ = v_snd_4100_;
                    v_isShared_4109_ = v_isSharedCheck_4135_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_den_4106_);
                    lean_inc(v_num_4105_);
                    lean_dec(v_snd_4100_);
                    v___x_4108_ = lean_box(0);
                    v_isShared_4109_ = v_isSharedCheck_4135_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4110_ = lean_box(0);
                v___x_4111_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_4101_);
                v___x_4112_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
                if v_isShared_4109_ == 0 {
                    lean_ctor_set_tag(v___x_4108_, 7);
                    lean_ctor_set(v___x_4108_, 1, v___x_4112_);
                    lean_ctor_set(v___x_4108_, 0, v___x_4111_);
                    v___x_4114_ = v___x_4108_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4134_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4111_);
                    lean_ctor_set(v_reuseFailAlloc_4134_, 1, v___x_4112_);
                    v___x_4114_ = v_reuseFailAlloc_4134_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4126_ = lean_unsigned_to_nat(1);
                v___x_4127_ = lean_nat_dec_eq(v_den_4106_, v___x_4126_);
                if v___x_4127_ == 0 {
                    v___x_4128_ = l_Int_repr(v_num_4105_);
                    lean_dec(v_num_4105_);
                    v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2;
                    v___x_4130_ = lean_string_append(v___x_4128_, v___x_4129_);
                    v___x_4131_ = l_Nat_reprFast(v_den_4106_);
                    v___x_4132_ = lean_string_append(v___x_4130_, v___x_4131_);
                    lean_dec_ref(v___x_4131_);
                    v___y_4116_ = v___x_4132_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_den_4106_);
                    v___x_4133_ = l_Int_repr(v_num_4105_);
                    lean_dec(v_num_4105_);
                    v___y_4116_ = v___x_4133_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4117_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4117_, 0, v___y_4116_);
                v___x_4118_ = l_Lean_MessageData_ofFormat(v___x_4117_);
                if v_isShared_4104_ == 0 {
                    lean_ctor_set_tag(v___x_4103_, 7);
                    lean_ctor_set(v___x_4103_, 1, v___x_4118_);
                    lean_ctor_set(v___x_4103_, 0, v___x_4114_);
                    v___x_4120_ = v___x_4103_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4114_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 1, v___x_4118_);
                    v___x_4120_ = v_reuseFailAlloc_4125_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc(v_traceClass_4087_);
                v___x_4121_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(
                    v_traceClass_4087_,
                    v___x_4120_,
                    v___y_4092_,
                    v___y_4093_,
                    v___y_4094_,
                    v___y_4095_,
                );
                if lean_obj_tag(v___x_4121_) == 0 {
                    lean_dec_ref_known(v___x_4121_, 1);
                    v___x_4122_ = 1usize;
                    v___x_4123_ = lean_usize_add(v_i_4090_, v___x_4122_);
                    v_i_4090_ = v___x_4123_;
                    v_b_4091_ = v___x_4110_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_traceClass_4087_);
                    return v___x_4121_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(
    mut v_traceClass_4137_: *mut LeanObject,
    mut v_as_4138_: *mut LeanObject,
    mut v_sz_4139_: *mut LeanObject,
    mut v_i_4140_: *mut LeanObject,
    mut v_b_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4147_: usize = 0;
    let mut v_i_boxed_4148_: usize = 0;
    let mut v_res_4149_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4147_ = lean_unbox_usize(v_sz_4139_);
    lean_dec(v_sz_4139_);
    v_i_boxed_4148_ = lean_unbox_usize(v_i_4140_);
    lean_dec(v_i_4140_);
    v_res_4149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_4137_, v_as_4138_, v_sz_boxed_4147_, v_i_boxed_4148_, v_b_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
    lean_dec(v___y_4145_);
    lean_dec_ref(v___y_4144_);
    lean_dec(v___y_4143_);
    lean_dec_ref(v___y_4142_);
    lean_dec_ref(v_as_4138_);
    return v_res_4149_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_traceModel(
    mut v_traceClass_4153_: *mut LeanObject,
    mut v_model_4154_: *mut LeanObject,
    mut v_a_4155_: *mut LeanObject,
    mut v_a_4156_: *mut LeanObject,
    mut v_a_4157_: *mut LeanObject,
    mut v_a_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4164_: u8 = 0;
    let mut v_inheritedTraceOptions_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: u8 = 0;
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4170_: usize = 0;
    let mut v___x_4171_: usize = 0;
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4175_: u8 = 0;
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4179_: u8 = 0;
    let mut v_unused_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4163_ = lean_ctor_get(v_a_4157_, 2);
                v_hasTrace_4164_ = lean_ctor_get_uint8(
                    v_options_4163_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4164_ == 0 {
                    lean_dec(v_traceClass_4153_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_4165_ = lean_ctor_get(v_a_4157_, 13);
                    v___x_4166_ = l_Lean_Meta_Grind_Arith_traceModel___closed__1;
                    lean_inc(v_traceClass_4153_);
                    v___x_4167_ = l_Lean_Name_append(v___x_4166_, v_traceClass_4153_);
                    v___x_4168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4165_,
                        v_options_4163_,
                        v___x_4167_,
                    );
                    lean_dec(v___x_4167_);
                    if v___x_4168_ == 0 {
                        lean_dec(v_traceClass_4153_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4169_ = lean_box(0);
                        v_sz_4170_ = lean_array_size(v_model_4154_);
                        v___x_4171_ = 0usize;
                        v___x_4172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_4153_, v_model_4154_, v_sz_4170_, v___x_4171_, v___x_4169_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
                        if lean_obj_tag(v___x_4172_) == 0 {
                            v_isSharedCheck_4179_ = (!lean_is_exclusive(v___x_4172_)) as u8;
                            if v_isSharedCheck_4179_ == 0 {
                                v_unused_4180_ = lean_ctor_get(v___x_4172_, 0);
                                lean_dec(v_unused_4180_);
                                v___x_4174_ = v___x_4172_;
                                v_isShared_4175_ = v_isSharedCheck_4179_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_4172_);
                                v___x_4174_ = lean_box(0);
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
                v___x_4161_ = lean_box(0);
                v___x_4162_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4162_, 0, v___x_4161_);
                return v___x_4162_;
            }
            2 => {
                if v_isShared_4175_ == 0 {
                    lean_ctor_set(v___x_4174_, 0, v___x_4169_);
                    v___x_4177_ = v___x_4174_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4169_);
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
    mut v_traceClass_4181_: *mut LeanObject,
    mut v_model_4182_: *mut LeanObject,
    mut v_a_4183_: *mut LeanObject,
    mut v_a_4184_: *mut LeanObject,
    mut v_a_4185_: *mut LeanObject,
    mut v_a_4186_: *mut LeanObject,
    mut v_a_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4188_: *mut LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Lean_Meta_Grind_Arith_traceModel(
        v_traceClass_4181_,
        v_model_4182_,
        v_a_4183_,
        v_a_4184_,
        v_a_4185_,
        v_a_4186_,
    );
    lean_dec(v_a_4186_);
    lean_dec_ref(v_a_4185_);
    lean_dec(v_a_4184_);
    lean_dec_ref(v_a_4183_);
    lean_dec_ref(v_model_4182_);
    return v_res_4188_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Module_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
}
