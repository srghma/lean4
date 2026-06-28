// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
use crate::r#gen::Init::Data::Int::Linear::l_Int_Linear_Poly_coeff;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util, l_Int_Linear_Poly_isSorted,
    l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_instInhabitedGoalM;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_11,
    lean_apply_13, lean_apply_14, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Int_Linear_Poly_checkCoeffs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_checkCoeffs___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Int_Linear_Poly_checkNoElimVars___closed__0_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105,
            110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 73, 110, 118,
            0,
        ],
    };
static mut l_Int_Linear_Poly_checkNoElimVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_checkNoElimVars___closed__0_value) as *mut LeanObject;
pub static l_Int_Linear_Poly_checkNoElimVars___closed__1_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 80, 111, 108, 121, 46, 99, 104, 101,
            99, 107, 78, 111, 69, 108, 105, 109, 86, 97, 114, 115, 0,
        ],
    };
static mut l_Int_Linear_Poly_checkNoElimVars___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_checkNoElimVars___closed__1_value) as *mut LeanObject;
pub static l_Int_Linear_Poly_checkNoElimVars___closed__2_value: LeanStringObject<111> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 111,
        m_capacity: 111,
        m_length: 110,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 33, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76,
            101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105,
            110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 73, 110, 118,
            46, 51, 53, 53, 48, 50, 52, 49, 57, 56, 57, 46, 95, 104, 121, 103, 67, 116, 120, 46,
            95, 104, 121, 103, 46, 51, 51, 46, 48, 32, 41, 10, 32, 32, 0,
        ],
    };
static mut l_Int_Linear_Poly_checkNoElimVars___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_checkNoElimVars___closed__2_value) as *mut LeanObject;
static mut l_Int_Linear_Poly_checkNoElimVars___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_checkNoElimVars___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__0_value: LeanStringObject<80> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 80, m_capacity: 80, m_length: 79, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 73, 110, 118, 46, 48, 46, 73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 79, 99, 99, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__1_value: LeanStringObject<121> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 121, m_capacity: 121, m_length: 120, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 73, 110, 118, 46, 50, 52, 55, 53, 54, 50, 57, 57, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 54, 53, 46, 48, 32, 41, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 121, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_Poly_checkCnstrOf___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            73, 110, 116, 46, 76, 105, 110, 101, 97, 114, 46, 80, 111, 108, 121, 46, 99, 104, 101,
            99, 107, 67, 110, 115, 116, 114, 79, 102, 0,
        ],
    };
static mut l_Int_Linear_Poly_checkCnstrOf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_checkCnstrOf___closed__0_value) as *mut LeanObject;
pub static l_Int_Linear_Poly_checkCnstrOf___closed__1_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 120, 32, 61, 61, 32, 121, 10, 10, 0,
        ],
    };
static mut l_Int_Linear_Poly_checkCnstrOf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_checkCnstrOf___closed__1_value) as *mut LeanObject;
static mut l_Int_Linear_Poly_checkCnstrOf___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_checkCnstrOf___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_Poly_checkCnstrOf___closed__3_value: LeanStringObject<34> =
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
static mut l_Int_Linear_Poly_checkCnstrOf___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_checkCnstrOf___closed__3_value) as *mut LeanObject;
static mut l_Int_Linear_Poly_checkCnstrOf___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_checkCnstrOf___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_Poly_checkCnstrOf___closed__5_value: LeanStringObject<35> =
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
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 112, 46, 105, 115, 83, 111, 114, 116, 101, 100, 10, 32, 32, 0,
        ],
    };
static mut l_Int_Linear_Poly_checkCnstrOf___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_checkCnstrOf___closed__5_value) as *mut LeanObject;
static mut l_Int_Linear_Poly_checkCnstrOf___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_checkCnstrOf___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_Poly_checkCnstrOf___closed__7_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 112, 46, 99, 104, 101, 99, 107, 67, 111, 101, 102, 102, 115, 10, 32, 32,
            0,
        ],
    };
static mut l_Int_Linear_Poly_checkCnstrOf___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_checkCnstrOf___closed__7_value) as *mut LeanObject;
static mut l_Int_Linear_Poly_checkCnstrOf___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_Linear_Poly_checkCnstrOf___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 99, 104, 101, 99, 107, 76, 101, 67, 110, 115, 116, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 76, 111, 119, 101, 114, 32, 61, 61, 32, 40, 97, 32, 60, 32, 48, 41, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105,
            116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 99, 104, 101, 99, 107, 76, 111, 119, 101,
            114, 115, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1_value: LeanStringObject<53> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 115, 46, 108, 111, 119, 101, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61,
            32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105,
            116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 99, 104, 101, 99, 107, 85, 112, 112, 101,
            114, 115, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1_value: LeanStringObject<53> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 115, 46, 117, 112, 112, 101, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61,
            32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 99, 104, 101, 99, 107, 68, 118, 100, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 99, 46, 100, 32, 62, 32, 49, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0_value: LeanStringObject<51> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115,
            46, 100, 118, 100, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0_value: LeanStringObject<
    39,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116,
        104, 46, 67, 117, 116, 115, 97, 116, 46, 99, 104, 101, 99, 107, 86, 97, 114, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2_value: LeanStringObject<
    48,
> = LeanStringObject {
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
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 120, 112, 114, 32, 101,
        120, 112, 114, 39, 10, 32, 32, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 110,
            117, 109, 10, 10, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 99, 104, 101, 99, 107, 69, 108, 105, 109, 69, 113, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 99, 46, 112, 46, 99, 111, 101, 102, 102, 32, 120, 32, 33, 61, 32, 48, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 99, 46, 112, 46, 105, 115, 83, 111, 114, 116, 101, 100, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 99, 46, 112, 46, 99, 104, 101, 99, 107, 67, 111, 101, 102, 102, 115, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7_value: LeanStringObject<51> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 101, 108, 105, 109, 83, 116, 97, 99, 107, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 120, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0_value: LeanStringObject<54> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 54,
        m_capacity: 54,
        m_length: 53,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 115, 46, 101, 108, 105, 109, 69, 113, 115, 46, 115, 105, 122, 101, 32, 61,
            61, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 99, 104, 101, 99, 107, 69, 108, 105, 109, 83, 116, 97, 99, 107, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1_value: LeanStringObject<108> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 108, m_capacity: 108, m_length: 107, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 73, 110, 118, 46, 49, 48, 57, 53, 50, 53, 57, 55, 52, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 50, 54, 46, 48, 32, 41, 10, 10, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0_value: LeanStringObject<46> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 46,
        m_capacity: 46,
        m_length: 45,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105,
            116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 99, 104, 101, 99, 107, 68, 105, 115, 101,
            113, 67, 110, 115, 116, 114, 115, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1_value: LeanStringObject<53> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115,
            46, 100, 105, 115, 101, 113, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Int_Linear_Poly_checkCoeffs___closed__0() -> *mut LeanObject {
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    v___x_4963_ = lean_unsigned_to_nat(0);
    v___x_4964_ = lean_nat_to_int(v___x_4963_);
    return v___x_4964_;
}
pub unsafe fn l_Int_Linear_Poly_checkCoeffs(mut v_x_4965_: *mut LeanObject) -> u8 {
    let mut v___x_4966_: u8 = 0;
    let mut v_k_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: u8 = 0;
    let mut v___x_4972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4965_) == 0 {
                    v___x_4966_ = 1;
                    return v___x_4966_;
                } else {
                    v_k_4967_ = lean_ctor_get(v_x_4965_, 0);
                    v_p_4968_ = lean_ctor_get(v_x_4965_, 2);
                    v___x_4969_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0),
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0_once),
                        _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                    );
                    v___x_4970_ = lean_int_dec_eq(v_k_4967_, v___x_4969_);
                    if v___x_4970_ == 0 {
                        v_x_4965_ = v_p_4968_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4972_ = 0;
                        return v___x_4972_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_checkCoeffs___boxed(
    mut v_x_4973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4974_: u8 = 0;
    let mut v_r_4975_: *mut LeanObject = core::ptr::null_mut();
    v_res_4974_ = l_Int_Linear_Poly_checkCoeffs(v_x_4973_);
    lean_dec_ref(v_x_4973_);
    v_r_4975_ = lean_box((v_res_4974_) as usize);
    return v_r_4975_;
}
pub unsafe fn _init_l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    v___x_4976_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_4976_;
}
pub unsafe fn l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
    mut v_msg_4977_: *mut LeanObject,
    mut v___y_4978_: *mut LeanObject,
    mut v___y_4979_: *mut LeanObject,
    mut v___y_4980_: *mut LeanObject,
    mut v___y_4981_: *mut LeanObject,
    mut v___y_4982_: *mut LeanObject,
    mut v___y_4983_: *mut LeanObject,
    mut v___y_4984_: *mut LeanObject,
    mut v___y_4985_: *mut LeanObject,
    mut v___y_4986_: *mut LeanObject,
    mut v___y_4987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598__overap_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    v___x_4989_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___closed__0,
    );
    v___x_1598__overap_4990_ = lean_panic_fn_borrowed(v___x_4989_, v_msg_4977_);
    lean_inc(v___y_4987_);
    lean_inc_ref(v___y_4986_);
    lean_inc(v___y_4985_);
    lean_inc_ref(v___y_4984_);
    lean_inc(v___y_4983_);
    lean_inc_ref(v___y_4982_);
    lean_inc(v___y_4981_);
    lean_inc_ref(v___y_4980_);
    lean_inc(v___y_4979_);
    lean_inc(v___y_4978_);
    v___x_4991_ = lean_apply_11(
        v___x_1598__overap_4990_,
        v___y_4978_,
        v___y_4979_,
        v___y_4980_,
        v___y_4981_,
        v___y_4982_,
        v___y_4983_,
        v___y_4984_,
        v___y_4985_,
        v___y_4986_,
        v___y_4987_,
        lean_box(0),
    );
    return v___x_4991_;
}
pub unsafe fn l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0___boxed(
    mut v_msg_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
    mut v___y_4994_: *mut LeanObject,
    mut v___y_4995_: *mut LeanObject,
    mut v___y_4996_: *mut LeanObject,
    mut v___y_4997_: *mut LeanObject,
    mut v___y_4998_: *mut LeanObject,
    mut v___y_4999_: *mut LeanObject,
    mut v___y_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
    mut v___y_5003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5004_: *mut LeanObject = core::ptr::null_mut();
    v_res_5004_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
        v_msg_4992_,
        v___y_4993_,
        v___y_4994_,
        v___y_4995_,
        v___y_4996_,
        v___y_4997_,
        v___y_4998_,
        v___y_4999_,
        v___y_5000_,
        v___y_5001_,
        v___y_5002_,
    );
    lean_dec(v___y_5002_);
    lean_dec_ref(v___y_5001_);
    lean_dec(v___y_5000_);
    lean_dec_ref(v___y_4999_);
    lean_dec(v___y_4998_);
    lean_dec_ref(v___y_4997_);
    lean_dec(v___y_4996_);
    lean_dec_ref(v___y_4995_);
    lean_dec(v___y_4994_);
    lean_dec(v___y_4993_);
    return v_res_5004_;
}
pub unsafe fn _init_l_Int_Linear_Poly_checkNoElimVars___closed__3() -> *mut LeanObject {
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    v___x_5008_ = l_Int_Linear_Poly_checkNoElimVars___closed__2;
    v___x_5009_ = lean_unsigned_to_nat(2);
    v___x_5010_ = lean_unsigned_to_nat(23);
    v___x_5011_ = l_Int_Linear_Poly_checkNoElimVars___closed__1;
    v___x_5012_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_5013_ = l_mkPanicMessageWithDecl(
        v___x_5012_,
        v___x_5011_,
        v___x_5010_,
        v___x_5009_,
        v___x_5008_,
    );
    return v___x_5013_;
}
pub unsafe fn l_Int_Linear_Poly_checkNoElimVars(
    mut v_p_5014_: *mut LeanObject,
    mut v_a_5015_: *mut LeanObject,
    mut v_a_5016_: *mut LeanObject,
    mut v_a_5017_: *mut LeanObject,
    mut v_a_5018_: *mut LeanObject,
    mut v_a_5019_: *mut LeanObject,
    mut v_a_5020_: *mut LeanObject,
    mut v_a_5021_: *mut LeanObject,
    mut v_a_5022_: *mut LeanObject,
    mut v_a_5023_: *mut LeanObject,
    mut v_a_5024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: u8 = 0;
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5037_: u8 = 0;
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5041_: u8 = 0;
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_5014_) == 1 {
                    v_v_5026_ = lean_ctor_get(v_p_5014_, 1);
                    v_p_5027_ = lean_ctor_get(v_p_5014_, 2);
                    v___x_5028_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(
                        v_v_5026_, v_a_5015_, v_a_5023_,
                    );
                    if lean_obj_tag(v___x_5028_) == 0 {
                        v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
                        lean_inc(v_a_5029_);
                        lean_dec_ref_known(v___x_5028_, 1);
                        v___x_5030_ = (lean_unbox(v_a_5029_) as u8);
                        lean_dec(v_a_5029_);
                        if v___x_5030_ == 0 {
                            v_p_5014_ = v_p_5027_;
                            state = 0;
                            continue;
                        } else {
                            v___x_5032_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Int_Linear_Poly_checkNoElimVars___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Int_Linear_Poly_checkNoElimVars___closed__3_once
                                ),
                                _init_l_Int_Linear_Poly_checkNoElimVars___closed__3,
                            );
                            v___x_5033_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                                v___x_5032_,
                                v_a_5015_,
                                v_a_5016_,
                                v_a_5017_,
                                v_a_5018_,
                                v_a_5019_,
                                v_a_5020_,
                                v_a_5021_,
                                v_a_5022_,
                                v_a_5023_,
                                v_a_5024_,
                            );
                            return v___x_5033_;
                        }
                    } else {
                        v_a_5034_ = lean_ctor_get(v___x_5028_, 0);
                        v_isSharedCheck_5041_ = (!lean_is_exclusive(v___x_5028_)) as u8;
                        if v_isSharedCheck_5041_ == 0 {
                            v___x_5036_ = v___x_5028_;
                            v_isShared_5037_ = v_isSharedCheck_5041_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5034_);
                            lean_dec(v___x_5028_);
                            v___x_5036_ = lean_box(0);
                            v_isShared_5037_ = v_isSharedCheck_5041_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_5042_ = lean_box(0);
                    v___x_5043_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5043_, 0, v___x_5042_);
                    return v___x_5043_;
                }
            }
            1 => {
                if v_isShared_5037_ == 0 {
                    v___x_5039_ = v___x_5036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
                    v___x_5039_ = v_reuseFailAlloc_5040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_checkNoElimVars___boxed(
    mut v_p_5044_: *mut LeanObject,
    mut v_a_5045_: *mut LeanObject,
    mut v_a_5046_: *mut LeanObject,
    mut v_a_5047_: *mut LeanObject,
    mut v_a_5048_: *mut LeanObject,
    mut v_a_5049_: *mut LeanObject,
    mut v_a_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
    mut v_a_5052_: *mut LeanObject,
    mut v_a_5053_: *mut LeanObject,
    mut v_a_5054_: *mut LeanObject,
    mut v_a_5055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5056_: *mut LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Int_Linear_Poly_checkNoElimVars(
        v_p_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_,
        v_a_5052_, v_a_5053_, v_a_5054_,
    );
    lean_dec(v_a_5054_);
    lean_dec_ref(v_a_5053_);
    lean_dec(v_a_5052_);
    lean_dec_ref(v_a_5051_);
    lean_dec(v_a_5050_);
    lean_dec_ref(v_a_5049_);
    lean_dec(v_a_5048_);
    lean_dec_ref(v_a_5047_);
    lean_dec(v_a_5046_);
    lean_dec(v_a_5045_);
    lean_dec_ref(v_p_5044_);
    return v_res_5056_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(
    mut v_k_5057_: *mut LeanObject,
    mut v_t_5058_: *mut LeanObject,
) -> u8 {
    let mut v_k_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: u8 = 0;
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_5058_) == 0 {
                    v_k_5059_ = lean_ctor_get(v_t_5058_, 1);
                    v_l_5060_ = lean_ctor_get(v_t_5058_, 3);
                    v_r_5061_ = lean_ctor_get(v_t_5058_, 4);
                    v___x_5062_ = lean_nat_dec_lt(v_k_5057_, v_k_5059_);
                    if v___x_5062_ == 0 {
                        v___x_5063_ = lean_nat_dec_eq(v_k_5057_, v_k_5059_);
                        if v___x_5063_ == 0 {
                            v_t_5058_ = v_r_5061_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_5063_;
                        }
                    } else {
                        v_t_5058_ = v_l_5060_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_5066_ = 0;
                    return v___x_5066_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg___boxed(
    mut v_k_5067_: *mut LeanObject,
    mut v_t_5068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5069_: u8 = 0;
    let mut v_r_5070_: *mut LeanObject = core::ptr::null_mut();
    v_res_5069_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_5067_, v_t_5068_);
    lean_dec(v_t_5068_);
    lean_dec(v_k_5067_);
    v_r_5070_ = lean_box((v_res_5069_) as usize);
    return v_r_5070_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2()
-> *mut LeanObject {
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    v___x_5073_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__1;
    v___x_5074_ = lean_unsigned_to_nat(4);
    v___x_5075_ = lean_unsigned_to_nat(30);
    v___x_5076_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__0;
    v___x_5077_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_5078_ = l_mkPanicMessageWithDecl(
        v___x_5077_,
        v___x_5076_,
        v___x_5075_,
        v___x_5074_,
        v___x_5073_,
    );
    return v___x_5078_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go(
    mut v_y_5079_: *mut LeanObject,
    mut v_p_5080_: *mut LeanObject,
    mut v_a_5081_: *mut LeanObject,
    mut v_a_5082_: *mut LeanObject,
    mut v_a_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_a_5088_: *mut LeanObject,
    mut v_a_5089_: *mut LeanObject,
    mut v_a_5090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: u8 = 0;
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_5080_) == 1 {
                    v_v_5092_ = lean_ctor_get(v_p_5080_, 1);
                    v_p_5093_ = lean_ctor_get(v_p_5080_, 2);
                    v___x_5094_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(
                        v_v_5092_, v_a_5081_, v_a_5089_,
                    );
                    if lean_obj_tag(v___x_5094_) == 0 {
                        v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
                        lean_inc(v_a_5095_);
                        lean_dec_ref_known(v___x_5094_, 1);
                        v___x_5096_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(v_y_5079_, v_a_5095_);
                        lean_dec(v_a_5095_);
                        if v___x_5096_ == 0 {
                            v___x_5097_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___closed__2);
                            v___x_5098_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                                v___x_5097_,
                                v_a_5081_,
                                v_a_5082_,
                                v_a_5083_,
                                v_a_5084_,
                                v_a_5085_,
                                v_a_5086_,
                                v_a_5087_,
                                v_a_5088_,
                                v_a_5089_,
                                v_a_5090_,
                            );
                            return v___x_5098_;
                        } else {
                            v_p_5080_ = v_p_5093_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_a_5100_ = lean_ctor_get(v___x_5094_, 0);
                        v_isSharedCheck_5107_ = (!lean_is_exclusive(v___x_5094_)) as u8;
                        if v_isSharedCheck_5107_ == 0 {
                            v___x_5102_ = v___x_5094_;
                            v_isShared_5103_ = v_isSharedCheck_5107_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5100_);
                            lean_dec(v___x_5094_);
                            v___x_5102_ = lean_box(0);
                            v_isShared_5103_ = v_isSharedCheck_5107_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_5108_ = lean_box(0);
                    v___x_5109_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5109_, 0, v___x_5108_);
                    return v___x_5109_;
                }
            }
            1 => {
                if v_isShared_5103_ == 0 {
                    v___x_5105_ = v___x_5102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go___boxed(
    mut v_y_5110_: *mut LeanObject,
    mut v_p_5111_: *mut LeanObject,
    mut v_a_5112_: *mut LeanObject,
    mut v_a_5113_: *mut LeanObject,
    mut v_a_5114_: *mut LeanObject,
    mut v_a_5115_: *mut LeanObject,
    mut v_a_5116_: *mut LeanObject,
    mut v_a_5117_: *mut LeanObject,
    mut v_a_5118_: *mut LeanObject,
    mut v_a_5119_: *mut LeanObject,
    mut v_a_5120_: *mut LeanObject,
    mut v_a_5121_: *mut LeanObject,
    mut v_a_5122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5123_: *mut LeanObject = core::ptr::null_mut();
    v_res_5123_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go(
            v_y_5110_, v_p_5111_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_,
            v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_,
        );
    lean_dec(v_a_5121_);
    lean_dec_ref(v_a_5120_);
    lean_dec(v_a_5119_);
    lean_dec_ref(v_a_5118_);
    lean_dec(v_a_5117_);
    lean_dec_ref(v_a_5116_);
    lean_dec(v_a_5115_);
    lean_dec_ref(v_a_5114_);
    lean_dec(v_a_5113_);
    lean_dec(v_a_5112_);
    lean_dec_ref(v_p_5111_);
    lean_dec(v_y_5110_);
    return v_res_5123_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0(
    mut v_00_u03b2_5124_: *mut LeanObject,
    mut v_k_5125_: *mut LeanObject,
    mut v_t_5126_: *mut LeanObject,
) -> u8 {
    let mut v___x_5127_: u8 = 0;
    v___x_5127_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___redArg(v_k_5125_, v_t_5126_);
    return v___x_5127_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0___boxed(
    mut v_00_u03b2_5128_: *mut LeanObject,
    mut v_k_5129_: *mut LeanObject,
    mut v_t_5130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5131_: u8 = 0;
    let mut v_r_5132_: *mut LeanObject = core::ptr::null_mut();
    v_res_5131_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go_spec__0(v_00_u03b2_5128_, v_k_5129_, v_t_5130_);
    lean_dec(v_t_5130_);
    lean_dec(v_k_5129_);
    v_r_5132_ = lean_box((v_res_5131_) as usize);
    return v_r_5132_;
}
pub unsafe fn l_Int_Linear_Poly_checkOccs(
    mut v_p_5133_: *mut LeanObject,
    mut v_a_5134_: *mut LeanObject,
    mut v_a_5135_: *mut LeanObject,
    mut v_a_5136_: *mut LeanObject,
    mut v_a_5137_: *mut LeanObject,
    mut v_a_5138_: *mut LeanObject,
    mut v_a_5139_: *mut LeanObject,
    mut v_a_5140_: *mut LeanObject,
    mut v_a_5141_: *mut LeanObject,
    mut v_a_5142_: *mut LeanObject,
    mut v_a_5143_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_5133_) == 1 {
        let mut v_v_5145_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_5146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
        v_v_5145_ = lean_ctor_get(v_p_5133_, 1);
        v_p_5146_ = lean_ctor_get(v_p_5133_, 2);
        v___x_5147_ =
            l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv_0__Int_Linear_Poly_checkOccs_go(
                v_v_5145_, v_p_5146_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_,
                v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_,
            );
        return v___x_5147_;
    } else {
        let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
        v___x_5148_ = lean_box(0);
        v___x_5149_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5149_, 0, v___x_5148_);
        return v___x_5149_;
    }
}
pub unsafe fn l_Int_Linear_Poly_checkOccs___boxed(
    mut v_p_5150_: *mut LeanObject,
    mut v_a_5151_: *mut LeanObject,
    mut v_a_5152_: *mut LeanObject,
    mut v_a_5153_: *mut LeanObject,
    mut v_a_5154_: *mut LeanObject,
    mut v_a_5155_: *mut LeanObject,
    mut v_a_5156_: *mut LeanObject,
    mut v_a_5157_: *mut LeanObject,
    mut v_a_5158_: *mut LeanObject,
    mut v_a_5159_: *mut LeanObject,
    mut v_a_5160_: *mut LeanObject,
    mut v_a_5161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5162_: *mut LeanObject = core::ptr::null_mut();
    v_res_5162_ = l_Int_Linear_Poly_checkOccs(
        v_p_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_,
        v_a_5158_, v_a_5159_, v_a_5160_,
    );
    lean_dec(v_a_5160_);
    lean_dec_ref(v_a_5159_);
    lean_dec(v_a_5158_);
    lean_dec_ref(v_a_5157_);
    lean_dec(v_a_5156_);
    lean_dec_ref(v_a_5155_);
    lean_dec(v_a_5154_);
    lean_dec_ref(v_a_5153_);
    lean_dec(v_a_5152_);
    lean_dec(v_a_5151_);
    lean_dec_ref(v_p_5150_);
    return v_res_5162_;
}
pub unsafe fn _init_l_Int_Linear_Poly_checkCnstrOf___closed__2() -> *mut LeanObject {
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    v___x_5165_ = l_Int_Linear_Poly_checkCnstrOf___closed__1;
    v___x_5166_ = lean_unsigned_to_nat(2);
    v___x_5167_ = lean_unsigned_to_nat(41);
    v___x_5168_ = l_Int_Linear_Poly_checkCnstrOf___closed__0;
    v___x_5169_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_5170_ = l_mkPanicMessageWithDecl(
        v___x_5169_,
        v___x_5168_,
        v___x_5167_,
        v___x_5166_,
        v___x_5165_,
    );
    return v___x_5170_;
}
pub unsafe fn _init_l_Int_Linear_Poly_checkCnstrOf___closed__4() -> *mut LeanObject {
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    v___x_5172_ = l_Int_Linear_Poly_checkCnstrOf___closed__3;
    v___x_5173_ = lean_unsigned_to_nat(24);
    v___x_5174_ = lean_unsigned_to_nat(40);
    v___x_5175_ = l_Int_Linear_Poly_checkCnstrOf___closed__0;
    v___x_5176_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_5177_ = l_mkPanicMessageWithDecl(
        v___x_5176_,
        v___x_5175_,
        v___x_5174_,
        v___x_5173_,
        v___x_5172_,
    );
    return v___x_5177_;
}
pub unsafe fn _init_l_Int_Linear_Poly_checkCnstrOf___closed__6() -> *mut LeanObject {
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    v___x_5179_ = l_Int_Linear_Poly_checkCnstrOf___closed__5;
    v___x_5180_ = lean_unsigned_to_nat(2);
    v___x_5181_ = lean_unsigned_to_nat(35);
    v___x_5182_ = l_Int_Linear_Poly_checkCnstrOf___closed__0;
    v___x_5183_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_5184_ = l_mkPanicMessageWithDecl(
        v___x_5183_,
        v___x_5182_,
        v___x_5181_,
        v___x_5180_,
        v___x_5179_,
    );
    return v___x_5184_;
}
pub unsafe fn _init_l_Int_Linear_Poly_checkCnstrOf___closed__8() -> *mut LeanObject {
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    v___x_5186_ = l_Int_Linear_Poly_checkCnstrOf___closed__7;
    v___x_5187_ = lean_unsigned_to_nat(2);
    v___x_5188_ = lean_unsigned_to_nat(36);
    v___x_5189_ = l_Int_Linear_Poly_checkCnstrOf___closed__0;
    v___x_5190_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_5191_ = l_mkPanicMessageWithDecl(
        v___x_5190_,
        v___x_5189_,
        v___x_5188_,
        v___x_5187_,
        v___x_5186_,
    );
    return v___x_5191_;
}
pub unsafe fn l_Int_Linear_Poly_checkCnstrOf(
    mut v_p_5192_: *mut LeanObject,
    mut v_x_5193_: *mut LeanObject,
    mut v_a_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
    mut v_a_5196_: *mut LeanObject,
    mut v_a_5197_: *mut LeanObject,
    mut v_a_5198_: *mut LeanObject,
    mut v_a_5199_: *mut LeanObject,
    mut v_a_5200_: *mut LeanObject,
    mut v_a_5201_: *mut LeanObject,
    mut v_a_5202_: *mut LeanObject,
    mut v_a_5203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: u8 = 0;
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: u8 = 0;
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5224_ = l_Int_Linear_Poly_isSorted(v_p_5192_);
                if v___x_5224_ == 0 {
                    v___x_5225_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCnstrOf___closed__6),
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCnstrOf___closed__6_once),
                        _init_l_Int_Linear_Poly_checkCnstrOf___closed__6,
                    );
                    v___x_5226_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                        v___x_5225_,
                        v_a_5194_,
                        v_a_5195_,
                        v_a_5196_,
                        v_a_5197_,
                        v_a_5198_,
                        v_a_5199_,
                        v_a_5200_,
                        v_a_5201_,
                        v_a_5202_,
                        v_a_5203_,
                    );
                    return v___x_5226_;
                } else {
                    v___x_5227_ = l_Int_Linear_Poly_checkCoeffs(v_p_5192_);
                    if v___x_5227_ == 0 {
                        v___x_5228_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCnstrOf___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Int_Linear_Poly_checkCnstrOf___closed__8_once
                            ),
                            _init_l_Int_Linear_Poly_checkCnstrOf___closed__8,
                        );
                        v___x_5229_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_5228_,
                            v_a_5194_,
                            v_a_5195_,
                            v_a_5196_,
                            v_a_5197_,
                            v_a_5198_,
                            v_a_5199_,
                            v_a_5200_,
                            v_a_5201_,
                            v_a_5202_,
                            v_a_5203_,
                        );
                        return v___x_5229_;
                    } else {
                        v___x_5230_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(
                            v_a_5194_, v_a_5202_,
                        );
                        if lean_obj_tag(v___x_5230_) == 0 {
                            v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
                            lean_inc(v_a_5231_);
                            lean_dec_ref_known(v___x_5230_, 1);
                            v___x_5232_ = (lean_unbox(v_a_5231_) as u8);
                            lean_dec(v_a_5231_);
                            if v___x_5232_ == 0 {
                                v___x_5233_ = l_Int_Linear_Poly_checkNoElimVars(
                                    v_p_5192_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_,
                                    v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_,
                                    v_a_5203_,
                                );
                                if lean_obj_tag(v___x_5233_) == 0 {
                                    lean_dec_ref_known(v___x_5233_, 1);
                                    v___x_5234_ = l_Int_Linear_Poly_checkOccs(
                                        v_p_5192_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_,
                                        v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_,
                                        v_a_5203_,
                                    );
                                    if lean_obj_tag(v___x_5234_) == 0 {
                                        lean_dec_ref_known(v___x_5234_, 1);
                                        v___y_5206_ = v_a_5194_;
                                        v___y_5207_ = v_a_5195_;
                                        v___y_5208_ = v_a_5196_;
                                        v___y_5209_ = v_a_5197_;
                                        v___y_5210_ = v_a_5198_;
                                        v___y_5211_ = v_a_5199_;
                                        v___y_5212_ = v_a_5200_;
                                        v___y_5213_ = v_a_5201_;
                                        v___y_5214_ = v_a_5202_;
                                        v___y_5215_ = v_a_5203_;
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_5234_;
                                    }
                                } else {
                                    return v___x_5233_;
                                }
                            } else {
                                v___y_5206_ = v_a_5194_;
                                v___y_5207_ = v_a_5195_;
                                v___y_5208_ = v_a_5196_;
                                v___y_5209_ = v_a_5197_;
                                v___y_5210_ = v_a_5198_;
                                v___y_5211_ = v_a_5199_;
                                v___y_5212_ = v_a_5200_;
                                v___y_5213_ = v_a_5201_;
                                v___y_5214_ = v_a_5202_;
                                v___y_5215_ = v_a_5203_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_5235_ = lean_ctor_get(v___x_5230_, 0);
                            v_isSharedCheck_5242_ = (!lean_is_exclusive(v___x_5230_)) as u8;
                            if v_isSharedCheck_5242_ == 0 {
                                v___x_5237_ = v___x_5230_;
                                v_isShared_5238_ = v_isSharedCheck_5242_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_5235_);
                                lean_dec(v___x_5230_);
                                v___x_5237_ = lean_box(0);
                                v_isShared_5238_ = v_isSharedCheck_5242_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_p_5192_) == 1 {
                    v_v_5216_ = lean_ctor_get(v_p_5192_, 1);
                    v___x_5217_ = lean_nat_dec_eq(v_x_5193_, v_v_5216_);
                    if v___x_5217_ == 0 {
                        v___x_5218_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCnstrOf___closed__2),
                            core::ptr::addr_of_mut!(
                                l_Int_Linear_Poly_checkCnstrOf___closed__2_once
                            ),
                            _init_l_Int_Linear_Poly_checkCnstrOf___closed__2,
                        );
                        v___x_5219_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_5218_,
                            v___y_5206_,
                            v___y_5207_,
                            v___y_5208_,
                            v___y_5209_,
                            v___y_5210_,
                            v___y_5211_,
                            v___y_5212_,
                            v___y_5213_,
                            v___y_5214_,
                            v___y_5215_,
                        );
                        return v___x_5219_;
                    } else {
                        v___x_5220_ = lean_box(0);
                        v___x_5221_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5221_, 0, v___x_5220_);
                        return v___x_5221_;
                    }
                } else {
                    v___x_5222_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCnstrOf___closed__4),
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCnstrOf___closed__4_once),
                        _init_l_Int_Linear_Poly_checkCnstrOf___closed__4,
                    );
                    v___x_5223_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                        v___x_5222_,
                        v___y_5206_,
                        v___y_5207_,
                        v___y_5208_,
                        v___y_5209_,
                        v___y_5210_,
                        v___y_5211_,
                        v___y_5212_,
                        v___y_5213_,
                        v___y_5214_,
                        v___y_5215_,
                    );
                    return v___x_5223_;
                }
            }
            2 => {
                if v_isShared_5238_ == 0 {
                    v___x_5240_ = v___x_5237_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
                    v___x_5240_ = v_reuseFailAlloc_5241_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_checkCnstrOf___boxed(
    mut v_p_5243_: *mut LeanObject,
    mut v_x_5244_: *mut LeanObject,
    mut v_a_5245_: *mut LeanObject,
    mut v_a_5246_: *mut LeanObject,
    mut v_a_5247_: *mut LeanObject,
    mut v_a_5248_: *mut LeanObject,
    mut v_a_5249_: *mut LeanObject,
    mut v_a_5250_: *mut LeanObject,
    mut v_a_5251_: *mut LeanObject,
    mut v_a_5252_: *mut LeanObject,
    mut v_a_5253_: *mut LeanObject,
    mut v_a_5254_: *mut LeanObject,
    mut v_a_5255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5256_: *mut LeanObject = core::ptr::null_mut();
    v_res_5256_ = l_Int_Linear_Poly_checkCnstrOf(
        v_p_5243_, v_x_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_,
        v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_,
    );
    lean_dec(v_a_5254_);
    lean_dec_ref(v_a_5253_);
    lean_dec(v_a_5252_);
    lean_dec_ref(v_a_5251_);
    lean_dec(v_a_5250_);
    lean_dec_ref(v_a_5249_);
    lean_dec(v_a_5248_);
    lean_dec_ref(v_a_5247_);
    lean_dec(v_a_5246_);
    lean_dec(v_a_5245_);
    lean_dec(v_x_5244_);
    lean_dec_ref(v_p_5243_);
    return v_res_5256_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    v___x_5257_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_5257_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(
    mut v_msg_5258_: *mut LeanObject,
    mut v___y_5259_: *mut LeanObject,
    mut v___y_5260_: *mut LeanObject,
    mut v___y_5261_: *mut LeanObject,
    mut v___y_5262_: *mut LeanObject,
    mut v___y_5263_: *mut LeanObject,
    mut v___y_5264_: *mut LeanObject,
    mut v___y_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991__overap_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    v___x_5270_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___closed__0,
    );
    v___x_3991__overap_5271_ = lean_panic_fn_borrowed(v___x_5270_, v_msg_5258_);
    lean_inc(v___y_5268_);
    lean_inc_ref(v___y_5267_);
    lean_inc(v___y_5266_);
    lean_inc_ref(v___y_5265_);
    lean_inc(v___y_5264_);
    lean_inc_ref(v___y_5263_);
    lean_inc(v___y_5262_);
    lean_inc_ref(v___y_5261_);
    lean_inc(v___y_5260_);
    lean_inc(v___y_5259_);
    v___x_5272_ = lean_apply_11(
        v___x_3991__overap_5271_,
        v___y_5259_,
        v___y_5260_,
        v___y_5261_,
        v___y_5262_,
        v___y_5263_,
        v___y_5264_,
        v___y_5265_,
        v___y_5266_,
        v___y_5267_,
        v___y_5268_,
        lean_box(0),
    );
    return v___x_5272_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0___boxed(
    mut v_msg_5273_: *mut LeanObject,
    mut v___y_5274_: *mut LeanObject,
    mut v___y_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
    mut v___y_5284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5285_: *mut LeanObject = core::ptr::null_mut();
    v_res_5285_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(
        v_msg_5273_,
        v___y_5274_,
        v___y_5275_,
        v___y_5276_,
        v___y_5277_,
        v___y_5278_,
        v___y_5279_,
        v___y_5280_,
        v___y_5281_,
        v___y_5282_,
        v___y_5283_,
    );
    lean_dec(v___y_5283_);
    lean_dec_ref(v___y_5282_);
    lean_dec(v___y_5281_);
    lean_dec_ref(v___y_5280_);
    lean_dec(v___y_5279_);
    lean_dec_ref(v___y_5278_);
    lean_dec(v___y_5277_);
    lean_dec_ref(v___y_5276_);
    lean_dec(v___y_5275_);
    lean_dec(v___y_5274_);
    return v_res_5285_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2()
-> *mut LeanObject {
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    v___x_5288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__1;
    v___x_5289_ = lean_unsigned_to_nat(6);
    v___x_5290_ = lean_unsigned_to_nat(49);
    v___x_5291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0;
    v___x_5292_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_5293_ = l_mkPanicMessageWithDecl(
        v___x_5292_,
        v___x_5291_,
        v___x_5290_,
        v___x_5289_,
        v___x_5288_,
    );
    return v___x_5293_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    v___x_5294_ = l_Int_Linear_Poly_checkCnstrOf___closed__3;
    v___x_5295_ = lean_unsigned_to_nat(30);
    v___x_5296_ = lean_unsigned_to_nat(48);
    v___x_5297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__0;
    v___x_5298_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_5299_ = l_mkPanicMessageWithDecl(
        v___x_5298_,
        v___x_5297_,
        v___x_5296_,
        v___x_5295_,
        v___x_5294_,
    );
    return v___x_5299_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(
    mut v_____s_5300_: *mut LeanObject,
    mut v_isLower_5301_: u8,
    mut v_as_5302_: *mut LeanObject,
    mut v_sz_5303_: usize,
    mut v_i_5304_: usize,
    mut v_b_5305_: *mut LeanObject,
    mut v___y_5306_: *mut LeanObject,
    mut v___y_5307_: *mut LeanObject,
    mut v___y_5308_: *mut LeanObject,
    mut v___y_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5317_: u8 = 0;
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v_a_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5327_: u8 = 0;
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: usize = 0;
    let mut v___x_5335_: usize = 0;
    let mut v_reuseFailAlloc_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5344_: u8 = 0;
    let mut v_a_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5348_: u8 = 0;
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5358_: u8 = 0;
    let mut v_a_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut v_a_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5371_: u8 = 0;
    let mut v_k_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: u8 = 0;
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5384_: u8 = 0;
    let mut v_a_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5388_: u8 = 0;
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5392_: u8 = 0;
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut v_unused_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5395_: u8 = 0;
    let mut v_unused_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5317_ = lean_usize_dec_lt(v_i_5304_, v_sz_5303_);
                if v___x_5317_ == 0 {
                    v___x_5318_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5318_, 0, v_b_5305_);
                    return v___x_5318_;
                } else {
                    v_snd_5319_ = lean_ctor_get(v_b_5305_, 1);
                    v_isSharedCheck_5395_ = (!lean_is_exclusive(v_b_5305_)) as u8;
                    if v_isSharedCheck_5395_ == 0 {
                        v_unused_5396_ = lean_ctor_get(v_b_5305_, 0);
                        lean_dec(v_unused_5396_);
                        v___x_5321_ = v_b_5305_;
                        v_isShared_5322_ = v_isSharedCheck_5395_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5319_);
                        lean_dec(v_b_5305_);
                        v___x_5321_ = lean_box(0);
                        v_isShared_5322_ = v_isSharedCheck_5395_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5323_ = lean_array_uget(v_as_5302_, v_i_5304_);
                v_p_5324_ = lean_ctor_get(v_a_5323_, 0);
                v_isSharedCheck_5393_ = (!lean_is_exclusive(v_a_5323_)) as u8;
                if v_isSharedCheck_5393_ == 0 {
                    v_unused_5394_ = lean_ctor_get(v_a_5323_, 1);
                    lean_dec(v_unused_5394_);
                    v___x_5326_ = v_a_5323_;
                    v_isShared_5327_ = v_isSharedCheck_5393_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_p_5324_);
                    lean_dec(v_a_5323_);
                    v___x_5326_ = lean_box(0);
                    v_isShared_5327_ = v_isSharedCheck_5393_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5328_ = l_Int_Linear_Poly_checkCnstrOf(
                    v_p_5324_,
                    v_____s_5300_,
                    v___y_5306_,
                    v___y_5307_,
                    v___y_5308_,
                    v___y_5309_,
                    v___y_5310_,
                    v___y_5311_,
                    v___y_5312_,
                    v___y_5313_,
                    v___y_5314_,
                    v___y_5315_,
                );
                if lean_obj_tag(v___x_5328_) == 0 {
                    lean_dec_ref_known(v___x_5328_, 1);
                    v___x_5329_ = lean_box(0);
                    v___x_5369_ = lean_box(0);
                    if lean_obj_tag(v_p_5324_) == 1 {
                        v_k_5372_ = lean_ctor_get(v_p_5324_, 0);
                        lean_inc(v_k_5372_);
                        lean_dec_ref_known(v_p_5324_, 3);
                        v___x_5373_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0),
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0_once),
                            _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                        );
                        v___x_5374_ = lean_int_dec_lt(v_k_5372_, v___x_5373_);
                        lean_dec(v_k_5372_);
                        if v_isLower_5301_ == 0 {
                            if v___x_5374_ == 0 {
                                v___y_5371_ = v___x_5317_;
                                state = 13;
                                continue;
                            } else {
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_5371_ = v___x_5374_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5326_);
                        lean_dec_ref(v_p_5324_);
                        lean_dec(v_snd_5319_);
                        v___x_5375_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
                        v___x_5376_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_5375_,
                            v___y_5306_,
                            v___y_5307_,
                            v___y_5308_,
                            v___y_5309_,
                            v___y_5310_,
                            v___y_5311_,
                            v___y_5312_,
                            v___y_5313_,
                            v___y_5314_,
                            v___y_5315_,
                        );
                        if lean_obj_tag(v___x_5376_) == 0 {
                            lean_dec_ref_known(v___x_5376_, 1);
                            v_a_5331_ = v___x_5369_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_5321_);
                            v_a_5377_ = lean_ctor_get(v___x_5376_, 0);
                            v_isSharedCheck_5384_ = (!lean_is_exclusive(v___x_5376_)) as u8;
                            if v_isSharedCheck_5384_ == 0 {
                                v___x_5379_ = v___x_5376_;
                                v_isShared_5380_ = v_isSharedCheck_5384_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_5377_);
                                lean_dec(v___x_5376_);
                                v___x_5379_ = lean_box(0);
                                v_isShared_5380_ = v_isSharedCheck_5384_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5326_);
                    lean_dec_ref(v_p_5324_);
                    lean_del_object(v___x_5321_);
                    lean_dec(v_snd_5319_);
                    v_a_5385_ = lean_ctor_get(v___x_5328_, 0);
                    v_isSharedCheck_5392_ = (!lean_is_exclusive(v___x_5328_)) as u8;
                    if v_isSharedCheck_5392_ == 0 {
                        v___x_5387_ = v___x_5328_;
                        v_isShared_5388_ = v_isSharedCheck_5392_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_5385_);
                        lean_dec(v___x_5328_);
                        v___x_5387_ = lean_box(0);
                        v_isShared_5388_ = v_isSharedCheck_5392_;
                        state = 16;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5322_ == 0 {
                    lean_ctor_set(v___x_5321_, 1, v_a_5331_);
                    lean_ctor_set(v___x_5321_, 0, v___x_5329_);
                    v___x_5333_ = v___x_5321_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5337_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5337_, 0, v___x_5329_);
                    lean_ctor_set(v_reuseFailAlloc_5337_, 1, v_a_5331_);
                    v___x_5333_ = v_reuseFailAlloc_5337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5334_ = 1usize;
                v___x_5335_ = lean_usize_add(v_i_5304_, v___x_5334_);
                v_i_5304_ = v___x_5335_;
                v_b_5305_ = v___x_5333_;
                state = 0;
                continue;
            }
            5 => {
                v___x_5339_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
                v___x_5340_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(
                    v___x_5339_,
                    v___y_5306_,
                    v___y_5307_,
                    v___y_5308_,
                    v___y_5309_,
                    v___y_5310_,
                    v___y_5311_,
                    v___y_5312_,
                    v___y_5313_,
                    v___y_5314_,
                    v___y_5315_,
                );
                if lean_obj_tag(v___x_5340_) == 0 {
                    v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
                    v_isSharedCheck_5360_ = (!lean_is_exclusive(v___x_5340_)) as u8;
                    if v_isSharedCheck_5360_ == 0 {
                        v___x_5343_ = v___x_5340_;
                        v_isShared_5344_ = v_isSharedCheck_5360_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5341_);
                        lean_dec(v___x_5340_);
                        v___x_5343_ = lean_box(0);
                        v_isShared_5344_ = v_isSharedCheck_5360_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5326_);
                    lean_del_object(v___x_5321_);
                    lean_dec(v_snd_5319_);
                    v_a_5361_ = lean_ctor_get(v___x_5340_, 0);
                    v_isSharedCheck_5368_ = (!lean_is_exclusive(v___x_5340_)) as u8;
                    if v_isSharedCheck_5368_ == 0 {
                        v___x_5363_ = v___x_5340_;
                        v_isShared_5364_ = v_isSharedCheck_5368_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5361_);
                        lean_dec(v___x_5340_);
                        v___x_5363_ = lean_box(0);
                        v_isShared_5364_ = v_isSharedCheck_5368_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_5341_) == 0 {
                    lean_del_object(v___x_5321_);
                    v_a_5345_ = lean_ctor_get(v_a_5341_, 0);
                    v_isSharedCheck_5358_ = (!lean_is_exclusive(v_a_5341_)) as u8;
                    if v_isSharedCheck_5358_ == 0 {
                        v___x_5347_ = v_a_5341_;
                        v_isShared_5348_ = v_isSharedCheck_5358_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5345_);
                        lean_dec(v_a_5341_);
                        v___x_5347_ = lean_box(0);
                        v_isShared_5348_ = v_isSharedCheck_5358_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5343_);
                    lean_del_object(v___x_5326_);
                    lean_dec(v_snd_5319_);
                    v_a_5359_ = lean_ctor_get(v_a_5341_, 0);
                    lean_inc(v_a_5359_);
                    lean_dec_ref_known(v_a_5341_, 1);
                    v_a_5331_ = v_a_5359_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v_isShared_5348_ == 0 {
                    lean_ctor_set_tag(v___x_5347_, 1);
                    v___x_5350_ = v___x_5347_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5345_);
                    v___x_5350_ = v_reuseFailAlloc_5357_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5327_ == 0 {
                    lean_ctor_set(v___x_5326_, 1, v_snd_5319_);
                    lean_ctor_set(v___x_5326_, 0, v___x_5350_);
                    v___x_5352_ = v___x_5326_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5356_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5356_, 0, v___x_5350_);
                    lean_ctor_set(v_reuseFailAlloc_5356_, 1, v_snd_5319_);
                    v___x_5352_ = v_reuseFailAlloc_5356_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5344_ == 0 {
                    lean_ctor_set(v___x_5343_, 0, v___x_5352_);
                    v___x_5354_ = v___x_5343_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5352_);
                    v___x_5354_ = v_reuseFailAlloc_5355_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5354_;
            }
            11 => {
                if v_isShared_5364_ == 0 {
                    v___x_5366_ = v___x_5363_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
                    v___x_5366_ = v_reuseFailAlloc_5367_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5366_;
            }
            13 => {
                if v___y_5371_ == 0 {
                    state = 5;
                    continue;
                } else {
                    lean_del_object(v___x_5326_);
                    lean_dec(v_snd_5319_);
                    v_a_5331_ = v___x_5369_;
                    state = 3;
                    continue;
                }
            }
            14 => {
                if v_isShared_5380_ == 0 {
                    v___x_5382_ = v___x_5379_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
                    v___x_5382_ = v_reuseFailAlloc_5383_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5382_;
            }
            16 => {
                if v_isShared_5388_ == 0 {
                    v___x_5390_ = v___x_5387_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
                    v___x_5390_ = v_reuseFailAlloc_5391_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_5397_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_5398_: *mut LeanObject = *_args.add(1);
    let mut v_as_5399_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5400_: *mut LeanObject = *_args.add(3);
    let mut v_i_5401_: *mut LeanObject = *_args.add(4);
    let mut v_b_5402_: *mut LeanObject = *_args.add(5);
    let mut v___y_5403_: *mut LeanObject = *_args.add(6);
    let mut v___y_5404_: *mut LeanObject = *_args.add(7);
    let mut v___y_5405_: *mut LeanObject = *_args.add(8);
    let mut v___y_5406_: *mut LeanObject = *_args.add(9);
    let mut v___y_5407_: *mut LeanObject = *_args.add(10);
    let mut v___y_5408_: *mut LeanObject = *_args.add(11);
    let mut v___y_5409_: *mut LeanObject = *_args.add(12);
    let mut v___y_5410_: *mut LeanObject = *_args.add(13);
    let mut v___y_5411_: *mut LeanObject = *_args.add(14);
    let mut v___y_5412_: *mut LeanObject = *_args.add(15);
    let mut v___y_5413_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5414_: u8 = 0;
    let mut v_sz_boxed_5415_: usize = 0;
    let mut v_i_boxed_5416_: usize = 0;
    let mut v_res_5417_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5414_ = (lean_unbox(v_isLower_5398_) as u8);
    v_sz_boxed_5415_ = lean_unbox_usize(v_sz_5400_);
    lean_dec(v_sz_5400_);
    v_i_boxed_5416_ = lean_unbox_usize(v_i_5401_);
    lean_dec(v_i_5401_);
    v_res_5417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_5397_, v_isLower_boxed_5414_, v_as_5399_, v_sz_boxed_5415_, v_i_boxed_5416_, v_b_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_);
    lean_dec(v___y_5412_);
    lean_dec_ref(v___y_5411_);
    lean_dec(v___y_5410_);
    lean_dec_ref(v___y_5409_);
    lean_dec(v___y_5408_);
    lean_dec_ref(v___y_5407_);
    lean_dec(v___y_5406_);
    lean_dec_ref(v___y_5405_);
    lean_dec(v___y_5404_);
    lean_dec(v___y_5403_);
    lean_dec_ref(v_as_5399_);
    lean_dec(v_____s_5397_);
    return v_res_5417_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(
    mut v_____s_5418_: *mut LeanObject,
    mut v_isLower_5419_: u8,
    mut v_as_5420_: *mut LeanObject,
    mut v_sz_5421_: usize,
    mut v_i_5422_: usize,
    mut v_b_5423_: *mut LeanObject,
    mut v___y_5424_: *mut LeanObject,
    mut v___y_5425_: *mut LeanObject,
    mut v___y_5426_: *mut LeanObject,
    mut v___y_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5435_: u8 = 0;
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5440_: u8 = 0;
    let mut v_a_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5445_: u8 = 0;
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: usize = 0;
    let mut v___x_5454_: usize = 0;
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v_a_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut v_a_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut v_a_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5483_: u8 = 0;
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5487_: u8 = 0;
    let mut v___y_5489_: u8 = 0;
    let mut v_k_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: u8 = 0;
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5498_: u8 = 0;
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v_a_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5506_: u8 = 0;
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5510_: u8 = 0;
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut v_unused_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5513_: u8 = 0;
    let mut v_unused_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5435_ = lean_usize_dec_lt(v_i_5422_, v_sz_5421_);
                if v___x_5435_ == 0 {
                    v___x_5436_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5436_, 0, v_b_5423_);
                    return v___x_5436_;
                } else {
                    v_snd_5437_ = lean_ctor_get(v_b_5423_, 1);
                    v_isSharedCheck_5513_ = (!lean_is_exclusive(v_b_5423_)) as u8;
                    if v_isSharedCheck_5513_ == 0 {
                        v_unused_5514_ = lean_ctor_get(v_b_5423_, 0);
                        lean_dec(v_unused_5514_);
                        v___x_5439_ = v_b_5423_;
                        v_isShared_5440_ = v_isSharedCheck_5513_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5437_);
                        lean_dec(v_b_5423_);
                        v___x_5439_ = lean_box(0);
                        v_isShared_5440_ = v_isSharedCheck_5513_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5441_ = lean_array_uget(v_as_5420_, v_i_5422_);
                v_p_5442_ = lean_ctor_get(v_a_5441_, 0);
                v_isSharedCheck_5511_ = (!lean_is_exclusive(v_a_5441_)) as u8;
                if v_isSharedCheck_5511_ == 0 {
                    v_unused_5512_ = lean_ctor_get(v_a_5441_, 1);
                    lean_dec(v_unused_5512_);
                    v___x_5444_ = v_a_5441_;
                    v_isShared_5445_ = v_isSharedCheck_5511_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_p_5442_);
                    lean_dec(v_a_5441_);
                    v___x_5444_ = lean_box(0);
                    v_isShared_5445_ = v_isSharedCheck_5511_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5446_ = l_Int_Linear_Poly_checkCnstrOf(
                    v_p_5442_,
                    v_____s_5418_,
                    v___y_5424_,
                    v___y_5425_,
                    v___y_5426_,
                    v___y_5427_,
                    v___y_5428_,
                    v___y_5429_,
                    v___y_5430_,
                    v___y_5431_,
                    v___y_5432_,
                    v___y_5433_,
                );
                if lean_obj_tag(v___x_5446_) == 0 {
                    lean_dec_ref_known(v___x_5446_, 1);
                    v___x_5447_ = lean_box(0);
                    v___x_5448_ = lean_box(0);
                    if lean_obj_tag(v_p_5442_) == 1 {
                        v_k_5490_ = lean_ctor_get(v_p_5442_, 0);
                        lean_inc(v_k_5490_);
                        lean_dec_ref_known(v_p_5442_, 3);
                        v___x_5491_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0),
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0_once),
                            _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                        );
                        v___x_5492_ = lean_int_dec_lt(v_k_5490_, v___x_5491_);
                        lean_dec(v_k_5490_);
                        if v_isLower_5419_ == 0 {
                            if v___x_5492_ == 0 {
                                v___y_5489_ = v___x_5435_;
                                state = 13;
                                continue;
                            } else {
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_5489_ = v___x_5492_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5444_);
                        lean_dec_ref(v_p_5442_);
                        lean_dec(v_snd_5437_);
                        v___x_5493_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
                        v___x_5494_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_5493_,
                            v___y_5424_,
                            v___y_5425_,
                            v___y_5426_,
                            v___y_5427_,
                            v___y_5428_,
                            v___y_5429_,
                            v___y_5430_,
                            v___y_5431_,
                            v___y_5432_,
                            v___y_5433_,
                        );
                        if lean_obj_tag(v___x_5494_) == 0 {
                            lean_dec_ref_known(v___x_5494_, 1);
                            v_a_5450_ = v___x_5447_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_5439_);
                            v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
                            v_isSharedCheck_5502_ = (!lean_is_exclusive(v___x_5494_)) as u8;
                            if v_isSharedCheck_5502_ == 0 {
                                v___x_5497_ = v___x_5494_;
                                v_isShared_5498_ = v_isSharedCheck_5502_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_5495_);
                                lean_dec(v___x_5494_);
                                v___x_5497_ = lean_box(0);
                                v_isShared_5498_ = v_isSharedCheck_5502_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5444_);
                    lean_dec_ref(v_p_5442_);
                    lean_del_object(v___x_5439_);
                    lean_dec(v_snd_5437_);
                    v_a_5503_ = lean_ctor_get(v___x_5446_, 0);
                    v_isSharedCheck_5510_ = (!lean_is_exclusive(v___x_5446_)) as u8;
                    if v_isSharedCheck_5510_ == 0 {
                        v___x_5505_ = v___x_5446_;
                        v_isShared_5506_ = v_isSharedCheck_5510_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_5503_);
                        lean_dec(v___x_5446_);
                        v___x_5505_ = lean_box(0);
                        v_isShared_5506_ = v_isSharedCheck_5510_;
                        state = 16;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5440_ == 0 {
                    lean_ctor_set(v___x_5439_, 1, v_a_5450_);
                    lean_ctor_set(v___x_5439_, 0, v___x_5448_);
                    v___x_5452_ = v___x_5439_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5456_, 0, v___x_5448_);
                    lean_ctor_set(v_reuseFailAlloc_5456_, 1, v_a_5450_);
                    v___x_5452_ = v_reuseFailAlloc_5456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5453_ = 1usize;
                v___x_5454_ = lean_usize_add(v_i_5422_, v___x_5453_);
                v___x_5455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_5418_, v_isLower_5419_, v_as_5420_, v_sz_5421_, v___x_5454_, v___x_5452_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
                return v___x_5455_;
            }
            5 => {
                v___x_5458_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
                v___x_5459_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(
                    v___x_5458_,
                    v___y_5424_,
                    v___y_5425_,
                    v___y_5426_,
                    v___y_5427_,
                    v___y_5428_,
                    v___y_5429_,
                    v___y_5430_,
                    v___y_5431_,
                    v___y_5432_,
                    v___y_5433_,
                );
                if lean_obj_tag(v___x_5459_) == 0 {
                    v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
                    v_isSharedCheck_5479_ = (!lean_is_exclusive(v___x_5459_)) as u8;
                    if v_isSharedCheck_5479_ == 0 {
                        v___x_5462_ = v___x_5459_;
                        v_isShared_5463_ = v_isSharedCheck_5479_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5460_);
                        lean_dec(v___x_5459_);
                        v___x_5462_ = lean_box(0);
                        v_isShared_5463_ = v_isSharedCheck_5479_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5444_);
                    lean_del_object(v___x_5439_);
                    lean_dec(v_snd_5437_);
                    v_a_5480_ = lean_ctor_get(v___x_5459_, 0);
                    v_isSharedCheck_5487_ = (!lean_is_exclusive(v___x_5459_)) as u8;
                    if v_isSharedCheck_5487_ == 0 {
                        v___x_5482_ = v___x_5459_;
                        v_isShared_5483_ = v_isSharedCheck_5487_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5480_);
                        lean_dec(v___x_5459_);
                        v___x_5482_ = lean_box(0);
                        v_isShared_5483_ = v_isSharedCheck_5487_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_5460_) == 0 {
                    lean_del_object(v___x_5439_);
                    v_a_5464_ = lean_ctor_get(v_a_5460_, 0);
                    v_isSharedCheck_5477_ = (!lean_is_exclusive(v_a_5460_)) as u8;
                    if v_isSharedCheck_5477_ == 0 {
                        v___x_5466_ = v_a_5460_;
                        v_isShared_5467_ = v_isSharedCheck_5477_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5464_);
                        lean_dec(v_a_5460_);
                        v___x_5466_ = lean_box(0);
                        v_isShared_5467_ = v_isSharedCheck_5477_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5462_);
                    lean_del_object(v___x_5444_);
                    lean_dec(v_snd_5437_);
                    v_a_5478_ = lean_ctor_get(v_a_5460_, 0);
                    lean_inc(v_a_5478_);
                    lean_dec_ref_known(v_a_5460_, 1);
                    v_a_5450_ = v_a_5478_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v_isShared_5467_ == 0 {
                    lean_ctor_set_tag(v___x_5466_, 1);
                    v___x_5469_ = v___x_5466_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5476_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5464_);
                    v___x_5469_ = v_reuseFailAlloc_5476_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5445_ == 0 {
                    lean_ctor_set(v___x_5444_, 1, v_snd_5437_);
                    lean_ctor_set(v___x_5444_, 0, v___x_5469_);
                    v___x_5471_ = v___x_5444_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5469_);
                    lean_ctor_set(v_reuseFailAlloc_5475_, 1, v_snd_5437_);
                    v___x_5471_ = v_reuseFailAlloc_5475_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5463_ == 0 {
                    lean_ctor_set(v___x_5462_, 0, v___x_5471_);
                    v___x_5473_ = v___x_5462_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5471_);
                    v___x_5473_ = v_reuseFailAlloc_5474_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5473_;
            }
            11 => {
                if v_isShared_5483_ == 0 {
                    v___x_5485_ = v___x_5482_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5486_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_a_5480_);
                    v___x_5485_ = v_reuseFailAlloc_5486_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5485_;
            }
            13 => {
                if v___y_5489_ == 0 {
                    state = 5;
                    continue;
                } else {
                    lean_del_object(v___x_5444_);
                    lean_dec(v_snd_5437_);
                    v_a_5450_ = v___x_5447_;
                    state = 3;
                    continue;
                }
            }
            14 => {
                if v_isShared_5498_ == 0 {
                    v___x_5500_ = v___x_5497_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
                    v___x_5500_ = v_reuseFailAlloc_5501_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5500_;
            }
            16 => {
                if v_isShared_5506_ == 0 {
                    v___x_5508_ = v___x_5505_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
                    v___x_5508_ = v_reuseFailAlloc_5509_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_5515_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_5516_: *mut LeanObject = *_args.add(1);
    let mut v_as_5517_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5518_: *mut LeanObject = *_args.add(3);
    let mut v_i_5519_: *mut LeanObject = *_args.add(4);
    let mut v_b_5520_: *mut LeanObject = *_args.add(5);
    let mut v___y_5521_: *mut LeanObject = *_args.add(6);
    let mut v___y_5522_: *mut LeanObject = *_args.add(7);
    let mut v___y_5523_: *mut LeanObject = *_args.add(8);
    let mut v___y_5524_: *mut LeanObject = *_args.add(9);
    let mut v___y_5525_: *mut LeanObject = *_args.add(10);
    let mut v___y_5526_: *mut LeanObject = *_args.add(11);
    let mut v___y_5527_: *mut LeanObject = *_args.add(12);
    let mut v___y_5528_: *mut LeanObject = *_args.add(13);
    let mut v___y_5529_: *mut LeanObject = *_args.add(14);
    let mut v___y_5530_: *mut LeanObject = *_args.add(15);
    let mut v___y_5531_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5532_: u8 = 0;
    let mut v_sz_boxed_5533_: usize = 0;
    let mut v_i_boxed_5534_: usize = 0;
    let mut v_res_5535_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5532_ = (lean_unbox(v_isLower_5516_) as u8);
    v_sz_boxed_5533_ = lean_unbox_usize(v_sz_5518_);
    lean_dec(v_sz_5518_);
    v_i_boxed_5534_ = lean_unbox_usize(v_i_5519_);
    lean_dec(v_i_5519_);
    v_res_5535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_5515_, v_isLower_boxed_5532_, v_as_5517_, v_sz_boxed_5533_, v_i_boxed_5534_, v_b_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_);
    lean_dec(v___y_5530_);
    lean_dec_ref(v___y_5529_);
    lean_dec(v___y_5528_);
    lean_dec_ref(v___y_5527_);
    lean_dec(v___y_5526_);
    lean_dec_ref(v___y_5525_);
    lean_dec(v___y_5524_);
    lean_dec_ref(v___y_5523_);
    lean_dec(v___y_5522_);
    lean_dec(v___y_5521_);
    lean_dec_ref(v_as_5517_);
    lean_dec(v_____s_5515_);
    return v_res_5535_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(
    mut v_____s_5536_: *mut LeanObject,
    mut v_isLower_5537_: u8,
    mut v_as_5538_: *mut LeanObject,
    mut v_sz_5539_: usize,
    mut v_i_5540_: usize,
    mut v_b_5541_: *mut LeanObject,
    mut v___y_5542_: *mut LeanObject,
    mut v___y_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
    mut v___y_5551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5553_: u8 = 0;
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5558_: u8 = 0;
    let mut v_a_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5563_: u8 = 0;
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: usize = 0;
    let mut v___x_5571_: usize = 0;
    let mut v_reuseFailAlloc_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5580_: u8 = 0;
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_a_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5593_: u8 = 0;
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5600_: u8 = 0;
    let mut v_k_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: u8 = 0;
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut v_a_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5621_: u8 = 0;
    let mut v_isSharedCheck_5622_: u8 = 0;
    let mut v_unused_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5624_: u8 = 0;
    let mut v_unused_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5553_ = lean_usize_dec_lt(v_i_5540_, v_sz_5539_);
                if v___x_5553_ == 0 {
                    v___x_5554_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5554_, 0, v_b_5541_);
                    return v___x_5554_;
                } else {
                    v_snd_5555_ = lean_ctor_get(v_b_5541_, 1);
                    v_isSharedCheck_5624_ = (!lean_is_exclusive(v_b_5541_)) as u8;
                    if v_isSharedCheck_5624_ == 0 {
                        v_unused_5625_ = lean_ctor_get(v_b_5541_, 0);
                        lean_dec(v_unused_5625_);
                        v___x_5557_ = v_b_5541_;
                        v_isShared_5558_ = v_isSharedCheck_5624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5555_);
                        lean_dec(v_b_5541_);
                        v___x_5557_ = lean_box(0);
                        v_isShared_5558_ = v_isSharedCheck_5624_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5559_ = lean_array_uget(v_as_5538_, v_i_5540_);
                v_p_5560_ = lean_ctor_get(v_a_5559_, 0);
                v_isSharedCheck_5622_ = (!lean_is_exclusive(v_a_5559_)) as u8;
                if v_isSharedCheck_5622_ == 0 {
                    v_unused_5623_ = lean_ctor_get(v_a_5559_, 1);
                    lean_dec(v_unused_5623_);
                    v___x_5562_ = v_a_5559_;
                    v_isShared_5563_ = v_isSharedCheck_5622_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_p_5560_);
                    lean_dec(v_a_5559_);
                    v___x_5562_ = lean_box(0);
                    v_isShared_5563_ = v_isSharedCheck_5622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5564_ = l_Int_Linear_Poly_checkCnstrOf(
                    v_p_5560_,
                    v_____s_5536_,
                    v___y_5542_,
                    v___y_5543_,
                    v___y_5544_,
                    v___y_5545_,
                    v___y_5546_,
                    v___y_5547_,
                    v___y_5548_,
                    v___y_5549_,
                    v___y_5550_,
                    v___y_5551_,
                );
                if lean_obj_tag(v___x_5564_) == 0 {
                    lean_dec_ref_known(v___x_5564_, 1);
                    v___x_5565_ = lean_box(0);
                    v___x_5598_ = lean_box(0);
                    if lean_obj_tag(v_p_5560_) == 1 {
                        v_k_5601_ = lean_ctor_get(v_p_5560_, 0);
                        lean_inc(v_k_5601_);
                        lean_dec_ref_known(v_p_5560_, 3);
                        v___x_5602_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0),
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0_once),
                            _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                        );
                        v___x_5603_ = lean_int_dec_lt(v_k_5601_, v___x_5602_);
                        lean_dec(v_k_5601_);
                        if v_isLower_5537_ == 0 {
                            if v___x_5603_ == 0 {
                                v___y_5600_ = v___x_5553_;
                                state = 11;
                                continue;
                            } else {
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_5600_ = v___x_5603_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5562_);
                        lean_dec_ref(v_p_5560_);
                        lean_dec(v_snd_5555_);
                        v___x_5604_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
                        v___x_5605_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_5604_,
                            v___y_5542_,
                            v___y_5543_,
                            v___y_5544_,
                            v___y_5545_,
                            v___y_5546_,
                            v___y_5547_,
                            v___y_5548_,
                            v___y_5549_,
                            v___y_5550_,
                            v___y_5551_,
                        );
                        if lean_obj_tag(v___x_5605_) == 0 {
                            lean_dec_ref_known(v___x_5605_, 1);
                            v_a_5567_ = v___x_5598_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_5557_);
                            v_a_5606_ = lean_ctor_get(v___x_5605_, 0);
                            v_isSharedCheck_5613_ = (!lean_is_exclusive(v___x_5605_)) as u8;
                            if v_isSharedCheck_5613_ == 0 {
                                v___x_5608_ = v___x_5605_;
                                v_isShared_5609_ = v_isSharedCheck_5613_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_5606_);
                                lean_dec(v___x_5605_);
                                v___x_5608_ = lean_box(0);
                                v_isShared_5609_ = v_isSharedCheck_5613_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5562_);
                    lean_dec_ref(v_p_5560_);
                    lean_del_object(v___x_5557_);
                    lean_dec(v_snd_5555_);
                    v_a_5614_ = lean_ctor_get(v___x_5564_, 0);
                    v_isSharedCheck_5621_ = (!lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5621_ == 0 {
                        v___x_5616_ = v___x_5564_;
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_5614_);
                        lean_dec(v___x_5564_);
                        v___x_5616_ = lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5558_ == 0 {
                    lean_ctor_set(v___x_5557_, 1, v_a_5567_);
                    lean_ctor_set(v___x_5557_, 0, v___x_5565_);
                    v___x_5569_ = v___x_5557_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5565_);
                    lean_ctor_set(v_reuseFailAlloc_5573_, 1, v_a_5567_);
                    v___x_5569_ = v_reuseFailAlloc_5573_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5570_ = 1usize;
                v___x_5571_ = lean_usize_add(v_i_5540_, v___x_5570_);
                v_i_5540_ = v___x_5571_;
                v_b_5541_ = v___x_5569_;
                state = 0;
                continue;
            }
            5 => {
                v___x_5575_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
                v___x_5576_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(
                    v___x_5575_,
                    v___y_5542_,
                    v___y_5543_,
                    v___y_5544_,
                    v___y_5545_,
                    v___y_5546_,
                    v___y_5547_,
                    v___y_5548_,
                    v___y_5549_,
                    v___y_5550_,
                    v___y_5551_,
                );
                if lean_obj_tag(v___x_5576_) == 0 {
                    v_a_5577_ = lean_ctor_get(v___x_5576_, 0);
                    v_isSharedCheck_5589_ = (!lean_is_exclusive(v___x_5576_)) as u8;
                    if v_isSharedCheck_5589_ == 0 {
                        v___x_5579_ = v___x_5576_;
                        v_isShared_5580_ = v_isSharedCheck_5589_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5577_);
                        lean_dec(v___x_5576_);
                        v___x_5579_ = lean_box(0);
                        v_isShared_5580_ = v_isSharedCheck_5589_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5562_);
                    lean_del_object(v___x_5557_);
                    lean_dec(v_snd_5555_);
                    v_a_5590_ = lean_ctor_get(v___x_5576_, 0);
                    v_isSharedCheck_5597_ = (!lean_is_exclusive(v___x_5576_)) as u8;
                    if v_isSharedCheck_5597_ == 0 {
                        v___x_5592_ = v___x_5576_;
                        v_isShared_5593_ = v_isSharedCheck_5597_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5590_);
                        lean_dec(v___x_5576_);
                        v___x_5592_ = lean_box(0);
                        v_isShared_5593_ = v_isSharedCheck_5597_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_5577_) == 0 {
                    lean_del_object(v___x_5557_);
                    v___x_5581_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5581_, 0, v_a_5577_);
                    if v_isShared_5563_ == 0 {
                        lean_ctor_set(v___x_5562_, 1, v_snd_5555_);
                        lean_ctor_set(v___x_5562_, 0, v___x_5581_);
                        v___x_5583_ = v___x_5562_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5581_);
                        lean_ctor_set(v_reuseFailAlloc_5587_, 1, v_snd_5555_);
                        v___x_5583_ = v_reuseFailAlloc_5587_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5579_);
                    lean_del_object(v___x_5562_);
                    lean_dec(v_snd_5555_);
                    v_a_5588_ = lean_ctor_get(v_a_5577_, 0);
                    lean_inc(v_a_5588_);
                    lean_dec_ref_known(v_a_5577_, 1);
                    v_a_5567_ = v_a_5588_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v_isShared_5580_ == 0 {
                    lean_ctor_set(v___x_5579_, 0, v___x_5583_);
                    v___x_5585_ = v___x_5579_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
                    v___x_5585_ = v_reuseFailAlloc_5586_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5585_;
            }
            9 => {
                if v_isShared_5593_ == 0 {
                    v___x_5595_ = v___x_5592_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5590_);
                    v___x_5595_ = v_reuseFailAlloc_5596_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5595_;
            }
            11 => {
                if v___y_5600_ == 0 {
                    state = 5;
                    continue;
                } else {
                    lean_del_object(v___x_5562_);
                    lean_dec(v_snd_5555_);
                    v_a_5567_ = v___x_5598_;
                    state = 3;
                    continue;
                }
            }
            12 => {
                if v_isShared_5609_ == 0 {
                    v___x_5611_ = v___x_5608_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
                    v___x_5611_ = v_reuseFailAlloc_5612_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5611_;
            }
            14 => {
                if v_isShared_5617_ == 0 {
                    v___x_5619_ = v___x_5616_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
                    v___x_5619_ = v_reuseFailAlloc_5620_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_5626_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_5627_: *mut LeanObject = *_args.add(1);
    let mut v_as_5628_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5629_: *mut LeanObject = *_args.add(3);
    let mut v_i_5630_: *mut LeanObject = *_args.add(4);
    let mut v_b_5631_: *mut LeanObject = *_args.add(5);
    let mut v___y_5632_: *mut LeanObject = *_args.add(6);
    let mut v___y_5633_: *mut LeanObject = *_args.add(7);
    let mut v___y_5634_: *mut LeanObject = *_args.add(8);
    let mut v___y_5635_: *mut LeanObject = *_args.add(9);
    let mut v___y_5636_: *mut LeanObject = *_args.add(10);
    let mut v___y_5637_: *mut LeanObject = *_args.add(11);
    let mut v___y_5638_: *mut LeanObject = *_args.add(12);
    let mut v___y_5639_: *mut LeanObject = *_args.add(13);
    let mut v___y_5640_: *mut LeanObject = *_args.add(14);
    let mut v___y_5641_: *mut LeanObject = *_args.add(15);
    let mut v___y_5642_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5643_: u8 = 0;
    let mut v_sz_boxed_5644_: usize = 0;
    let mut v_i_boxed_5645_: usize = 0;
    let mut v_res_5646_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5643_ = (lean_unbox(v_isLower_5627_) as u8);
    v_sz_boxed_5644_ = lean_unbox_usize(v_sz_5629_);
    lean_dec(v_sz_5629_);
    v_i_boxed_5645_ = lean_unbox_usize(v_i_5630_);
    lean_dec(v_i_5630_);
    v_res_5646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_5626_, v_isLower_boxed_5643_, v_as_5628_, v_sz_boxed_5644_, v_i_boxed_5645_, v_b_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
    lean_dec(v___y_5641_);
    lean_dec_ref(v___y_5640_);
    lean_dec(v___y_5639_);
    lean_dec_ref(v___y_5638_);
    lean_dec(v___y_5637_);
    lean_dec_ref(v___y_5636_);
    lean_dec(v___y_5635_);
    lean_dec_ref(v___y_5634_);
    lean_dec(v___y_5633_);
    lean_dec(v___y_5632_);
    lean_dec_ref(v_as_5628_);
    lean_dec(v_____s_5626_);
    return v_res_5646_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(
    mut v_____s_5647_: *mut LeanObject,
    mut v_isLower_5648_: u8,
    mut v_as_5649_: *mut LeanObject,
    mut v_sz_5650_: usize,
    mut v_i_5651_: usize,
    mut v_b_5652_: *mut LeanObject,
    mut v___y_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
    mut v___y_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
    mut v___y_5662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5664_: u8 = 0;
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5669_: u8 = 0;
    let mut v_a_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5674_: u8 = 0;
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: usize = 0;
    let mut v___x_5683_: usize = 0;
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5692_: u8 = 0;
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5701_: u8 = 0;
    let mut v_a_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5705_: u8 = 0;
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5709_: u8 = 0;
    let mut v___y_5711_: u8 = 0;
    let mut v_k_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: u8 = 0;
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5720_: u8 = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut v_a_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5728_: u8 = 0;
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5732_: u8 = 0;
    let mut v_isSharedCheck_5733_: u8 = 0;
    let mut v_unused_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5735_: u8 = 0;
    let mut v_unused_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5664_ = lean_usize_dec_lt(v_i_5651_, v_sz_5650_);
                if v___x_5664_ == 0 {
                    v___x_5665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5665_, 0, v_b_5652_);
                    return v___x_5665_;
                } else {
                    v_snd_5666_ = lean_ctor_get(v_b_5652_, 1);
                    v_isSharedCheck_5735_ = (!lean_is_exclusive(v_b_5652_)) as u8;
                    if v_isSharedCheck_5735_ == 0 {
                        v_unused_5736_ = lean_ctor_get(v_b_5652_, 0);
                        lean_dec(v_unused_5736_);
                        v___x_5668_ = v_b_5652_;
                        v_isShared_5669_ = v_isSharedCheck_5735_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5666_);
                        lean_dec(v_b_5652_);
                        v___x_5668_ = lean_box(0);
                        v_isShared_5669_ = v_isSharedCheck_5735_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5670_ = lean_array_uget(v_as_5649_, v_i_5651_);
                v_p_5671_ = lean_ctor_get(v_a_5670_, 0);
                v_isSharedCheck_5733_ = (!lean_is_exclusive(v_a_5670_)) as u8;
                if v_isSharedCheck_5733_ == 0 {
                    v_unused_5734_ = lean_ctor_get(v_a_5670_, 1);
                    lean_dec(v_unused_5734_);
                    v___x_5673_ = v_a_5670_;
                    v_isShared_5674_ = v_isSharedCheck_5733_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_p_5671_);
                    lean_dec(v_a_5670_);
                    v___x_5673_ = lean_box(0);
                    v_isShared_5674_ = v_isSharedCheck_5733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5675_ = l_Int_Linear_Poly_checkCnstrOf(
                    v_p_5671_,
                    v_____s_5647_,
                    v___y_5653_,
                    v___y_5654_,
                    v___y_5655_,
                    v___y_5656_,
                    v___y_5657_,
                    v___y_5658_,
                    v___y_5659_,
                    v___y_5660_,
                    v___y_5661_,
                    v___y_5662_,
                );
                if lean_obj_tag(v___x_5675_) == 0 {
                    lean_dec_ref_known(v___x_5675_, 1);
                    v___x_5676_ = lean_box(0);
                    v___x_5677_ = lean_box(0);
                    if lean_obj_tag(v_p_5671_) == 1 {
                        v_k_5712_ = lean_ctor_get(v_p_5671_, 0);
                        lean_inc(v_k_5712_);
                        lean_dec_ref_known(v_p_5671_, 3);
                        v___x_5713_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0),
                            core::ptr::addr_of_mut!(l_Int_Linear_Poly_checkCoeffs___closed__0_once),
                            _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                        );
                        v___x_5714_ = lean_int_dec_lt(v_k_5712_, v___x_5713_);
                        lean_dec(v_k_5712_);
                        if v_isLower_5648_ == 0 {
                            if v___x_5714_ == 0 {
                                v___y_5711_ = v___x_5664_;
                                state = 11;
                                continue;
                            } else {
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_5711_ = v___x_5714_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5673_);
                        lean_dec_ref(v_p_5671_);
                        lean_dec(v_snd_5666_);
                        v___x_5715_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__3);
                        v___x_5716_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_5715_,
                            v___y_5653_,
                            v___y_5654_,
                            v___y_5655_,
                            v___y_5656_,
                            v___y_5657_,
                            v___y_5658_,
                            v___y_5659_,
                            v___y_5660_,
                            v___y_5661_,
                            v___y_5662_,
                        );
                        if lean_obj_tag(v___x_5716_) == 0 {
                            lean_dec_ref_known(v___x_5716_, 1);
                            v_a_5679_ = v___x_5676_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_5668_);
                            v_a_5717_ = lean_ctor_get(v___x_5716_, 0);
                            v_isSharedCheck_5724_ = (!lean_is_exclusive(v___x_5716_)) as u8;
                            if v_isSharedCheck_5724_ == 0 {
                                v___x_5719_ = v___x_5716_;
                                v_isShared_5720_ = v_isSharedCheck_5724_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_5717_);
                                lean_dec(v___x_5716_);
                                v___x_5719_ = lean_box(0);
                                v_isShared_5720_ = v_isSharedCheck_5724_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5673_);
                    lean_dec_ref(v_p_5671_);
                    lean_del_object(v___x_5668_);
                    lean_dec(v_snd_5666_);
                    v_a_5725_ = lean_ctor_get(v___x_5675_, 0);
                    v_isSharedCheck_5732_ = (!lean_is_exclusive(v___x_5675_)) as u8;
                    if v_isSharedCheck_5732_ == 0 {
                        v___x_5727_ = v___x_5675_;
                        v_isShared_5728_ = v_isSharedCheck_5732_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_5725_);
                        lean_dec(v___x_5675_);
                        v___x_5727_ = lean_box(0);
                        v_isShared_5728_ = v_isSharedCheck_5732_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5669_ == 0 {
                    lean_ctor_set(v___x_5668_, 1, v_a_5679_);
                    lean_ctor_set(v___x_5668_, 0, v___x_5677_);
                    v___x_5681_ = v___x_5668_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5685_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5685_, 0, v___x_5677_);
                    lean_ctor_set(v_reuseFailAlloc_5685_, 1, v_a_5679_);
                    v___x_5681_ = v_reuseFailAlloc_5685_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5682_ = 1usize;
                v___x_5683_ = lean_usize_add(v_i_5651_, v___x_5682_);
                v___x_5684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_5647_, v_isLower_5648_, v_as_5649_, v_sz_5650_, v___x_5683_, v___x_5681_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_);
                return v___x_5684_;
            }
            5 => {
                v___x_5687_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2_spec__5___closed__2);
                v___x_5688_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(
                    v___x_5687_,
                    v___y_5653_,
                    v___y_5654_,
                    v___y_5655_,
                    v___y_5656_,
                    v___y_5657_,
                    v___y_5658_,
                    v___y_5659_,
                    v___y_5660_,
                    v___y_5661_,
                    v___y_5662_,
                );
                if lean_obj_tag(v___x_5688_) == 0 {
                    v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
                    v_isSharedCheck_5701_ = (!lean_is_exclusive(v___x_5688_)) as u8;
                    if v_isSharedCheck_5701_ == 0 {
                        v___x_5691_ = v___x_5688_;
                        v_isShared_5692_ = v_isSharedCheck_5701_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5689_);
                        lean_dec(v___x_5688_);
                        v___x_5691_ = lean_box(0);
                        v_isShared_5692_ = v_isSharedCheck_5701_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5673_);
                    lean_del_object(v___x_5668_);
                    lean_dec(v_snd_5666_);
                    v_a_5702_ = lean_ctor_get(v___x_5688_, 0);
                    v_isSharedCheck_5709_ = (!lean_is_exclusive(v___x_5688_)) as u8;
                    if v_isSharedCheck_5709_ == 0 {
                        v___x_5704_ = v___x_5688_;
                        v_isShared_5705_ = v_isSharedCheck_5709_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5702_);
                        lean_dec(v___x_5688_);
                        v___x_5704_ = lean_box(0);
                        v_isShared_5705_ = v_isSharedCheck_5709_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_5689_) == 0 {
                    lean_del_object(v___x_5668_);
                    v___x_5693_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5693_, 0, v_a_5689_);
                    if v_isShared_5674_ == 0 {
                        lean_ctor_set(v___x_5673_, 1, v_snd_5666_);
                        lean_ctor_set(v___x_5673_, 0, v___x_5693_);
                        v___x_5695_ = v___x_5673_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5699_, 0, v___x_5693_);
                        lean_ctor_set(v_reuseFailAlloc_5699_, 1, v_snd_5666_);
                        v___x_5695_ = v_reuseFailAlloc_5699_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5691_);
                    lean_del_object(v___x_5673_);
                    lean_dec(v_snd_5666_);
                    v_a_5700_ = lean_ctor_get(v_a_5689_, 0);
                    lean_inc(v_a_5700_);
                    lean_dec_ref_known(v_a_5689_, 1);
                    v_a_5679_ = v_a_5700_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if v_isShared_5692_ == 0 {
                    lean_ctor_set(v___x_5691_, 0, v___x_5695_);
                    v___x_5697_ = v___x_5691_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5695_);
                    v___x_5697_ = v_reuseFailAlloc_5698_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5697_;
            }
            9 => {
                if v_isShared_5705_ == 0 {
                    v___x_5707_ = v___x_5704_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5708_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_a_5702_);
                    v___x_5707_ = v_reuseFailAlloc_5708_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5707_;
            }
            11 => {
                if v___y_5711_ == 0 {
                    state = 5;
                    continue;
                } else {
                    lean_del_object(v___x_5673_);
                    lean_dec(v_snd_5666_);
                    v_a_5679_ = v___x_5676_;
                    state = 3;
                    continue;
                }
            }
            12 => {
                if v_isShared_5720_ == 0 {
                    v___x_5722_ = v___x_5719_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
                    v___x_5722_ = v_reuseFailAlloc_5723_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5722_;
            }
            14 => {
                if v_isShared_5728_ == 0 {
                    v___x_5730_ = v___x_5727_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5731_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_a_5725_);
                    v___x_5730_ = v_reuseFailAlloc_5731_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_5737_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_5738_: *mut LeanObject = *_args.add(1);
    let mut v_as_5739_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5740_: *mut LeanObject = *_args.add(3);
    let mut v_i_5741_: *mut LeanObject = *_args.add(4);
    let mut v_b_5742_: *mut LeanObject = *_args.add(5);
    let mut v___y_5743_: *mut LeanObject = *_args.add(6);
    let mut v___y_5744_: *mut LeanObject = *_args.add(7);
    let mut v___y_5745_: *mut LeanObject = *_args.add(8);
    let mut v___y_5746_: *mut LeanObject = *_args.add(9);
    let mut v___y_5747_: *mut LeanObject = *_args.add(10);
    let mut v___y_5748_: *mut LeanObject = *_args.add(11);
    let mut v___y_5749_: *mut LeanObject = *_args.add(12);
    let mut v___y_5750_: *mut LeanObject = *_args.add(13);
    let mut v___y_5751_: *mut LeanObject = *_args.add(14);
    let mut v___y_5752_: *mut LeanObject = *_args.add(15);
    let mut v___y_5753_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5754_: u8 = 0;
    let mut v_sz_boxed_5755_: usize = 0;
    let mut v_i_boxed_5756_: usize = 0;
    let mut v_res_5757_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5754_ = (lean_unbox(v_isLower_5738_) as u8);
    v_sz_boxed_5755_ = lean_unbox_usize(v_sz_5740_);
    lean_dec(v_sz_5740_);
    v_i_boxed_5756_ = lean_unbox_usize(v_i_5741_);
    lean_dec(v_i_5741_);
    v_res_5757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_5737_, v_isLower_boxed_5754_, v_as_5739_, v_sz_boxed_5755_, v_i_boxed_5756_, v_b_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
    lean_dec(v___y_5752_);
    lean_dec_ref(v___y_5751_);
    lean_dec(v___y_5750_);
    lean_dec_ref(v___y_5749_);
    lean_dec(v___y_5748_);
    lean_dec_ref(v___y_5747_);
    lean_dec(v___y_5746_);
    lean_dec_ref(v___y_5745_);
    lean_dec(v___y_5744_);
    lean_dec(v___y_5743_);
    lean_dec_ref(v_as_5739_);
    lean_dec(v_____s_5737_);
    return v_res_5757_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(
    mut v_init_5758_: *mut LeanObject,
    mut v_____s_5759_: *mut LeanObject,
    mut v_isLower_5760_: u8,
    mut v_n_5761_: *mut LeanObject,
    mut v_b_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
    mut v___y_5771_: *mut LeanObject,
    mut v___y_5772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5777_: usize = 0;
    let mut v___x_5778_: usize = 0;
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v_fst_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5794_: u8 = 0;
    let mut v_a_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5798_: u8 = 0;
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5802_: u8 = 0;
    let mut v_vs_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5806_: usize = 0;
    let mut v___x_5807_: usize = 0;
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5812_: u8 = 0;
    let mut v_fst_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5823_: u8 = 0;
    let mut v_a_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5827_: u8 = 0;
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5761_) == 0 {
                    v_cs_5774_ = lean_ctor_get(v_n_5761_, 0);
                    v___x_5775_ = lean_box(0);
                    v___x_5776_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5776_, 0, v___x_5775_);
                    lean_ctor_set(v___x_5776_, 1, v_b_5762_);
                    v_sz_5777_ = lean_array_size(v_cs_5774_);
                    v___x_5778_ = 0usize;
                    v___x_5779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_5758_, v_____s_5759_, v_isLower_5760_, v_cs_5774_, v_sz_5777_, v___x_5778_, v___x_5776_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
                    if lean_obj_tag(v___x_5779_) == 0 {
                        v_a_5780_ = lean_ctor_get(v___x_5779_, 0);
                        v_isSharedCheck_5794_ = (!lean_is_exclusive(v___x_5779_)) as u8;
                        if v_isSharedCheck_5794_ == 0 {
                            v___x_5782_ = v___x_5779_;
                            v_isShared_5783_ = v_isSharedCheck_5794_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5780_);
                            lean_dec(v___x_5779_);
                            v___x_5782_ = lean_box(0);
                            v_isShared_5783_ = v_isSharedCheck_5794_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5795_ = lean_ctor_get(v___x_5779_, 0);
                        v_isSharedCheck_5802_ = (!lean_is_exclusive(v___x_5779_)) as u8;
                        if v_isSharedCheck_5802_ == 0 {
                            v___x_5797_ = v___x_5779_;
                            v_isShared_5798_ = v_isSharedCheck_5802_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5795_);
                            lean_dec(v___x_5779_);
                            v___x_5797_ = lean_box(0);
                            v_isShared_5798_ = v_isSharedCheck_5802_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5803_ = lean_ctor_get(v_n_5761_, 0);
                    v___x_5804_ = lean_box(0);
                    v___x_5805_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5805_, 0, v___x_5804_);
                    lean_ctor_set(v___x_5805_, 1, v_b_5762_);
                    v_sz_5806_ = lean_array_size(v_vs_5803_);
                    v___x_5807_ = 0usize;
                    v___x_5808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_5759_, v_isLower_5760_, v_vs_5803_, v_sz_5806_, v___x_5807_, v___x_5805_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
                    if lean_obj_tag(v___x_5808_) == 0 {
                        v_a_5809_ = lean_ctor_get(v___x_5808_, 0);
                        v_isSharedCheck_5823_ = (!lean_is_exclusive(v___x_5808_)) as u8;
                        if v_isSharedCheck_5823_ == 0 {
                            v___x_5811_ = v___x_5808_;
                            v_isShared_5812_ = v_isSharedCheck_5823_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5809_);
                            lean_dec(v___x_5808_);
                            v___x_5811_ = lean_box(0);
                            v_isShared_5812_ = v_isSharedCheck_5823_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5824_ = lean_ctor_get(v___x_5808_, 0);
                        v_isSharedCheck_5831_ = (!lean_is_exclusive(v___x_5808_)) as u8;
                        if v_isSharedCheck_5831_ == 0 {
                            v___x_5826_ = v___x_5808_;
                            v_isShared_5827_ = v_isSharedCheck_5831_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5824_);
                            lean_dec(v___x_5808_);
                            v___x_5826_ = lean_box(0);
                            v_isShared_5827_ = v_isSharedCheck_5831_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5784_ = lean_ctor_get(v_a_5780_, 0);
                if lean_obj_tag(v_fst_5784_) == 0 {
                    v_snd_5785_ = lean_ctor_get(v_a_5780_, 1);
                    lean_inc(v_snd_5785_);
                    lean_dec(v_a_5780_);
                    v___x_5786_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5786_, 0, v_snd_5785_);
                    if v_isShared_5783_ == 0 {
                        lean_ctor_set(v___x_5782_, 0, v___x_5786_);
                        v___x_5788_ = v___x_5782_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5789_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5789_, 0, v___x_5786_);
                        v___x_5788_ = v_reuseFailAlloc_5789_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5784_);
                    lean_dec(v_a_5780_);
                    v_val_5790_ = lean_ctor_get(v_fst_5784_, 0);
                    lean_inc(v_val_5790_);
                    lean_dec_ref_known(v_fst_5784_, 1);
                    if v_isShared_5783_ == 0 {
                        lean_ctor_set(v___x_5782_, 0, v_val_5790_);
                        v___x_5792_ = v___x_5782_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5793_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5793_, 0, v_val_5790_);
                        v___x_5792_ = v_reuseFailAlloc_5793_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5788_;
            }
            3 => {
                return v___x_5792_;
            }
            4 => {
                if v_isShared_5798_ == 0 {
                    v___x_5800_ = v___x_5797_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5801_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5801_, 0, v_a_5795_);
                    v___x_5800_ = v_reuseFailAlloc_5801_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5800_;
            }
            6 => {
                v_fst_5813_ = lean_ctor_get(v_a_5809_, 0);
                if lean_obj_tag(v_fst_5813_) == 0 {
                    v_snd_5814_ = lean_ctor_get(v_a_5809_, 1);
                    lean_inc(v_snd_5814_);
                    lean_dec(v_a_5809_);
                    v___x_5815_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5815_, 0, v_snd_5814_);
                    if v_isShared_5812_ == 0 {
                        lean_ctor_set(v___x_5811_, 0, v___x_5815_);
                        v___x_5817_ = v___x_5811_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5818_, 0, v___x_5815_);
                        v___x_5817_ = v_reuseFailAlloc_5818_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5813_);
                    lean_dec(v_a_5809_);
                    v_val_5819_ = lean_ctor_get(v_fst_5813_, 0);
                    lean_inc(v_val_5819_);
                    lean_dec_ref_known(v_fst_5813_, 1);
                    if v_isShared_5812_ == 0 {
                        lean_ctor_set(v___x_5811_, 0, v_val_5819_);
                        v___x_5821_ = v___x_5811_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5822_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_val_5819_);
                        v___x_5821_ = v_reuseFailAlloc_5822_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5817_;
            }
            8 => {
                return v___x_5821_;
            }
            9 => {
                if v_isShared_5827_ == 0 {
                    v___x_5829_ = v___x_5826_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5830_, 0, v_a_5824_);
                    v___x_5829_ = v_reuseFailAlloc_5830_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(
    mut v_init_5832_: *mut LeanObject,
    mut v_____s_5833_: *mut LeanObject,
    mut v_isLower_5834_: u8,
    mut v_as_5835_: *mut LeanObject,
    mut v_sz_5836_: usize,
    mut v_i_5837_: usize,
    mut v_b_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
    mut v___y_5847_: *mut LeanObject,
    mut v___y_5848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5850_: u8 = 0;
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5855_: u8 = 0;
    let mut v_a_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5861_: u8 = 0;
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: usize = 0;
    let mut v___x_5874_: usize = 0;
    let mut v_reuseFailAlloc_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5877_: u8 = 0;
    let mut v_a_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5881_: u8 = 0;
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5885_: u8 = 0;
    let mut v_isSharedCheck_5886_: u8 = 0;
    let mut v_unused_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5850_ = lean_usize_dec_lt(v_i_5837_, v_sz_5836_);
                if v___x_5850_ == 0 {
                    v___x_5851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5851_, 0, v_b_5838_);
                    return v___x_5851_;
                } else {
                    v_snd_5852_ = lean_ctor_get(v_b_5838_, 1);
                    v_isSharedCheck_5886_ = (!lean_is_exclusive(v_b_5838_)) as u8;
                    if v_isSharedCheck_5886_ == 0 {
                        v_unused_5887_ = lean_ctor_get(v_b_5838_, 0);
                        lean_dec(v_unused_5887_);
                        v___x_5854_ = v_b_5838_;
                        v_isShared_5855_ = v_isSharedCheck_5886_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5852_);
                        lean_dec(v_b_5838_);
                        v___x_5854_ = lean_box(0);
                        v_isShared_5855_ = v_isSharedCheck_5886_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5856_ = lean_array_uget_borrowed(v_as_5835_, v_i_5837_);
                lean_inc(v_snd_5852_);
                v___x_5857_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_5832_, v_____s_5833_, v_isLower_5834_, v_a_5856_, v_snd_5852_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_);
                if lean_obj_tag(v___x_5857_) == 0 {
                    v_a_5858_ = lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5877_ = (!lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5877_ == 0 {
                        v___x_5860_ = v___x_5857_;
                        v_isShared_5861_ = v_isSharedCheck_5877_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5858_);
                        lean_dec(v___x_5857_);
                        v___x_5860_ = lean_box(0);
                        v_isShared_5861_ = v_isSharedCheck_5877_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5854_);
                    lean_dec(v_snd_5852_);
                    v_a_5878_ = lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5885_ = (!lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5885_ == 0 {
                        v___x_5880_ = v___x_5857_;
                        v_isShared_5881_ = v_isSharedCheck_5885_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5878_);
                        lean_dec(v___x_5857_);
                        v___x_5880_ = lean_box(0);
                        v_isShared_5881_ = v_isSharedCheck_5885_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5858_) == 0 {
                    v___x_5862_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5862_, 0, v_a_5858_);
                    if v_isShared_5855_ == 0 {
                        lean_ctor_set(v___x_5854_, 0, v___x_5862_);
                        v___x_5864_ = v___x_5854_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5862_);
                        lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_snd_5852_);
                        v___x_5864_ = v_reuseFailAlloc_5868_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5860_);
                    lean_dec(v_snd_5852_);
                    v_a_5869_ = lean_ctor_get(v_a_5858_, 0);
                    lean_inc(v_a_5869_);
                    lean_dec_ref_known(v_a_5858_, 1);
                    v___x_5870_ = lean_box(0);
                    if v_isShared_5855_ == 0 {
                        lean_ctor_set(v___x_5854_, 1, v_a_5869_);
                        lean_ctor_set(v___x_5854_, 0, v___x_5870_);
                        v___x_5872_ = v___x_5854_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5876_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5876_, 0, v___x_5870_);
                        lean_ctor_set(v_reuseFailAlloc_5876_, 1, v_a_5869_);
                        v___x_5872_ = v_reuseFailAlloc_5876_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5861_ == 0 {
                    lean_ctor_set(v___x_5860_, 0, v___x_5864_);
                    v___x_5866_ = v___x_5860_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5867_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5867_, 0, v___x_5864_);
                    v___x_5866_ = v_reuseFailAlloc_5867_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5866_;
            }
            5 => {
                v___x_5873_ = 1usize;
                v___x_5874_ = lean_usize_add(v_i_5837_, v___x_5873_);
                v_i_5837_ = v___x_5874_;
                v_b_5838_ = v___x_5872_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5881_ == 0 {
                    v___x_5883_ = v___x_5880_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5884_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5884_, 0, v_a_5878_);
                    v___x_5883_ = v_reuseFailAlloc_5884_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_5888_: *mut LeanObject = *_args.add(0);
    let mut v_____s_5889_: *mut LeanObject = *_args.add(1);
    let mut v_isLower_5890_: *mut LeanObject = *_args.add(2);
    let mut v_as_5891_: *mut LeanObject = *_args.add(3);
    let mut v_sz_5892_: *mut LeanObject = *_args.add(4);
    let mut v_i_5893_: *mut LeanObject = *_args.add(5);
    let mut v_b_5894_: *mut LeanObject = *_args.add(6);
    let mut v___y_5895_: *mut LeanObject = *_args.add(7);
    let mut v___y_5896_: *mut LeanObject = *_args.add(8);
    let mut v___y_5897_: *mut LeanObject = *_args.add(9);
    let mut v___y_5898_: *mut LeanObject = *_args.add(10);
    let mut v___y_5899_: *mut LeanObject = *_args.add(11);
    let mut v___y_5900_: *mut LeanObject = *_args.add(12);
    let mut v___y_5901_: *mut LeanObject = *_args.add(13);
    let mut v___y_5902_: *mut LeanObject = *_args.add(14);
    let mut v___y_5903_: *mut LeanObject = *_args.add(15);
    let mut v___y_5904_: *mut LeanObject = *_args.add(16);
    let mut v___y_5905_: *mut LeanObject = *_args.add(17);
    let mut v_isLower_boxed_5906_: u8 = 0;
    let mut v_sz_boxed_5907_: usize = 0;
    let mut v_i_boxed_5908_: usize = 0;
    let mut v_res_5909_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5906_ = (lean_unbox(v_isLower_5890_) as u8);
    v_sz_boxed_5907_ = lean_unbox_usize(v_sz_5892_);
    lean_dec(v_sz_5892_);
    v_i_boxed_5908_ = lean_unbox_usize(v_i_5893_);
    lean_dec(v_i_5893_);
    v_res_5909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_5888_, v_____s_5889_, v_isLower_boxed_5906_, v_as_5891_, v_sz_boxed_5907_, v_i_boxed_5908_, v_b_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_);
    lean_dec(v___y_5904_);
    lean_dec_ref(v___y_5903_);
    lean_dec(v___y_5902_);
    lean_dec_ref(v___y_5901_);
    lean_dec(v___y_5900_);
    lean_dec_ref(v___y_5899_);
    lean_dec(v___y_5898_);
    lean_dec_ref(v___y_5897_);
    lean_dec(v___y_5896_);
    lean_dec(v___y_5895_);
    lean_dec_ref(v_as_5891_);
    lean_dec(v_____s_5889_);
    return v_res_5909_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1___boxed(
    mut v_init_5910_: *mut LeanObject,
    mut v_____s_5911_: *mut LeanObject,
    mut v_isLower_5912_: *mut LeanObject,
    mut v_n_5913_: *mut LeanObject,
    mut v_b_5914_: *mut LeanObject,
    mut v___y_5915_: *mut LeanObject,
    mut v___y_5916_: *mut LeanObject,
    mut v___y_5917_: *mut LeanObject,
    mut v___y_5918_: *mut LeanObject,
    mut v___y_5919_: *mut LeanObject,
    mut v___y_5920_: *mut LeanObject,
    mut v___y_5921_: *mut LeanObject,
    mut v___y_5922_: *mut LeanObject,
    mut v___y_5923_: *mut LeanObject,
    mut v___y_5924_: *mut LeanObject,
    mut v___y_5925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_5926_: u8 = 0;
    let mut v_res_5927_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5926_ = (lean_unbox(v_isLower_5912_) as u8);
    v_res_5927_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_5910_, v_____s_5911_, v_isLower_boxed_5926_, v_n_5913_, v_b_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_);
    lean_dec(v___y_5924_);
    lean_dec_ref(v___y_5923_);
    lean_dec(v___y_5922_);
    lean_dec_ref(v___y_5921_);
    lean_dec(v___y_5920_);
    lean_dec_ref(v___y_5919_);
    lean_dec(v___y_5918_);
    lean_dec_ref(v___y_5917_);
    lean_dec(v___y_5916_);
    lean_dec(v___y_5915_);
    lean_dec_ref(v_n_5913_);
    lean_dec(v_____s_5911_);
    return v_res_5927_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(
    mut v_____s_5928_: *mut LeanObject,
    mut v_isLower_5929_: u8,
    mut v_t_5930_: *mut LeanObject,
    mut v_init_5931_: *mut LeanObject,
    mut v___y_5932_: *mut LeanObject,
    mut v___y_5933_: *mut LeanObject,
    mut v___y_5934_: *mut LeanObject,
    mut v___y_5935_: *mut LeanObject,
    mut v___y_5936_: *mut LeanObject,
    mut v___y_5937_: *mut LeanObject,
    mut v___y_5938_: *mut LeanObject,
    mut v___y_5939_: *mut LeanObject,
    mut v___y_5940_: *mut LeanObject,
    mut v___y_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5949_: u8 = 0;
    let mut v_a_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5957_: usize = 0;
    let mut v___x_5958_: usize = 0;
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5963_: u8 = 0;
    let mut v_fst_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut v_a_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5977_: u8 = 0;
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v_isSharedCheck_5982_: u8 = 0;
    let mut v_a_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5986_: u8 = 0;
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5943_ = lean_ctor_get(v_t_5930_, 0);
                v_tail_5944_ = lean_ctor_get(v_t_5930_, 1);
                v___x_5945_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__1(v_init_5931_, v_____s_5928_, v_isLower_5929_, v_root_5943_, v_init_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_);
                if lean_obj_tag(v___x_5945_) == 0 {
                    v_a_5946_ = lean_ctor_get(v___x_5945_, 0);
                    v_isSharedCheck_5982_ = (!lean_is_exclusive(v___x_5945_)) as u8;
                    if v_isSharedCheck_5982_ == 0 {
                        v___x_5948_ = v___x_5945_;
                        v_isShared_5949_ = v_isSharedCheck_5982_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5946_);
                        lean_dec(v___x_5945_);
                        v___x_5948_ = lean_box(0);
                        v_isShared_5949_ = v_isSharedCheck_5982_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5983_ = lean_ctor_get(v___x_5945_, 0);
                    v_isSharedCheck_5990_ = (!lean_is_exclusive(v___x_5945_)) as u8;
                    if v_isSharedCheck_5990_ == 0 {
                        v___x_5985_ = v___x_5945_;
                        v_isShared_5986_ = v_isSharedCheck_5990_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5983_);
                        lean_dec(v___x_5945_);
                        v___x_5985_ = lean_box(0);
                        v_isShared_5986_ = v_isSharedCheck_5990_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5946_) == 0 {
                    v_a_5950_ = lean_ctor_get(v_a_5946_, 0);
                    lean_inc(v_a_5950_);
                    lean_dec_ref_known(v_a_5946_, 1);
                    if v_isShared_5949_ == 0 {
                        lean_ctor_set(v___x_5948_, 0, v_a_5950_);
                        v___x_5952_ = v___x_5948_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5953_, 0, v_a_5950_);
                        v___x_5952_ = v_reuseFailAlloc_5953_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5948_);
                    v_a_5954_ = lean_ctor_get(v_a_5946_, 0);
                    lean_inc(v_a_5954_);
                    lean_dec_ref_known(v_a_5946_, 1);
                    v___x_5955_ = lean_box(0);
                    v___x_5956_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5956_, 0, v___x_5955_);
                    lean_ctor_set(v___x_5956_, 1, v_a_5954_);
                    v_sz_5957_ = lean_array_size(v_tail_5944_);
                    v___x_5958_ = 0usize;
                    v___x_5959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1_spec__2(v_____s_5928_, v_isLower_5929_, v_tail_5944_, v_sz_5957_, v___x_5958_, v___x_5956_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_);
                    if lean_obj_tag(v___x_5959_) == 0 {
                        v_a_5960_ = lean_ctor_get(v___x_5959_, 0);
                        v_isSharedCheck_5973_ = (!lean_is_exclusive(v___x_5959_)) as u8;
                        if v_isSharedCheck_5973_ == 0 {
                            v___x_5962_ = v___x_5959_;
                            v_isShared_5963_ = v_isSharedCheck_5973_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5960_);
                            lean_dec(v___x_5959_);
                            v___x_5962_ = lean_box(0);
                            v_isShared_5963_ = v_isSharedCheck_5973_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5974_ = lean_ctor_get(v___x_5959_, 0);
                        v_isSharedCheck_5981_ = (!lean_is_exclusive(v___x_5959_)) as u8;
                        if v_isSharedCheck_5981_ == 0 {
                            v___x_5976_ = v___x_5959_;
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5974_);
                            lean_dec(v___x_5959_);
                            v___x_5976_ = lean_box(0);
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5952_;
            }
            3 => {
                v_fst_5964_ = lean_ctor_get(v_a_5960_, 0);
                if lean_obj_tag(v_fst_5964_) == 0 {
                    v_snd_5965_ = lean_ctor_get(v_a_5960_, 1);
                    lean_inc(v_snd_5965_);
                    lean_dec(v_a_5960_);
                    if v_isShared_5963_ == 0 {
                        lean_ctor_set(v___x_5962_, 0, v_snd_5965_);
                        v___x_5967_ = v___x_5962_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5968_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5968_, 0, v_snd_5965_);
                        v___x_5967_ = v_reuseFailAlloc_5968_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5964_);
                    lean_dec(v_a_5960_);
                    v_val_5969_ = lean_ctor_get(v_fst_5964_, 0);
                    lean_inc(v_val_5969_);
                    lean_dec_ref_known(v_fst_5964_, 1);
                    if v_isShared_5963_ == 0 {
                        lean_ctor_set(v___x_5962_, 0, v_val_5969_);
                        v___x_5971_ = v___x_5962_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_val_5969_);
                        v___x_5971_ = v_reuseFailAlloc_5972_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5967_;
            }
            5 => {
                return v___x_5971_;
            }
            6 => {
                if v_isShared_5977_ == 0 {
                    v___x_5979_ = v___x_5976_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
                    v___x_5979_ = v_reuseFailAlloc_5980_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5979_;
            }
            8 => {
                if v_isShared_5986_ == 0 {
                    v___x_5988_ = v___x_5985_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
                    v___x_5988_ = v_reuseFailAlloc_5989_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1___boxed(
    mut v_____s_5991_: *mut LeanObject,
    mut v_isLower_5992_: *mut LeanObject,
    mut v_t_5993_: *mut LeanObject,
    mut v_init_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
    mut v___y_5996_: *mut LeanObject,
    mut v___y_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
    mut v___y_6000_: *mut LeanObject,
    mut v___y_6001_: *mut LeanObject,
    mut v___y_6002_: *mut LeanObject,
    mut v___y_6003_: *mut LeanObject,
    mut v___y_6004_: *mut LeanObject,
    mut v___y_6005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_6006_: u8 = 0;
    let mut v_res_6007_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6006_ = (lean_unbox(v_isLower_5992_) as u8);
    v_res_6007_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(
            v_____s_5991_,
            v_isLower_boxed_6006_,
            v_t_5993_,
            v_init_5994_,
            v___y_5995_,
            v___y_5996_,
            v___y_5997_,
            v___y_5998_,
            v___y_5999_,
            v___y_6000_,
            v___y_6001_,
            v___y_6002_,
            v___y_6003_,
            v___y_6004_,
        );
    lean_dec(v___y_6004_);
    lean_dec_ref(v___y_6003_);
    lean_dec(v___y_6002_);
    lean_dec_ref(v___y_6001_);
    lean_dec(v___y_6000_);
    lean_dec_ref(v___y_5999_);
    lean_dec(v___y_5998_);
    lean_dec_ref(v___y_5997_);
    lean_dec(v___y_5996_);
    lean_dec(v___y_5995_);
    lean_dec_ref(v_t_5993_);
    lean_dec(v_____s_5991_);
    return v_res_6007_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(
    mut v_isLower_6008_: u8,
    mut v_as_6009_: *mut LeanObject,
    mut v_sz_6010_: usize,
    mut v_i_6011_: usize,
    mut v_b_6012_: *mut LeanObject,
    mut v___y_6013_: *mut LeanObject,
    mut v___y_6014_: *mut LeanObject,
    mut v___y_6015_: *mut LeanObject,
    mut v___y_6016_: *mut LeanObject,
    mut v___y_6017_: *mut LeanObject,
    mut v___y_6018_: *mut LeanObject,
    mut v___y_6019_: *mut LeanObject,
    mut v___y_6020_: *mut LeanObject,
    mut v___y_6021_: *mut LeanObject,
    mut v___y_6022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6024_: u8 = 0;
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6029_: u8 = 0;
    let mut v_a_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: usize = 0;
    let mut v___x_6039_: usize = 0;
    let mut v_reuseFailAlloc_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6045_: u8 = 0;
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6049_: u8 = 0;
    let mut v_isSharedCheck_6050_: u8 = 0;
    let mut v_unused_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6024_ = lean_usize_dec_lt(v_i_6011_, v_sz_6010_);
                if v___x_6024_ == 0 {
                    v___x_6025_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6025_, 0, v_b_6012_);
                    return v___x_6025_;
                } else {
                    v_snd_6026_ = lean_ctor_get(v_b_6012_, 1);
                    v_isSharedCheck_6050_ = (!lean_is_exclusive(v_b_6012_)) as u8;
                    if v_isSharedCheck_6050_ == 0 {
                        v_unused_6051_ = lean_ctor_get(v_b_6012_, 0);
                        lean_dec(v_unused_6051_);
                        v___x_6028_ = v_b_6012_;
                        v_isShared_6029_ = v_isSharedCheck_6050_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6026_);
                        lean_dec(v_b_6012_);
                        v___x_6028_ = lean_box(0);
                        v_isShared_6029_ = v_isSharedCheck_6050_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6030_ = lean_array_uget_borrowed(v_as_6009_, v_i_6011_);
                v___x_6031_ = lean_box(0);
                v___x_6032_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_6026_, v_isLower_6008_, v_a_6030_, v___x_6031_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_);
                if lean_obj_tag(v___x_6032_) == 0 {
                    lean_dec_ref_known(v___x_6032_, 1);
                    v___x_6033_ = lean_box(0);
                    v___x_6034_ = lean_unsigned_to_nat(1);
                    v___x_6035_ = lean_nat_add(v_snd_6026_, v___x_6034_);
                    lean_dec(v_snd_6026_);
                    if v_isShared_6029_ == 0 {
                        lean_ctor_set(v___x_6028_, 1, v___x_6035_);
                        lean_ctor_set(v___x_6028_, 0, v___x_6033_);
                        v___x_6037_ = v___x_6028_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6041_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6041_, 0, v___x_6033_);
                        lean_ctor_set(v_reuseFailAlloc_6041_, 1, v___x_6035_);
                        v___x_6037_ = v_reuseFailAlloc_6041_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6028_);
                    lean_dec(v_snd_6026_);
                    v_a_6042_ = lean_ctor_get(v___x_6032_, 0);
                    v_isSharedCheck_6049_ = (!lean_is_exclusive(v___x_6032_)) as u8;
                    if v_isSharedCheck_6049_ == 0 {
                        v___x_6044_ = v___x_6032_;
                        v_isShared_6045_ = v_isSharedCheck_6049_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6042_);
                        lean_dec(v___x_6032_);
                        v___x_6044_ = lean_box(0);
                        v_isShared_6045_ = v_isSharedCheck_6049_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6038_ = 1usize;
                v___x_6039_ = lean_usize_add(v_i_6011_, v___x_6038_);
                v_i_6011_ = v___x_6039_;
                v_b_6012_ = v___x_6037_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6045_ == 0 {
                    v___x_6047_ = v___x_6044_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_a_6042_);
                    v___x_6047_ = v_reuseFailAlloc_6048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(
    mut v_isLower_6052_: *mut LeanObject,
    mut v_as_6053_: *mut LeanObject,
    mut v_sz_6054_: *mut LeanObject,
    mut v_i_6055_: *mut LeanObject,
    mut v_b_6056_: *mut LeanObject,
    mut v___y_6057_: *mut LeanObject,
    mut v___y_6058_: *mut LeanObject,
    mut v___y_6059_: *mut LeanObject,
    mut v___y_6060_: *mut LeanObject,
    mut v___y_6061_: *mut LeanObject,
    mut v___y_6062_: *mut LeanObject,
    mut v___y_6063_: *mut LeanObject,
    mut v___y_6064_: *mut LeanObject,
    mut v___y_6065_: *mut LeanObject,
    mut v___y_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_6068_: u8 = 0;
    let mut v_sz_boxed_6069_: usize = 0;
    let mut v_i_boxed_6070_: usize = 0;
    let mut v_res_6071_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6068_ = (lean_unbox(v_isLower_6052_) as u8);
    v_sz_boxed_6069_ = lean_unbox_usize(v_sz_6054_);
    lean_dec(v_sz_6054_);
    v_i_boxed_6070_ = lean_unbox_usize(v_i_6055_);
    lean_dec(v_i_6055_);
    v_res_6071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_6068_, v_as_6053_, v_sz_boxed_6069_, v_i_boxed_6070_, v_b_6056_, v___y_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_);
    lean_dec(v___y_6066_);
    lean_dec_ref(v___y_6065_);
    lean_dec(v___y_6064_);
    lean_dec_ref(v___y_6063_);
    lean_dec(v___y_6062_);
    lean_dec_ref(v___y_6061_);
    lean_dec(v___y_6060_);
    lean_dec_ref(v___y_6059_);
    lean_dec(v___y_6058_);
    lean_dec(v___y_6057_);
    lean_dec_ref(v_as_6053_);
    return v_res_6071_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(
    mut v_isLower_6072_: u8,
    mut v_as_6073_: *mut LeanObject,
    mut v_sz_6074_: usize,
    mut v_i_6075_: usize,
    mut v_b_6076_: *mut LeanObject,
    mut v___y_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
    mut v___y_6079_: *mut LeanObject,
    mut v___y_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
    mut v___y_6082_: *mut LeanObject,
    mut v___y_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
    mut v___y_6086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6093_: u8 = 0;
    let mut v_a_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: usize = 0;
    let mut v___x_6103_: usize = 0;
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6109_: u8 = 0;
    let mut v___x_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6113_: u8 = 0;
    let mut v_isSharedCheck_6114_: u8 = 0;
    let mut v_unused_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6088_ = lean_usize_dec_lt(v_i_6075_, v_sz_6074_);
                if v___x_6088_ == 0 {
                    v___x_6089_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6089_, 0, v_b_6076_);
                    return v___x_6089_;
                } else {
                    v_snd_6090_ = lean_ctor_get(v_b_6076_, 1);
                    v_isSharedCheck_6114_ = (!lean_is_exclusive(v_b_6076_)) as u8;
                    if v_isSharedCheck_6114_ == 0 {
                        v_unused_6115_ = lean_ctor_get(v_b_6076_, 0);
                        lean_dec(v_unused_6115_);
                        v___x_6092_ = v_b_6076_;
                        v_isShared_6093_ = v_isSharedCheck_6114_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6090_);
                        lean_dec(v_b_6076_);
                        v___x_6092_ = lean_box(0);
                        v_isShared_6093_ = v_isSharedCheck_6114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6094_ = lean_array_uget_borrowed(v_as_6073_, v_i_6075_);
                v___x_6095_ = lean_box(0);
                v___x_6096_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_6090_, v_isLower_6072_, v_a_6094_, v___x_6095_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_, v___y_6085_, v___y_6086_);
                if lean_obj_tag(v___x_6096_) == 0 {
                    lean_dec_ref_known(v___x_6096_, 1);
                    v___x_6097_ = lean_box(0);
                    v___x_6098_ = lean_unsigned_to_nat(1);
                    v___x_6099_ = lean_nat_add(v_snd_6090_, v___x_6098_);
                    lean_dec(v_snd_6090_);
                    if v_isShared_6093_ == 0 {
                        lean_ctor_set(v___x_6092_, 1, v___x_6099_);
                        lean_ctor_set(v___x_6092_, 0, v___x_6097_);
                        v___x_6101_ = v___x_6092_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6105_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6097_);
                        lean_ctor_set(v_reuseFailAlloc_6105_, 1, v___x_6099_);
                        v___x_6101_ = v_reuseFailAlloc_6105_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6092_);
                    lean_dec(v_snd_6090_);
                    v_a_6106_ = lean_ctor_get(v___x_6096_, 0);
                    v_isSharedCheck_6113_ = (!lean_is_exclusive(v___x_6096_)) as u8;
                    if v_isSharedCheck_6113_ == 0 {
                        v___x_6108_ = v___x_6096_;
                        v_isShared_6109_ = v_isSharedCheck_6113_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6106_);
                        lean_dec(v___x_6096_);
                        v___x_6108_ = lean_box(0);
                        v_isShared_6109_ = v_isSharedCheck_6113_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6102_ = 1usize;
                v___x_6103_ = lean_usize_add(v_i_6075_, v___x_6102_);
                v___x_6104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_6072_, v_as_6073_, v_sz_6074_, v___x_6103_, v___x_6101_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_, v___y_6085_, v___y_6086_);
                return v___x_6104_;
            }
            3 => {
                if v_isShared_6109_ == 0 {
                    v___x_6111_ = v___x_6108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6112_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_a_6106_);
                    v___x_6111_ = v_reuseFailAlloc_6112_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5___boxed(
    mut v_isLower_6116_: *mut LeanObject,
    mut v_as_6117_: *mut LeanObject,
    mut v_sz_6118_: *mut LeanObject,
    mut v_i_6119_: *mut LeanObject,
    mut v_b_6120_: *mut LeanObject,
    mut v___y_6121_: *mut LeanObject,
    mut v___y_6122_: *mut LeanObject,
    mut v___y_6123_: *mut LeanObject,
    mut v___y_6124_: *mut LeanObject,
    mut v___y_6125_: *mut LeanObject,
    mut v___y_6126_: *mut LeanObject,
    mut v___y_6127_: *mut LeanObject,
    mut v___y_6128_: *mut LeanObject,
    mut v___y_6129_: *mut LeanObject,
    mut v___y_6130_: *mut LeanObject,
    mut v___y_6131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_6132_: u8 = 0;
    let mut v_sz_boxed_6133_: usize = 0;
    let mut v_i_boxed_6134_: usize = 0;
    let mut v_res_6135_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6132_ = (lean_unbox(v_isLower_6116_) as u8);
    v_sz_boxed_6133_ = lean_unbox_usize(v_sz_6118_);
    lean_dec(v_sz_6118_);
    v_i_boxed_6134_ = lean_unbox_usize(v_i_6119_);
    lean_dec(v_i_6119_);
    v_res_6135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_6132_, v_as_6117_, v_sz_boxed_6133_, v_i_boxed_6134_, v_b_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_);
    lean_dec(v___y_6130_);
    lean_dec_ref(v___y_6129_);
    lean_dec(v___y_6128_);
    lean_dec_ref(v___y_6127_);
    lean_dec(v___y_6126_);
    lean_dec_ref(v___y_6125_);
    lean_dec(v___y_6124_);
    lean_dec_ref(v___y_6123_);
    lean_dec(v___y_6122_);
    lean_dec(v___y_6121_);
    lean_dec_ref(v_as_6117_);
    return v_res_6135_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(
    mut v_isLower_6136_: u8,
    mut v_as_6137_: *mut LeanObject,
    mut v_sz_6138_: usize,
    mut v_i_6139_: usize,
    mut v_b_6140_: *mut LeanObject,
    mut v___y_6141_: *mut LeanObject,
    mut v___y_6142_: *mut LeanObject,
    mut v___y_6143_: *mut LeanObject,
    mut v___y_6144_: *mut LeanObject,
    mut v___y_6145_: *mut LeanObject,
    mut v___y_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6152_: u8 = 0;
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6157_: u8 = 0;
    let mut v_a_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: usize = 0;
    let mut v___x_6167_: usize = 0;
    let mut v_reuseFailAlloc_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6173_: u8 = 0;
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6177_: u8 = 0;
    let mut v_isSharedCheck_6178_: u8 = 0;
    let mut v_unused_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6152_ = lean_usize_dec_lt(v_i_6139_, v_sz_6138_);
                if v___x_6152_ == 0 {
                    v___x_6153_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6153_, 0, v_b_6140_);
                    return v___x_6153_;
                } else {
                    v_snd_6154_ = lean_ctor_get(v_b_6140_, 1);
                    v_isSharedCheck_6178_ = (!lean_is_exclusive(v_b_6140_)) as u8;
                    if v_isSharedCheck_6178_ == 0 {
                        v_unused_6179_ = lean_ctor_get(v_b_6140_, 0);
                        lean_dec(v_unused_6179_);
                        v___x_6156_ = v_b_6140_;
                        v_isShared_6157_ = v_isSharedCheck_6178_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6154_);
                        lean_dec(v_b_6140_);
                        v___x_6156_ = lean_box(0);
                        v_isShared_6157_ = v_isSharedCheck_6178_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6158_ = lean_array_uget_borrowed(v_as_6137_, v_i_6139_);
                v___x_6159_ = lean_box(0);
                v___x_6160_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_6154_, v_isLower_6136_, v_a_6158_, v___x_6159_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
                if lean_obj_tag(v___x_6160_) == 0 {
                    lean_dec_ref_known(v___x_6160_, 1);
                    v___x_6161_ = lean_box(0);
                    v___x_6162_ = lean_unsigned_to_nat(1);
                    v___x_6163_ = lean_nat_add(v_snd_6154_, v___x_6162_);
                    lean_dec(v_snd_6154_);
                    if v_isShared_6157_ == 0 {
                        lean_ctor_set(v___x_6156_, 1, v___x_6163_);
                        lean_ctor_set(v___x_6156_, 0, v___x_6161_);
                        v___x_6165_ = v___x_6156_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6161_);
                        lean_ctor_set(v_reuseFailAlloc_6169_, 1, v___x_6163_);
                        v___x_6165_ = v_reuseFailAlloc_6169_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6156_);
                    lean_dec(v_snd_6154_);
                    v_a_6170_ = lean_ctor_get(v___x_6160_, 0);
                    v_isSharedCheck_6177_ = (!lean_is_exclusive(v___x_6160_)) as u8;
                    if v_isSharedCheck_6177_ == 0 {
                        v___x_6172_ = v___x_6160_;
                        v_isShared_6173_ = v_isSharedCheck_6177_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6170_);
                        lean_dec(v___x_6160_);
                        v___x_6172_ = lean_box(0);
                        v_isShared_6173_ = v_isSharedCheck_6177_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6166_ = 1usize;
                v___x_6167_ = lean_usize_add(v_i_6139_, v___x_6166_);
                v_i_6139_ = v___x_6167_;
                v_b_6140_ = v___x_6165_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6173_ == 0 {
                    v___x_6175_ = v___x_6172_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6176_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6176_, 0, v_a_6170_);
                    v___x_6175_ = v_reuseFailAlloc_6176_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(
    mut v_isLower_6180_: *mut LeanObject,
    mut v_as_6181_: *mut LeanObject,
    mut v_sz_6182_: *mut LeanObject,
    mut v_i_6183_: *mut LeanObject,
    mut v_b_6184_: *mut LeanObject,
    mut v___y_6185_: *mut LeanObject,
    mut v___y_6186_: *mut LeanObject,
    mut v___y_6187_: *mut LeanObject,
    mut v___y_6188_: *mut LeanObject,
    mut v___y_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
    mut v___y_6191_: *mut LeanObject,
    mut v___y_6192_: *mut LeanObject,
    mut v___y_6193_: *mut LeanObject,
    mut v___y_6194_: *mut LeanObject,
    mut v___y_6195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_6196_: u8 = 0;
    let mut v_sz_boxed_6197_: usize = 0;
    let mut v_i_boxed_6198_: usize = 0;
    let mut v_res_6199_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6196_ = (lean_unbox(v_isLower_6180_) as u8);
    v_sz_boxed_6197_ = lean_unbox_usize(v_sz_6182_);
    lean_dec(v_sz_6182_);
    v_i_boxed_6198_ = lean_unbox_usize(v_i_6183_);
    lean_dec(v_i_6183_);
    v_res_6199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_6196_, v_as_6181_, v_sz_boxed_6197_, v_i_boxed_6198_, v_b_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_);
    lean_dec(v___y_6194_);
    lean_dec_ref(v___y_6193_);
    lean_dec(v___y_6192_);
    lean_dec_ref(v___y_6191_);
    lean_dec(v___y_6190_);
    lean_dec_ref(v___y_6189_);
    lean_dec(v___y_6188_);
    lean_dec_ref(v___y_6187_);
    lean_dec(v___y_6186_);
    lean_dec(v___y_6185_);
    lean_dec_ref(v_as_6181_);
    return v_res_6199_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(
    mut v_isLower_6200_: u8,
    mut v_as_6201_: *mut LeanObject,
    mut v_sz_6202_: usize,
    mut v_i_6203_: usize,
    mut v_b_6204_: *mut LeanObject,
    mut v___y_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
    mut v___y_6207_: *mut LeanObject,
    mut v___y_6208_: *mut LeanObject,
    mut v___y_6209_: *mut LeanObject,
    mut v___y_6210_: *mut LeanObject,
    mut v___y_6211_: *mut LeanObject,
    mut v___y_6212_: *mut LeanObject,
    mut v___y_6213_: *mut LeanObject,
    mut v___y_6214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6216_: u8 = 0;
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6221_: u8 = 0;
    let mut v_a_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: usize = 0;
    let mut v___x_6231_: usize = 0;
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6237_: u8 = 0;
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6241_: u8 = 0;
    let mut v_isSharedCheck_6242_: u8 = 0;
    let mut v_unused_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6216_ = lean_usize_dec_lt(v_i_6203_, v_sz_6202_);
                if v___x_6216_ == 0 {
                    v___x_6217_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6217_, 0, v_b_6204_);
                    return v___x_6217_;
                } else {
                    v_snd_6218_ = lean_ctor_get(v_b_6204_, 1);
                    v_isSharedCheck_6242_ = (!lean_is_exclusive(v_b_6204_)) as u8;
                    if v_isSharedCheck_6242_ == 0 {
                        v_unused_6243_ = lean_ctor_get(v_b_6204_, 0);
                        lean_dec(v_unused_6243_);
                        v___x_6220_ = v_b_6204_;
                        v_isShared_6221_ = v_isSharedCheck_6242_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6218_);
                        lean_dec(v_b_6204_);
                        v___x_6220_ = lean_box(0);
                        v_isShared_6221_ = v_isSharedCheck_6242_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6222_ = lean_array_uget_borrowed(v_as_6201_, v_i_6203_);
                v___x_6223_ = lean_box(0);
                v___x_6224_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__1(v_snd_6218_, v_isLower_6200_, v_a_6222_, v___x_6223_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_, v___y_6214_);
                if lean_obj_tag(v___x_6224_) == 0 {
                    lean_dec_ref_known(v___x_6224_, 1);
                    v___x_6225_ = lean_box(0);
                    v___x_6226_ = lean_unsigned_to_nat(1);
                    v___x_6227_ = lean_nat_add(v_snd_6218_, v___x_6226_);
                    lean_dec(v_snd_6218_);
                    if v_isShared_6221_ == 0 {
                        lean_ctor_set(v___x_6220_, 1, v___x_6227_);
                        lean_ctor_set(v___x_6220_, 0, v___x_6225_);
                        v___x_6229_ = v___x_6220_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6233_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6233_, 0, v___x_6225_);
                        lean_ctor_set(v_reuseFailAlloc_6233_, 1, v___x_6227_);
                        v___x_6229_ = v_reuseFailAlloc_6233_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6220_);
                    lean_dec(v_snd_6218_);
                    v_a_6234_ = lean_ctor_get(v___x_6224_, 0);
                    v_isSharedCheck_6241_ = (!lean_is_exclusive(v___x_6224_)) as u8;
                    if v_isSharedCheck_6241_ == 0 {
                        v___x_6236_ = v___x_6224_;
                        v_isShared_6237_ = v_isSharedCheck_6241_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6234_);
                        lean_dec(v___x_6224_);
                        v___x_6236_ = lean_box(0);
                        v_isShared_6237_ = v_isSharedCheck_6241_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6230_ = 1usize;
                v___x_6231_ = lean_usize_add(v_i_6203_, v___x_6230_);
                v___x_6232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_6200_, v_as_6201_, v_sz_6202_, v___x_6231_, v___x_6229_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_, v___y_6214_);
                return v___x_6232_;
            }
            3 => {
                if v_isShared_6237_ == 0 {
                    v___x_6239_ = v___x_6236_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
                    v___x_6239_ = v_reuseFailAlloc_6240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(
    mut v_isLower_6244_: *mut LeanObject,
    mut v_as_6245_: *mut LeanObject,
    mut v_sz_6246_: *mut LeanObject,
    mut v_i_6247_: *mut LeanObject,
    mut v_b_6248_: *mut LeanObject,
    mut v___y_6249_: *mut LeanObject,
    mut v___y_6250_: *mut LeanObject,
    mut v___y_6251_: *mut LeanObject,
    mut v___y_6252_: *mut LeanObject,
    mut v___y_6253_: *mut LeanObject,
    mut v___y_6254_: *mut LeanObject,
    mut v___y_6255_: *mut LeanObject,
    mut v___y_6256_: *mut LeanObject,
    mut v___y_6257_: *mut LeanObject,
    mut v___y_6258_: *mut LeanObject,
    mut v___y_6259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_6260_: u8 = 0;
    let mut v_sz_boxed_6261_: usize = 0;
    let mut v_i_boxed_6262_: usize = 0;
    let mut v_res_6263_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6260_ = (lean_unbox(v_isLower_6244_) as u8);
    v_sz_boxed_6261_ = lean_unbox_usize(v_sz_6246_);
    lean_dec(v_sz_6246_);
    v_i_boxed_6262_ = lean_unbox_usize(v_i_6247_);
    lean_dec(v_i_6247_);
    v_res_6263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_6260_, v_as_6245_, v_sz_boxed_6261_, v_i_boxed_6262_, v_b_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_);
    lean_dec(v___y_6258_);
    lean_dec_ref(v___y_6257_);
    lean_dec(v___y_6256_);
    lean_dec_ref(v___y_6255_);
    lean_dec(v___y_6254_);
    lean_dec_ref(v___y_6253_);
    lean_dec(v___y_6252_);
    lean_dec_ref(v___y_6251_);
    lean_dec(v___y_6250_);
    lean_dec(v___y_6249_);
    lean_dec_ref(v_as_6245_);
    return v_res_6263_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(
    mut v_init_6264_: *mut LeanObject,
    mut v_isLower_6265_: u8,
    mut v_n_6266_: *mut LeanObject,
    mut v_b_6267_: *mut LeanObject,
    mut v___y_6268_: *mut LeanObject,
    mut v___y_6269_: *mut LeanObject,
    mut v___y_6270_: *mut LeanObject,
    mut v___y_6271_: *mut LeanObject,
    mut v___y_6272_: *mut LeanObject,
    mut v___y_6273_: *mut LeanObject,
    mut v___y_6274_: *mut LeanObject,
    mut v___y_6275_: *mut LeanObject,
    mut v___y_6276_: *mut LeanObject,
    mut v___y_6277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6282_: usize = 0;
    let mut v___x_6283_: usize = 0;
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6288_: u8 = 0;
    let mut v_fst_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6299_: u8 = 0;
    let mut v_a_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6303_: u8 = 0;
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6307_: u8 = 0;
    let mut v_vs_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6311_: usize = 0;
    let mut v___x_6312_: usize = 0;
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6317_: u8 = 0;
    let mut v_fst_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6328_: u8 = 0;
    let mut v_a_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6332_: u8 = 0;
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_6266_) == 0 {
                    v_cs_6279_ = lean_ctor_get(v_n_6266_, 0);
                    v___x_6280_ = lean_box(0);
                    v___x_6281_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6281_, 0, v___x_6280_);
                    lean_ctor_set(v___x_6281_, 1, v_b_6267_);
                    v_sz_6282_ = lean_array_size(v_cs_6279_);
                    v___x_6283_ = 0usize;
                    v___x_6284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_6264_, v_isLower_6265_, v_cs_6279_, v_sz_6282_, v___x_6283_, v___x_6281_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_);
                    if lean_obj_tag(v___x_6284_) == 0 {
                        v_a_6285_ = lean_ctor_get(v___x_6284_, 0);
                        v_isSharedCheck_6299_ = (!lean_is_exclusive(v___x_6284_)) as u8;
                        if v_isSharedCheck_6299_ == 0 {
                            v___x_6287_ = v___x_6284_;
                            v_isShared_6288_ = v_isSharedCheck_6299_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6285_);
                            lean_dec(v___x_6284_);
                            v___x_6287_ = lean_box(0);
                            v_isShared_6288_ = v_isSharedCheck_6299_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6300_ = lean_ctor_get(v___x_6284_, 0);
                        v_isSharedCheck_6307_ = (!lean_is_exclusive(v___x_6284_)) as u8;
                        if v_isSharedCheck_6307_ == 0 {
                            v___x_6302_ = v___x_6284_;
                            v_isShared_6303_ = v_isSharedCheck_6307_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6300_);
                            lean_dec(v___x_6284_);
                            v___x_6302_ = lean_box(0);
                            v_isShared_6303_ = v_isSharedCheck_6307_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6308_ = lean_ctor_get(v_n_6266_, 0);
                    v___x_6309_ = lean_box(0);
                    v___x_6310_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6310_, 0, v___x_6309_);
                    lean_ctor_set(v___x_6310_, 1, v_b_6267_);
                    v_sz_6311_ = lean_array_size(v_vs_6308_);
                    v___x_6312_ = 0usize;
                    v___x_6313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_6265_, v_vs_6308_, v_sz_6311_, v___x_6312_, v___x_6310_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_);
                    if lean_obj_tag(v___x_6313_) == 0 {
                        v_a_6314_ = lean_ctor_get(v___x_6313_, 0);
                        v_isSharedCheck_6328_ = (!lean_is_exclusive(v___x_6313_)) as u8;
                        if v_isSharedCheck_6328_ == 0 {
                            v___x_6316_ = v___x_6313_;
                            v_isShared_6317_ = v_isSharedCheck_6328_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6314_);
                            lean_dec(v___x_6313_);
                            v___x_6316_ = lean_box(0);
                            v_isShared_6317_ = v_isSharedCheck_6328_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6329_ = lean_ctor_get(v___x_6313_, 0);
                        v_isSharedCheck_6336_ = (!lean_is_exclusive(v___x_6313_)) as u8;
                        if v_isSharedCheck_6336_ == 0 {
                            v___x_6331_ = v___x_6313_;
                            v_isShared_6332_ = v_isSharedCheck_6336_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6329_);
                            lean_dec(v___x_6313_);
                            v___x_6331_ = lean_box(0);
                            v_isShared_6332_ = v_isSharedCheck_6336_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6289_ = lean_ctor_get(v_a_6285_, 0);
                if lean_obj_tag(v_fst_6289_) == 0 {
                    v_snd_6290_ = lean_ctor_get(v_a_6285_, 1);
                    lean_inc(v_snd_6290_);
                    lean_dec(v_a_6285_);
                    v___x_6291_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6291_, 0, v_snd_6290_);
                    if v_isShared_6288_ == 0 {
                        lean_ctor_set(v___x_6287_, 0, v___x_6291_);
                        v___x_6293_ = v___x_6287_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6294_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6294_, 0, v___x_6291_);
                        v___x_6293_ = v_reuseFailAlloc_6294_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6289_);
                    lean_dec(v_a_6285_);
                    v_val_6295_ = lean_ctor_get(v_fst_6289_, 0);
                    lean_inc(v_val_6295_);
                    lean_dec_ref_known(v_fst_6289_, 1);
                    if v_isShared_6288_ == 0 {
                        lean_ctor_set(v___x_6287_, 0, v_val_6295_);
                        v___x_6297_ = v___x_6287_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6298_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6298_, 0, v_val_6295_);
                        v___x_6297_ = v_reuseFailAlloc_6298_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6293_;
            }
            3 => {
                return v___x_6297_;
            }
            4 => {
                if v_isShared_6303_ == 0 {
                    v___x_6305_ = v___x_6302_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6300_);
                    v___x_6305_ = v_reuseFailAlloc_6306_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6305_;
            }
            6 => {
                v_fst_6318_ = lean_ctor_get(v_a_6314_, 0);
                if lean_obj_tag(v_fst_6318_) == 0 {
                    v_snd_6319_ = lean_ctor_get(v_a_6314_, 1);
                    lean_inc(v_snd_6319_);
                    lean_dec(v_a_6314_);
                    v___x_6320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6320_, 0, v_snd_6319_);
                    if v_isShared_6317_ == 0 {
                        lean_ctor_set(v___x_6316_, 0, v___x_6320_);
                        v___x_6322_ = v___x_6316_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6323_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6323_, 0, v___x_6320_);
                        v___x_6322_ = v_reuseFailAlloc_6323_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6318_);
                    lean_dec(v_a_6314_);
                    v_val_6324_ = lean_ctor_get(v_fst_6318_, 0);
                    lean_inc(v_val_6324_);
                    lean_dec_ref_known(v_fst_6318_, 1);
                    if v_isShared_6317_ == 0 {
                        lean_ctor_set(v___x_6316_, 0, v_val_6324_);
                        v___x_6326_ = v___x_6316_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6327_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6327_, 0, v_val_6324_);
                        v___x_6326_ = v_reuseFailAlloc_6327_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6322_;
            }
            8 => {
                return v___x_6326_;
            }
            9 => {
                if v_isShared_6332_ == 0 {
                    v___x_6334_ = v___x_6331_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6335_, 0, v_a_6329_);
                    v___x_6334_ = v_reuseFailAlloc_6335_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(
    mut v_init_6337_: *mut LeanObject,
    mut v_isLower_6338_: u8,
    mut v_as_6339_: *mut LeanObject,
    mut v_sz_6340_: usize,
    mut v_i_6341_: usize,
    mut v_b_6342_: *mut LeanObject,
    mut v___y_6343_: *mut LeanObject,
    mut v___y_6344_: *mut LeanObject,
    mut v___y_6345_: *mut LeanObject,
    mut v___y_6346_: *mut LeanObject,
    mut v___y_6347_: *mut LeanObject,
    mut v___y_6348_: *mut LeanObject,
    mut v___y_6349_: *mut LeanObject,
    mut v___y_6350_: *mut LeanObject,
    mut v___y_6351_: *mut LeanObject,
    mut v___y_6352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6354_: u8 = 0;
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6359_: u8 = 0;
    let mut v_a_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: usize = 0;
    let mut v___x_6378_: usize = 0;
    let mut v_reuseFailAlloc_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6381_: u8 = 0;
    let mut v_a_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6385_: u8 = 0;
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6389_: u8 = 0;
    let mut v_isSharedCheck_6390_: u8 = 0;
    let mut v_unused_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6354_ = lean_usize_dec_lt(v_i_6341_, v_sz_6340_);
                if v___x_6354_ == 0 {
                    v___x_6355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6355_, 0, v_b_6342_);
                    return v___x_6355_;
                } else {
                    v_snd_6356_ = lean_ctor_get(v_b_6342_, 1);
                    v_isSharedCheck_6390_ = (!lean_is_exclusive(v_b_6342_)) as u8;
                    if v_isSharedCheck_6390_ == 0 {
                        v_unused_6391_ = lean_ctor_get(v_b_6342_, 0);
                        lean_dec(v_unused_6391_);
                        v___x_6358_ = v_b_6342_;
                        v_isShared_6359_ = v_isSharedCheck_6390_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6356_);
                        lean_dec(v_b_6342_);
                        v___x_6358_ = lean_box(0);
                        v_isShared_6359_ = v_isSharedCheck_6390_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6360_ = lean_array_uget_borrowed(v_as_6339_, v_i_6341_);
                lean_inc(v_snd_6356_);
                v___x_6361_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_6337_, v_isLower_6338_, v_a_6360_, v_snd_6356_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_);
                if lean_obj_tag(v___x_6361_) == 0 {
                    v_a_6362_ = lean_ctor_get(v___x_6361_, 0);
                    v_isSharedCheck_6381_ = (!lean_is_exclusive(v___x_6361_)) as u8;
                    if v_isSharedCheck_6381_ == 0 {
                        v___x_6364_ = v___x_6361_;
                        v_isShared_6365_ = v_isSharedCheck_6381_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6362_);
                        lean_dec(v___x_6361_);
                        v___x_6364_ = lean_box(0);
                        v_isShared_6365_ = v_isSharedCheck_6381_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6358_);
                    lean_dec(v_snd_6356_);
                    v_a_6382_ = lean_ctor_get(v___x_6361_, 0);
                    v_isSharedCheck_6389_ = (!lean_is_exclusive(v___x_6361_)) as u8;
                    if v_isSharedCheck_6389_ == 0 {
                        v___x_6384_ = v___x_6361_;
                        v_isShared_6385_ = v_isSharedCheck_6389_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6382_);
                        lean_dec(v___x_6361_);
                        v___x_6384_ = lean_box(0);
                        v_isShared_6385_ = v_isSharedCheck_6389_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6362_) == 0 {
                    v___x_6366_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6366_, 0, v_a_6362_);
                    if v_isShared_6359_ == 0 {
                        lean_ctor_set(v___x_6358_, 0, v___x_6366_);
                        v___x_6368_ = v___x_6358_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6372_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6372_, 0, v___x_6366_);
                        lean_ctor_set(v_reuseFailAlloc_6372_, 1, v_snd_6356_);
                        v___x_6368_ = v_reuseFailAlloc_6372_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6364_);
                    lean_dec(v_snd_6356_);
                    v_a_6373_ = lean_ctor_get(v_a_6362_, 0);
                    lean_inc(v_a_6373_);
                    lean_dec_ref_known(v_a_6362_, 1);
                    v___x_6374_ = lean_box(0);
                    if v_isShared_6359_ == 0 {
                        lean_ctor_set(v___x_6358_, 1, v_a_6373_);
                        lean_ctor_set(v___x_6358_, 0, v___x_6374_);
                        v___x_6376_ = v___x_6358_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6380_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6380_, 0, v___x_6374_);
                        lean_ctor_set(v_reuseFailAlloc_6380_, 1, v_a_6373_);
                        v___x_6376_ = v_reuseFailAlloc_6380_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6365_ == 0 {
                    lean_ctor_set(v___x_6364_, 0, v___x_6368_);
                    v___x_6370_ = v___x_6364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6371_, 0, v___x_6368_);
                    v___x_6370_ = v_reuseFailAlloc_6371_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6370_;
            }
            5 => {
                v___x_6377_ = 1usize;
                v___x_6378_ = lean_usize_add(v_i_6341_, v___x_6377_);
                v_i_6341_ = v___x_6378_;
                v_b_6342_ = v___x_6376_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_6385_ == 0 {
                    v___x_6387_ = v___x_6384_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_a_6382_);
                    v___x_6387_ = v_reuseFailAlloc_6388_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_6392_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_6393_: *mut LeanObject = *_args.add(1);
    let mut v_as_6394_: *mut LeanObject = *_args.add(2);
    let mut v_sz_6395_: *mut LeanObject = *_args.add(3);
    let mut v_i_6396_: *mut LeanObject = *_args.add(4);
    let mut v_b_6397_: *mut LeanObject = *_args.add(5);
    let mut v___y_6398_: *mut LeanObject = *_args.add(6);
    let mut v___y_6399_: *mut LeanObject = *_args.add(7);
    let mut v___y_6400_: *mut LeanObject = *_args.add(8);
    let mut v___y_6401_: *mut LeanObject = *_args.add(9);
    let mut v___y_6402_: *mut LeanObject = *_args.add(10);
    let mut v___y_6403_: *mut LeanObject = *_args.add(11);
    let mut v___y_6404_: *mut LeanObject = *_args.add(12);
    let mut v___y_6405_: *mut LeanObject = *_args.add(13);
    let mut v___y_6406_: *mut LeanObject = *_args.add(14);
    let mut v___y_6407_: *mut LeanObject = *_args.add(15);
    let mut v___y_6408_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_6409_: u8 = 0;
    let mut v_sz_boxed_6410_: usize = 0;
    let mut v_i_boxed_6411_: usize = 0;
    let mut v_res_6412_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6409_ = (lean_unbox(v_isLower_6393_) as u8);
    v_sz_boxed_6410_ = lean_unbox_usize(v_sz_6395_);
    lean_dec(v_sz_6395_);
    v_i_boxed_6411_ = lean_unbox_usize(v_i_6396_);
    lean_dec(v_i_6396_);
    v_res_6412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_6392_, v_isLower_boxed_6409_, v_as_6394_, v_sz_boxed_6410_, v_i_boxed_6411_, v_b_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_, v___y_6406_, v___y_6407_);
    lean_dec(v___y_6407_);
    lean_dec_ref(v___y_6406_);
    lean_dec(v___y_6405_);
    lean_dec_ref(v___y_6404_);
    lean_dec(v___y_6403_);
    lean_dec_ref(v___y_6402_);
    lean_dec(v___y_6401_);
    lean_dec_ref(v___y_6400_);
    lean_dec(v___y_6399_);
    lean_dec(v___y_6398_);
    lean_dec_ref(v_as_6394_);
    lean_dec(v_init_6392_);
    return v_res_6412_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4___boxed(
    mut v_init_6413_: *mut LeanObject,
    mut v_isLower_6414_: *mut LeanObject,
    mut v_n_6415_: *mut LeanObject,
    mut v_b_6416_: *mut LeanObject,
    mut v___y_6417_: *mut LeanObject,
    mut v___y_6418_: *mut LeanObject,
    mut v___y_6419_: *mut LeanObject,
    mut v___y_6420_: *mut LeanObject,
    mut v___y_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
    mut v___y_6426_: *mut LeanObject,
    mut v___y_6427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_6428_: u8 = 0;
    let mut v_res_6429_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6428_ = (lean_unbox(v_isLower_6414_) as u8);
    v_res_6429_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_6413_, v_isLower_boxed_6428_, v_n_6415_, v_b_6416_, v___y_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_);
    lean_dec(v___y_6426_);
    lean_dec_ref(v___y_6425_);
    lean_dec(v___y_6424_);
    lean_dec_ref(v___y_6423_);
    lean_dec(v___y_6422_);
    lean_dec_ref(v___y_6421_);
    lean_dec(v___y_6420_);
    lean_dec_ref(v___y_6419_);
    lean_dec(v___y_6418_);
    lean_dec(v___y_6417_);
    lean_dec_ref(v_n_6415_);
    lean_dec(v_init_6413_);
    return v_res_6429_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(
    mut v_isLower_6430_: u8,
    mut v_t_6431_: *mut LeanObject,
    mut v_init_6432_: *mut LeanObject,
    mut v___y_6433_: *mut LeanObject,
    mut v___y_6434_: *mut LeanObject,
    mut v___y_6435_: *mut LeanObject,
    mut v___y_6436_: *mut LeanObject,
    mut v___y_6437_: *mut LeanObject,
    mut v___y_6438_: *mut LeanObject,
    mut v___y_6439_: *mut LeanObject,
    mut v___y_6440_: *mut LeanObject,
    mut v___y_6441_: *mut LeanObject,
    mut v___y_6442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v_a_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6458_: usize = 0;
    let mut v___x_6459_: usize = 0;
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6464_: u8 = 0;
    let mut v_fst_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6474_: u8 = 0;
    let mut v_a_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6478_: u8 = 0;
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6482_: u8 = 0;
    let mut v_isSharedCheck_6483_: u8 = 0;
    let mut v_a_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6487_: u8 = 0;
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6444_ = lean_ctor_get(v_t_6431_, 0);
                v_tail_6445_ = lean_ctor_get(v_t_6431_, 1);
                lean_inc(v_init_6432_);
                v___x_6446_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__4(v_init_6432_, v_isLower_6430_, v_root_6444_, v_init_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_);
                lean_dec(v_init_6432_);
                if lean_obj_tag(v___x_6446_) == 0 {
                    v_a_6447_ = lean_ctor_get(v___x_6446_, 0);
                    v_isSharedCheck_6483_ = (!lean_is_exclusive(v___x_6446_)) as u8;
                    if v_isSharedCheck_6483_ == 0 {
                        v___x_6449_ = v___x_6446_;
                        v_isShared_6450_ = v_isSharedCheck_6483_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6447_);
                        lean_dec(v___x_6446_);
                        v___x_6449_ = lean_box(0);
                        v_isShared_6450_ = v_isSharedCheck_6483_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6484_ = lean_ctor_get(v___x_6446_, 0);
                    v_isSharedCheck_6491_ = (!lean_is_exclusive(v___x_6446_)) as u8;
                    if v_isSharedCheck_6491_ == 0 {
                        v___x_6486_ = v___x_6446_;
                        v_isShared_6487_ = v_isSharedCheck_6491_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6484_);
                        lean_dec(v___x_6446_);
                        v___x_6486_ = lean_box(0);
                        v_isShared_6487_ = v_isSharedCheck_6491_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6447_) == 0 {
                    v_a_6451_ = lean_ctor_get(v_a_6447_, 0);
                    lean_inc(v_a_6451_);
                    lean_dec_ref_known(v_a_6447_, 1);
                    if v_isShared_6450_ == 0 {
                        lean_ctor_set(v___x_6449_, 0, v_a_6451_);
                        v___x_6453_ = v___x_6449_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6454_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6454_, 0, v_a_6451_);
                        v___x_6453_ = v_reuseFailAlloc_6454_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6449_);
                    v_a_6455_ = lean_ctor_get(v_a_6447_, 0);
                    lean_inc(v_a_6455_);
                    lean_dec_ref_known(v_a_6447_, 1);
                    v___x_6456_ = lean_box(0);
                    v___x_6457_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6457_, 0, v___x_6456_);
                    lean_ctor_set(v___x_6457_, 1, v_a_6455_);
                    v_sz_6458_ = lean_array_size(v_tail_6445_);
                    v___x_6459_ = 0usize;
                    v___x_6460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2_spec__5(v_isLower_6430_, v_tail_6445_, v_sz_6458_, v___x_6459_, v___x_6457_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_);
                    if lean_obj_tag(v___x_6460_) == 0 {
                        v_a_6461_ = lean_ctor_get(v___x_6460_, 0);
                        v_isSharedCheck_6474_ = (!lean_is_exclusive(v___x_6460_)) as u8;
                        if v_isSharedCheck_6474_ == 0 {
                            v___x_6463_ = v___x_6460_;
                            v_isShared_6464_ = v_isSharedCheck_6474_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6461_);
                            lean_dec(v___x_6460_);
                            v___x_6463_ = lean_box(0);
                            v_isShared_6464_ = v_isSharedCheck_6474_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6475_ = lean_ctor_get(v___x_6460_, 0);
                        v_isSharedCheck_6482_ = (!lean_is_exclusive(v___x_6460_)) as u8;
                        if v_isSharedCheck_6482_ == 0 {
                            v___x_6477_ = v___x_6460_;
                            v_isShared_6478_ = v_isSharedCheck_6482_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6475_);
                            lean_dec(v___x_6460_);
                            v___x_6477_ = lean_box(0);
                            v_isShared_6478_ = v_isSharedCheck_6482_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6453_;
            }
            3 => {
                v_fst_6465_ = lean_ctor_get(v_a_6461_, 0);
                if lean_obj_tag(v_fst_6465_) == 0 {
                    v_snd_6466_ = lean_ctor_get(v_a_6461_, 1);
                    lean_inc(v_snd_6466_);
                    lean_dec(v_a_6461_);
                    if v_isShared_6464_ == 0 {
                        lean_ctor_set(v___x_6463_, 0, v_snd_6466_);
                        v___x_6468_ = v___x_6463_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6469_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6469_, 0, v_snd_6466_);
                        v___x_6468_ = v_reuseFailAlloc_6469_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6465_);
                    lean_dec(v_a_6461_);
                    v_val_6470_ = lean_ctor_get(v_fst_6465_, 0);
                    lean_inc(v_val_6470_);
                    lean_dec_ref_known(v_fst_6465_, 1);
                    if v_isShared_6464_ == 0 {
                        lean_ctor_set(v___x_6463_, 0, v_val_6470_);
                        v___x_6472_ = v___x_6463_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6473_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_val_6470_);
                        v___x_6472_ = v_reuseFailAlloc_6473_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6468_;
            }
            5 => {
                return v___x_6472_;
            }
            6 => {
                if v_isShared_6478_ == 0 {
                    v___x_6480_ = v___x_6477_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6481_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6481_, 0, v_a_6475_);
                    v___x_6480_ = v_reuseFailAlloc_6481_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6480_;
            }
            8 => {
                if v_isShared_6487_ == 0 {
                    v___x_6489_ = v___x_6486_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6490_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6490_, 0, v_a_6484_);
                    v___x_6489_ = v_reuseFailAlloc_6490_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6489_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2___boxed(
    mut v_isLower_6492_: *mut LeanObject,
    mut v_t_6493_: *mut LeanObject,
    mut v_init_6494_: *mut LeanObject,
    mut v___y_6495_: *mut LeanObject,
    mut v___y_6496_: *mut LeanObject,
    mut v___y_6497_: *mut LeanObject,
    mut v___y_6498_: *mut LeanObject,
    mut v___y_6499_: *mut LeanObject,
    mut v___y_6500_: *mut LeanObject,
    mut v___y_6501_: *mut LeanObject,
    mut v___y_6502_: *mut LeanObject,
    mut v___y_6503_: *mut LeanObject,
    mut v___y_6504_: *mut LeanObject,
    mut v___y_6505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_6506_: u8 = 0;
    let mut v_res_6507_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6506_ = (lean_unbox(v_isLower_6492_) as u8);
    v_res_6507_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(
            v_isLower_boxed_6506_,
            v_t_6493_,
            v_init_6494_,
            v___y_6495_,
            v___y_6496_,
            v___y_6497_,
            v___y_6498_,
            v___y_6499_,
            v___y_6500_,
            v___y_6501_,
            v___y_6502_,
            v___y_6503_,
            v___y_6504_,
        );
    lean_dec(v___y_6504_);
    lean_dec_ref(v___y_6503_);
    lean_dec(v___y_6502_);
    lean_dec_ref(v___y_6501_);
    lean_dec(v___y_6500_);
    lean_dec_ref(v___y_6499_);
    lean_dec(v___y_6498_);
    lean_dec_ref(v___y_6497_);
    lean_dec(v___y_6496_);
    lean_dec(v___y_6495_);
    lean_dec_ref(v_t_6493_);
    return v_res_6507_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(
    mut v_css_6508_: *mut LeanObject,
    mut v_isLower_6509_: u8,
    mut v_a_6510_: *mut LeanObject,
    mut v_a_6511_: *mut LeanObject,
    mut v_a_6512_: *mut LeanObject,
    mut v_a_6513_: *mut LeanObject,
    mut v_a_6514_: *mut LeanObject,
    mut v_a_6515_: *mut LeanObject,
    mut v_a_6516_: *mut LeanObject,
    mut v_a_6517_: *mut LeanObject,
    mut v_a_6518_: *mut LeanObject,
    mut v_a_6519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6525_: u8 = 0;
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6530_: u8 = 0;
    let mut v_unused_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6535_: u8 = 0;
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_6521_ = lean_unsigned_to_nat(0);
                v___x_6522_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__2(v_isLower_6509_, v_css_6508_, v_x_6521_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_, v_a_6514_, v_a_6515_, v_a_6516_, v_a_6517_, v_a_6518_, v_a_6519_);
                if lean_obj_tag(v___x_6522_) == 0 {
                    v_isSharedCheck_6530_ = (!lean_is_exclusive(v___x_6522_)) as u8;
                    if v_isSharedCheck_6530_ == 0 {
                        v_unused_6531_ = lean_ctor_get(v___x_6522_, 0);
                        lean_dec(v_unused_6531_);
                        v___x_6524_ = v___x_6522_;
                        v_isShared_6525_ = v_isSharedCheck_6530_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6522_);
                        v___x_6524_ = lean_box(0);
                        v_isShared_6525_ = v_isSharedCheck_6530_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6532_ = lean_ctor_get(v___x_6522_, 0);
                    v_isSharedCheck_6539_ = (!lean_is_exclusive(v___x_6522_)) as u8;
                    if v_isSharedCheck_6539_ == 0 {
                        v___x_6534_ = v___x_6522_;
                        v_isShared_6535_ = v_isSharedCheck_6539_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6532_);
                        lean_dec(v___x_6522_);
                        v___x_6534_ = lean_box(0);
                        v_isShared_6535_ = v_isSharedCheck_6539_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6526_ = lean_box(0);
                if v_isShared_6525_ == 0 {
                    lean_ctor_set(v___x_6524_, 0, v___x_6526_);
                    v___x_6528_ = v___x_6524_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6529_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6529_, 0, v___x_6526_);
                    v___x_6528_ = v_reuseFailAlloc_6529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6528_;
            }
            3 => {
                if v_isShared_6535_ == 0 {
                    v___x_6537_ = v___x_6534_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_a_6532_);
                    v___x_6537_ = v_reuseFailAlloc_6538_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs___boxed(
    mut v_css_6540_: *mut LeanObject,
    mut v_isLower_6541_: *mut LeanObject,
    mut v_a_6542_: *mut LeanObject,
    mut v_a_6543_: *mut LeanObject,
    mut v_a_6544_: *mut LeanObject,
    mut v_a_6545_: *mut LeanObject,
    mut v_a_6546_: *mut LeanObject,
    mut v_a_6547_: *mut LeanObject,
    mut v_a_6548_: *mut LeanObject,
    mut v_a_6549_: *mut LeanObject,
    mut v_a_6550_: *mut LeanObject,
    mut v_a_6551_: *mut LeanObject,
    mut v_a_6552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_6553_: u8 = 0;
    let mut v_res_6554_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_6553_ = (lean_unbox(v_isLower_6541_) as u8);
    v_res_6554_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(
        v_css_6540_,
        v_isLower_boxed_6553_,
        v_a_6542_,
        v_a_6543_,
        v_a_6544_,
        v_a_6545_,
        v_a_6546_,
        v_a_6547_,
        v_a_6548_,
        v_a_6549_,
        v_a_6550_,
        v_a_6551_,
    );
    lean_dec(v_a_6551_);
    lean_dec_ref(v_a_6550_);
    lean_dec(v_a_6549_);
    lean_dec_ref(v_a_6548_);
    lean_dec(v_a_6547_);
    lean_dec_ref(v_a_6546_);
    lean_dec(v_a_6545_);
    lean_dec_ref(v_a_6544_);
    lean_dec(v_a_6543_);
    lean_dec(v_a_6542_);
    lean_dec_ref(v_css_6540_);
    return v_res_6554_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2() -> *mut LeanObject {
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    v___x_6557_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__1;
    v___x_6558_ = lean_unsigned_to_nat(2);
    v___x_6559_ = lean_unsigned_to_nat(55);
    v___x_6560_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__0;
    v___x_6561_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_6562_ = l_mkPanicMessageWithDecl(
        v___x_6561_,
        v___x_6560_,
        v___x_6559_,
        v___x_6558_,
        v___x_6557_,
    );
    return v___x_6562_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(
    mut v_a_6563_: *mut LeanObject,
    mut v_a_6564_: *mut LeanObject,
    mut v_a_6565_: *mut LeanObject,
    mut v_a_6566_: *mut LeanObject,
    mut v_a_6567_: *mut LeanObject,
    mut v_a_6568_: *mut LeanObject,
    mut v_a_6569_: *mut LeanObject,
    mut v_a_6570_: *mut LeanObject,
    mut v_a_6571_: *mut LeanObject,
    mut v_a_6572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: u8 = 0;
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6574_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_6563_, v_a_6571_);
                if lean_obj_tag(v___x_6574_) == 0 {
                    v_a_6575_ = lean_ctor_get(v___x_6574_, 0);
                    lean_inc(v_a_6575_);
                    lean_dec_ref_known(v___x_6574_, 1);
                    v_lowers_6576_ = lean_ctor_get(v_a_6575_, 7);
                    lean_inc_ref(v_lowers_6576_);
                    v_vars_6577_ = lean_ctor_get(v_a_6575_, 0);
                    lean_inc_ref(v_vars_6577_);
                    lean_dec(v_a_6575_);
                    v_size_6578_ = lean_ctor_get(v_lowers_6576_, 2);
                    v_size_6579_ = lean_ctor_get(v_vars_6577_, 2);
                    lean_inc(v_size_6579_);
                    lean_dec_ref(v_vars_6577_);
                    v___x_6580_ = lean_nat_dec_eq(v_size_6578_, v_size_6579_);
                    lean_dec(v_size_6579_);
                    if v___x_6580_ == 0 {
                        lean_dec_ref(v_lowers_6576_);
                        v___x_6581_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___closed__2,
                        );
                        v___x_6582_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_6581_,
                            v_a_6563_,
                            v_a_6564_,
                            v_a_6565_,
                            v_a_6566_,
                            v_a_6567_,
                            v_a_6568_,
                            v_a_6569_,
                            v_a_6570_,
                            v_a_6571_,
                            v_a_6572_,
                        );
                        return v___x_6582_;
                    } else {
                        v___x_6583_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(
                            v_lowers_6576_,
                            v___x_6580_,
                            v_a_6563_,
                            v_a_6564_,
                            v_a_6565_,
                            v_a_6566_,
                            v_a_6567_,
                            v_a_6568_,
                            v_a_6569_,
                            v_a_6570_,
                            v_a_6571_,
                            v_a_6572_,
                        );
                        lean_dec_ref(v_lowers_6576_);
                        return v___x_6583_;
                    }
                } else {
                    v_a_6584_ = lean_ctor_get(v___x_6574_, 0);
                    v_isSharedCheck_6591_ = (!lean_is_exclusive(v___x_6574_)) as u8;
                    if v_isSharedCheck_6591_ == 0 {
                        v___x_6586_ = v___x_6574_;
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6584_);
                        lean_dec(v___x_6574_);
                        v___x_6586_ = lean_box(0);
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6587_ == 0 {
                    v___x_6589_ = v___x_6586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
                    v___x_6589_ = v_reuseFailAlloc_6590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkLowers___boxed(
    mut v_a_6592_: *mut LeanObject,
    mut v_a_6593_: *mut LeanObject,
    mut v_a_6594_: *mut LeanObject,
    mut v_a_6595_: *mut LeanObject,
    mut v_a_6596_: *mut LeanObject,
    mut v_a_6597_: *mut LeanObject,
    mut v_a_6598_: *mut LeanObject,
    mut v_a_6599_: *mut LeanObject,
    mut v_a_6600_: *mut LeanObject,
    mut v_a_6601_: *mut LeanObject,
    mut v_a_6602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6603_: *mut LeanObject = core::ptr::null_mut();
    v_res_6603_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(
        v_a_6592_, v_a_6593_, v_a_6594_, v_a_6595_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_,
        v_a_6600_, v_a_6601_,
    );
    lean_dec(v_a_6601_);
    lean_dec_ref(v_a_6600_);
    lean_dec(v_a_6599_);
    lean_dec_ref(v_a_6598_);
    lean_dec(v_a_6597_);
    lean_dec_ref(v_a_6596_);
    lean_dec(v_a_6595_);
    lean_dec_ref(v_a_6594_);
    lean_dec(v_a_6593_);
    lean_dec(v_a_6592_);
    return v_res_6603_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2() -> *mut LeanObject {
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    v___x_6606_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__1;
    v___x_6607_ = lean_unsigned_to_nat(2);
    v___x_6608_ = lean_unsigned_to_nat(60);
    v___x_6609_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__0;
    v___x_6610_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_6611_ = l_mkPanicMessageWithDecl(
        v___x_6610_,
        v___x_6609_,
        v___x_6608_,
        v___x_6607_,
        v___x_6606_,
    );
    return v___x_6611_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(
    mut v_a_6612_: *mut LeanObject,
    mut v_a_6613_: *mut LeanObject,
    mut v_a_6614_: *mut LeanObject,
    mut v_a_6615_: *mut LeanObject,
    mut v_a_6616_: *mut LeanObject,
    mut v_a_6617_: *mut LeanObject,
    mut v_a_6618_: *mut LeanObject,
    mut v_a_6619_: *mut LeanObject,
    mut v_a_6620_: *mut LeanObject,
    mut v_a_6621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: u8 = 0;
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: u8 = 0;
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6637_: u8 = 0;
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6623_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_6612_, v_a_6620_);
                if lean_obj_tag(v___x_6623_) == 0 {
                    v_a_6624_ = lean_ctor_get(v___x_6623_, 0);
                    lean_inc(v_a_6624_);
                    lean_dec_ref_known(v___x_6623_, 1);
                    v_uppers_6625_ = lean_ctor_get(v_a_6624_, 8);
                    lean_inc_ref(v_uppers_6625_);
                    v_vars_6626_ = lean_ctor_get(v_a_6624_, 0);
                    lean_inc_ref(v_vars_6626_);
                    lean_dec(v_a_6624_);
                    v_size_6627_ = lean_ctor_get(v_uppers_6625_, 2);
                    v_size_6628_ = lean_ctor_get(v_vars_6626_, 2);
                    lean_inc(v_size_6628_);
                    lean_dec_ref(v_vars_6626_);
                    v___x_6629_ = lean_nat_dec_eq(v_size_6627_, v_size_6628_);
                    lean_dec(v_size_6628_);
                    if v___x_6629_ == 0 {
                        lean_dec_ref(v_uppers_6625_);
                        v___x_6630_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___closed__2,
                        );
                        v___x_6631_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_6630_,
                            v_a_6612_,
                            v_a_6613_,
                            v_a_6614_,
                            v_a_6615_,
                            v_a_6616_,
                            v_a_6617_,
                            v_a_6618_,
                            v_a_6619_,
                            v_a_6620_,
                            v_a_6621_,
                        );
                        return v___x_6631_;
                    } else {
                        v___x_6632_ = 0;
                        v___x_6633_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs(
                            v_uppers_6625_,
                            v___x_6632_,
                            v_a_6612_,
                            v_a_6613_,
                            v_a_6614_,
                            v_a_6615_,
                            v_a_6616_,
                            v_a_6617_,
                            v_a_6618_,
                            v_a_6619_,
                            v_a_6620_,
                            v_a_6621_,
                        );
                        lean_dec_ref(v_uppers_6625_);
                        return v___x_6633_;
                    }
                } else {
                    v_a_6634_ = lean_ctor_get(v___x_6623_, 0);
                    v_isSharedCheck_6641_ = (!lean_is_exclusive(v___x_6623_)) as u8;
                    if v_isSharedCheck_6641_ == 0 {
                        v___x_6636_ = v___x_6623_;
                        v_isShared_6637_ = v_isSharedCheck_6641_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6634_);
                        lean_dec(v___x_6623_);
                        v___x_6636_ = lean_box(0);
                        v_isShared_6637_ = v_isSharedCheck_6641_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6637_ == 0 {
                    v___x_6639_ = v___x_6636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6640_, 0, v_a_6634_);
                    v___x_6639_ = v_reuseFailAlloc_6640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkUppers___boxed(
    mut v_a_6642_: *mut LeanObject,
    mut v_a_6643_: *mut LeanObject,
    mut v_a_6644_: *mut LeanObject,
    mut v_a_6645_: *mut LeanObject,
    mut v_a_6646_: *mut LeanObject,
    mut v_a_6647_: *mut LeanObject,
    mut v_a_6648_: *mut LeanObject,
    mut v_a_6649_: *mut LeanObject,
    mut v_a_6650_: *mut LeanObject,
    mut v_a_6651_: *mut LeanObject,
    mut v_a_6652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6653_: *mut LeanObject = core::ptr::null_mut();
    v_res_6653_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(
        v_a_6642_, v_a_6643_, v_a_6644_, v_a_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_,
        v_a_6650_, v_a_6651_,
    );
    lean_dec(v_a_6651_);
    lean_dec_ref(v_a_6650_);
    lean_dec(v_a_6649_);
    lean_dec_ref(v_a_6648_);
    lean_dec(v_a_6647_);
    lean_dec_ref(v_a_6646_);
    lean_dec(v_a_6645_);
    lean_dec_ref(v_a_6644_);
    lean_dec(v_a_6643_);
    lean_dec(v_a_6642_);
    return v_res_6653_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
    v___x_6654_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_6654_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
    mut v_msg_6655_: *mut LeanObject,
    mut v___y_6656_: *mut LeanObject,
    mut v___y_6657_: *mut LeanObject,
    mut v___y_6658_: *mut LeanObject,
    mut v___y_6659_: *mut LeanObject,
    mut v___y_6660_: *mut LeanObject,
    mut v___y_6661_: *mut LeanObject,
    mut v___y_6662_: *mut LeanObject,
    mut v___y_6663_: *mut LeanObject,
    mut v___y_6664_: *mut LeanObject,
    mut v___y_6665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874__overap_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    v___x_6667_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___closed__0,
    );
    v___x_4874__overap_6668_ = lean_panic_fn_borrowed(v___x_6667_, v_msg_6655_);
    lean_inc(v___y_6665_);
    lean_inc_ref(v___y_6664_);
    lean_inc(v___y_6663_);
    lean_inc_ref(v___y_6662_);
    lean_inc(v___y_6661_);
    lean_inc_ref(v___y_6660_);
    lean_inc(v___y_6659_);
    lean_inc_ref(v___y_6658_);
    lean_inc(v___y_6657_);
    lean_inc(v___y_6656_);
    v___x_6669_ = lean_apply_11(
        v___x_4874__overap_6668_,
        v___y_6656_,
        v___y_6657_,
        v___y_6658_,
        v___y_6659_,
        v___y_6660_,
        v___y_6661_,
        v___y_6662_,
        v___y_6663_,
        v___y_6664_,
        v___y_6665_,
        lean_box(0),
    );
    return v___x_6669_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0___boxed(
    mut v_msg_6670_: *mut LeanObject,
    mut v___y_6671_: *mut LeanObject,
    mut v___y_6672_: *mut LeanObject,
    mut v___y_6673_: *mut LeanObject,
    mut v___y_6674_: *mut LeanObject,
    mut v___y_6675_: *mut LeanObject,
    mut v___y_6676_: *mut LeanObject,
    mut v___y_6677_: *mut LeanObject,
    mut v___y_6678_: *mut LeanObject,
    mut v___y_6679_: *mut LeanObject,
    mut v___y_6680_: *mut LeanObject,
    mut v___y_6681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6682_: *mut LeanObject = core::ptr::null_mut();
    v_res_6682_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
        v_msg_6670_,
        v___y_6671_,
        v___y_6672_,
        v___y_6673_,
        v___y_6674_,
        v___y_6675_,
        v___y_6676_,
        v___y_6677_,
        v___y_6678_,
        v___y_6679_,
        v___y_6680_,
    );
    lean_dec(v___y_6680_);
    lean_dec_ref(v___y_6679_);
    lean_dec(v___y_6678_);
    lean_dec_ref(v___y_6677_);
    lean_dec(v___y_6676_);
    lean_dec_ref(v___y_6675_);
    lean_dec(v___y_6674_);
    lean_dec_ref(v___y_6673_);
    lean_dec(v___y_6672_);
    lean_dec(v___y_6671_);
    return v_res_6682_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    v___x_6683_ = lean_unsigned_to_nat(1);
    v___x_6684_ = lean_nat_to_int(v___x_6683_);
    return v___x_6684_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    v___x_6687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__2;
    v___x_6688_ = lean_unsigned_to_nat(6);
    v___x_6689_ = lean_unsigned_to_nat(70);
    v___x_6690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1;
    v___x_6691_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_6692_ = l_mkPanicMessageWithDecl(
        v___x_6691_,
        v___x_6690_,
        v___x_6689_,
        v___x_6688_,
        v___x_6687_,
    );
    return v___x_6692_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(
    mut v_as_6693_: *mut LeanObject,
    mut v_sz_6694_: usize,
    mut v_i_6695_: usize,
    mut v_b_6696_: *mut LeanObject,
    mut v___y_6697_: *mut LeanObject,
    mut v___y_6698_: *mut LeanObject,
    mut v___y_6699_: *mut LeanObject,
    mut v___y_6700_: *mut LeanObject,
    mut v___y_6701_: *mut LeanObject,
    mut v___y_6702_: *mut LeanObject,
    mut v___y_6703_: *mut LeanObject,
    mut v___y_6704_: *mut LeanObject,
    mut v___y_6705_: *mut LeanObject,
    mut v___y_6706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6708_: u8 = 0;
    let mut v___x_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6713_: u8 = 0;
    let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: usize = 0;
    let mut v___x_6720_: usize = 0;
    let mut v_reuseFailAlloc_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6730_: u8 = 0;
    let mut v_d_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: u8 = 0;
    let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6741_: u8 = 0;
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6750_: u8 = 0;
    let mut v_a_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6754_: u8 = 0;
    let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_a_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6762_: u8 = 0;
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6766_: u8 = 0;
    let mut v_isSharedCheck_6767_: u8 = 0;
    let mut v_isSharedCheck_6768_: u8 = 0;
    let mut v_unused_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6708_ = lean_usize_dec_lt(v_i_6695_, v_sz_6694_);
                if v___x_6708_ == 0 {
                    v___x_6709_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6709_, 0, v_b_6696_);
                    return v___x_6709_;
                } else {
                    v_snd_6710_ = lean_ctor_get(v_b_6696_, 1);
                    v_isSharedCheck_6768_ = (!lean_is_exclusive(v_b_6696_)) as u8;
                    if v_isSharedCheck_6768_ == 0 {
                        v_unused_6769_ = lean_ctor_get(v_b_6696_, 0);
                        lean_dec(v_unused_6769_);
                        v___x_6712_ = v_b_6696_;
                        v_isShared_6713_ = v_isSharedCheck_6768_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6710_);
                        lean_dec(v_b_6696_);
                        v___x_6712_ = lean_box(0);
                        v_isShared_6713_ = v_isSharedCheck_6768_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6714_ = lean_box(0);
                v_a_6726_ = lean_array_uget(v_as_6693_, v_i_6695_);
                if lean_obj_tag(v_a_6726_) == 1 {
                    v_val_6727_ = lean_ctor_get(v_a_6726_, 0);
                    v_isSharedCheck_6767_ = (!lean_is_exclusive(v_a_6726_)) as u8;
                    if v_isSharedCheck_6767_ == 0 {
                        v___x_6729_ = v_a_6726_;
                        v_isShared_6730_ = v_isSharedCheck_6767_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_6727_);
                        lean_dec(v_a_6726_);
                        v___x_6729_ = lean_box(0);
                        v_isShared_6730_ = v_isSharedCheck_6767_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6726_);
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_6713_ == 0 {
                    lean_ctor_set(v___x_6712_, 1, v_a_6716_);
                    lean_ctor_set(v___x_6712_, 0, v___x_6714_);
                    v___x_6718_ = v___x_6712_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6722_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6722_, 0, v___x_6714_);
                    lean_ctor_set(v_reuseFailAlloc_6722_, 1, v_a_6716_);
                    v___x_6718_ = v_reuseFailAlloc_6722_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6719_ = 1usize;
                v___x_6720_ = lean_usize_add(v_i_6695_, v___x_6719_);
                v_i_6695_ = v___x_6720_;
                v_b_6696_ = v___x_6718_;
                state = 0;
                continue;
            }
            4 => {
                v___x_6724_ = lean_unsigned_to_nat(1);
                v___x_6725_ = lean_nat_add(v_snd_6710_, v___x_6724_);
                lean_dec(v_snd_6710_);
                v_a_6716_ = v___x_6725_;
                state = 2;
                continue;
            }
            5 => {
                v_d_6731_ = lean_ctor_get(v_val_6727_, 0);
                lean_inc(v_d_6731_);
                v_p_6732_ = lean_ctor_get(v_val_6727_, 1);
                lean_inc_ref(v_p_6732_);
                lean_dec(v_val_6727_);
                v___x_6733_ = l_Int_Linear_Poly_checkCnstrOf(
                    v_p_6732_,
                    v_snd_6710_,
                    v___y_6697_,
                    v___y_6698_,
                    v___y_6699_,
                    v___y_6700_,
                    v___y_6701_,
                    v___y_6702_,
                    v___y_6703_,
                    v___y_6704_,
                    v___y_6705_,
                    v___y_6706_,
                );
                lean_dec_ref(v_p_6732_);
                if lean_obj_tag(v___x_6733_) == 0 {
                    lean_dec_ref_known(v___x_6733_, 1);
                    v___x_6734_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
                    v___x_6735_ = lean_int_dec_lt(v___x_6734_, v_d_6731_);
                    lean_dec(v_d_6731_);
                    if v___x_6735_ == 0 {
                        v___x_6736_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
                        v___x_6737_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_6736_,
                                v___y_6697_,
                                v___y_6698_,
                                v___y_6699_,
                                v___y_6700_,
                                v___y_6701_,
                                v___y_6702_,
                                v___y_6703_,
                                v___y_6704_,
                                v___y_6705_,
                                v___y_6706_,
                            );
                        if lean_obj_tag(v___x_6737_) == 0 {
                            v_a_6738_ = lean_ctor_get(v___x_6737_, 0);
                            v_isSharedCheck_6750_ = (!lean_is_exclusive(v___x_6737_)) as u8;
                            if v_isSharedCheck_6750_ == 0 {
                                v___x_6740_ = v___x_6737_;
                                v_isShared_6741_ = v_isSharedCheck_6750_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6738_);
                                lean_dec(v___x_6737_);
                                v___x_6740_ = lean_box(0);
                                v_isShared_6741_ = v_isSharedCheck_6750_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_6729_);
                            lean_del_object(v___x_6712_);
                            lean_dec(v_snd_6710_);
                            v_a_6751_ = lean_ctor_get(v___x_6737_, 0);
                            v_isSharedCheck_6758_ = (!lean_is_exclusive(v___x_6737_)) as u8;
                            if v_isSharedCheck_6758_ == 0 {
                                v___x_6753_ = v___x_6737_;
                                v_isShared_6754_ = v_isSharedCheck_6758_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_6751_);
                                lean_dec(v___x_6737_);
                                v___x_6753_ = lean_box(0);
                                v_isShared_6754_ = v_isSharedCheck_6758_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_6729_);
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_d_6731_);
                    lean_del_object(v___x_6729_);
                    lean_del_object(v___x_6712_);
                    lean_dec(v_snd_6710_);
                    v_a_6759_ = lean_ctor_get(v___x_6733_, 0);
                    v_isSharedCheck_6766_ = (!lean_is_exclusive(v___x_6733_)) as u8;
                    if v_isSharedCheck_6766_ == 0 {
                        v___x_6761_ = v___x_6733_;
                        v_isShared_6762_ = v_isSharedCheck_6766_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_6759_);
                        lean_dec(v___x_6733_);
                        v___x_6761_ = lean_box(0);
                        v_isShared_6762_ = v_isSharedCheck_6766_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_6738_) == 0 {
                    lean_del_object(v___x_6712_);
                    if v_isShared_6730_ == 0 {
                        lean_ctor_set(v___x_6729_, 0, v_a_6738_);
                        v___x_6743_ = v___x_6729_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6748_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6748_, 0, v_a_6738_);
                        v___x_6743_ = v_reuseFailAlloc_6748_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6740_);
                    lean_del_object(v___x_6729_);
                    lean_dec(v_snd_6710_);
                    v_a_6749_ = lean_ctor_get(v_a_6738_, 0);
                    lean_inc(v_a_6749_);
                    lean_dec_ref_known(v_a_6738_, 1);
                    v_a_6716_ = v_a_6749_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_6744_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6744_, 0, v___x_6743_);
                lean_ctor_set(v___x_6744_, 1, v_snd_6710_);
                if v_isShared_6741_ == 0 {
                    lean_ctor_set(v___x_6740_, 0, v___x_6744_);
                    v___x_6746_ = v___x_6740_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6747_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6747_, 0, v___x_6744_);
                    v___x_6746_ = v_reuseFailAlloc_6747_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6746_;
            }
            9 => {
                if v_isShared_6754_ == 0 {
                    v___x_6756_ = v___x_6753_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6757_, 0, v_a_6751_);
                    v___x_6756_ = v_reuseFailAlloc_6757_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6756_;
            }
            11 => {
                if v_isShared_6762_ == 0 {
                    v___x_6764_ = v___x_6761_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6765_, 0, v_a_6759_);
                    v___x_6764_ = v_reuseFailAlloc_6765_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___boxed(
    mut v_as_6770_: *mut LeanObject,
    mut v_sz_6771_: *mut LeanObject,
    mut v_i_6772_: *mut LeanObject,
    mut v_b_6773_: *mut LeanObject,
    mut v___y_6774_: *mut LeanObject,
    mut v___y_6775_: *mut LeanObject,
    mut v___y_6776_: *mut LeanObject,
    mut v___y_6777_: *mut LeanObject,
    mut v___y_6778_: *mut LeanObject,
    mut v___y_6779_: *mut LeanObject,
    mut v___y_6780_: *mut LeanObject,
    mut v___y_6781_: *mut LeanObject,
    mut v___y_6782_: *mut LeanObject,
    mut v___y_6783_: *mut LeanObject,
    mut v___y_6784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6785_: usize = 0;
    let mut v_i_boxed_6786_: usize = 0;
    let mut v_res_6787_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6785_ = lean_unbox_usize(v_sz_6771_);
    lean_dec(v_sz_6771_);
    v_i_boxed_6786_ = lean_unbox_usize(v_i_6772_);
    lean_dec(v_i_6772_);
    v_res_6787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_6770_, v_sz_boxed_6785_, v_i_boxed_6786_, v_b_6773_, v___y_6774_, v___y_6775_, v___y_6776_, v___y_6777_, v___y_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_, v___y_6783_);
    lean_dec(v___y_6783_);
    lean_dec_ref(v___y_6782_);
    lean_dec(v___y_6781_);
    lean_dec_ref(v___y_6780_);
    lean_dec(v___y_6779_);
    lean_dec_ref(v___y_6778_);
    lean_dec(v___y_6777_);
    lean_dec_ref(v___y_6776_);
    lean_dec(v___y_6775_);
    lean_dec(v___y_6774_);
    lean_dec_ref(v_as_6770_);
    return v_res_6787_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(
    mut v_as_6788_: *mut LeanObject,
    mut v_sz_6789_: usize,
    mut v_i_6790_: usize,
    mut v_b_6791_: *mut LeanObject,
    mut v___y_6792_: *mut LeanObject,
    mut v___y_6793_: *mut LeanObject,
    mut v___y_6794_: *mut LeanObject,
    mut v___y_6795_: *mut LeanObject,
    mut v___y_6796_: *mut LeanObject,
    mut v___y_6797_: *mut LeanObject,
    mut v___y_6798_: *mut LeanObject,
    mut v___y_6799_: *mut LeanObject,
    mut v___y_6800_: *mut LeanObject,
    mut v___y_6801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6803_: u8 = 0;
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6808_: u8 = 0;
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: usize = 0;
    let mut v___x_6815_: usize = 0;
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6825_: u8 = 0;
    let mut v_d_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: u8 = 0;
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6836_: u8 = 0;
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut v_a_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6849_: u8 = 0;
    let mut v___x_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6853_: u8 = 0;
    let mut v_a_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6857_: u8 = 0;
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6861_: u8 = 0;
    let mut v_isSharedCheck_6862_: u8 = 0;
    let mut v_isSharedCheck_6863_: u8 = 0;
    let mut v_unused_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6803_ = lean_usize_dec_lt(v_i_6790_, v_sz_6789_);
                if v___x_6803_ == 0 {
                    v___x_6804_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6804_, 0, v_b_6791_);
                    return v___x_6804_;
                } else {
                    v_snd_6805_ = lean_ctor_get(v_b_6791_, 1);
                    v_isSharedCheck_6863_ = (!lean_is_exclusive(v_b_6791_)) as u8;
                    if v_isSharedCheck_6863_ == 0 {
                        v_unused_6864_ = lean_ctor_get(v_b_6791_, 0);
                        lean_dec(v_unused_6864_);
                        v___x_6807_ = v_b_6791_;
                        v_isShared_6808_ = v_isSharedCheck_6863_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6805_);
                        lean_dec(v_b_6791_);
                        v___x_6807_ = lean_box(0);
                        v_isShared_6808_ = v_isSharedCheck_6863_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6809_ = lean_box(0);
                v_a_6821_ = lean_array_uget(v_as_6788_, v_i_6790_);
                if lean_obj_tag(v_a_6821_) == 1 {
                    v_val_6822_ = lean_ctor_get(v_a_6821_, 0);
                    v_isSharedCheck_6862_ = (!lean_is_exclusive(v_a_6821_)) as u8;
                    if v_isSharedCheck_6862_ == 0 {
                        v___x_6824_ = v_a_6821_;
                        v_isShared_6825_ = v_isSharedCheck_6862_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_6822_);
                        lean_dec(v_a_6821_);
                        v___x_6824_ = lean_box(0);
                        v_isShared_6825_ = v_isSharedCheck_6862_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6821_);
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_6808_ == 0 {
                    lean_ctor_set(v___x_6807_, 1, v_a_6811_);
                    lean_ctor_set(v___x_6807_, 0, v___x_6809_);
                    v___x_6813_ = v___x_6807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6817_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6817_, 0, v___x_6809_);
                    lean_ctor_set(v_reuseFailAlloc_6817_, 1, v_a_6811_);
                    v___x_6813_ = v_reuseFailAlloc_6817_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6814_ = 1usize;
                v___x_6815_ = lean_usize_add(v_i_6790_, v___x_6814_);
                v___x_6816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4(v_as_6788_, v_sz_6789_, v___x_6815_, v___x_6813_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_);
                return v___x_6816_;
            }
            4 => {
                v___x_6819_ = lean_unsigned_to_nat(1);
                v___x_6820_ = lean_nat_add(v_snd_6805_, v___x_6819_);
                lean_dec(v_snd_6805_);
                v_a_6811_ = v___x_6820_;
                state = 2;
                continue;
            }
            5 => {
                v_d_6826_ = lean_ctor_get(v_val_6822_, 0);
                lean_inc(v_d_6826_);
                v_p_6827_ = lean_ctor_get(v_val_6822_, 1);
                lean_inc_ref(v_p_6827_);
                lean_dec(v_val_6822_);
                v___x_6828_ = l_Int_Linear_Poly_checkCnstrOf(
                    v_p_6827_,
                    v_snd_6805_,
                    v___y_6792_,
                    v___y_6793_,
                    v___y_6794_,
                    v___y_6795_,
                    v___y_6796_,
                    v___y_6797_,
                    v___y_6798_,
                    v___y_6799_,
                    v___y_6800_,
                    v___y_6801_,
                );
                lean_dec_ref(v_p_6827_);
                if lean_obj_tag(v___x_6828_) == 0 {
                    lean_dec_ref_known(v___x_6828_, 1);
                    v___x_6829_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
                    v___x_6830_ = lean_int_dec_lt(v___x_6829_, v_d_6826_);
                    lean_dec(v_d_6826_);
                    if v___x_6830_ == 0 {
                        v___x_6831_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
                        v___x_6832_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_6831_,
                                v___y_6792_,
                                v___y_6793_,
                                v___y_6794_,
                                v___y_6795_,
                                v___y_6796_,
                                v___y_6797_,
                                v___y_6798_,
                                v___y_6799_,
                                v___y_6800_,
                                v___y_6801_,
                            );
                        if lean_obj_tag(v___x_6832_) == 0 {
                            v_a_6833_ = lean_ctor_get(v___x_6832_, 0);
                            v_isSharedCheck_6845_ = (!lean_is_exclusive(v___x_6832_)) as u8;
                            if v_isSharedCheck_6845_ == 0 {
                                v___x_6835_ = v___x_6832_;
                                v_isShared_6836_ = v_isSharedCheck_6845_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6833_);
                                lean_dec(v___x_6832_);
                                v___x_6835_ = lean_box(0);
                                v_isShared_6836_ = v_isSharedCheck_6845_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_6824_);
                            lean_del_object(v___x_6807_);
                            lean_dec(v_snd_6805_);
                            v_a_6846_ = lean_ctor_get(v___x_6832_, 0);
                            v_isSharedCheck_6853_ = (!lean_is_exclusive(v___x_6832_)) as u8;
                            if v_isSharedCheck_6853_ == 0 {
                                v___x_6848_ = v___x_6832_;
                                v_isShared_6849_ = v_isSharedCheck_6853_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_6846_);
                                lean_dec(v___x_6832_);
                                v___x_6848_ = lean_box(0);
                                v_isShared_6849_ = v_isSharedCheck_6853_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_6824_);
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_d_6826_);
                    lean_del_object(v___x_6824_);
                    lean_del_object(v___x_6807_);
                    lean_dec(v_snd_6805_);
                    v_a_6854_ = lean_ctor_get(v___x_6828_, 0);
                    v_isSharedCheck_6861_ = (!lean_is_exclusive(v___x_6828_)) as u8;
                    if v_isSharedCheck_6861_ == 0 {
                        v___x_6856_ = v___x_6828_;
                        v_isShared_6857_ = v_isSharedCheck_6861_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_6854_);
                        lean_dec(v___x_6828_);
                        v___x_6856_ = lean_box(0);
                        v_isShared_6857_ = v_isSharedCheck_6861_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_6833_) == 0 {
                    lean_del_object(v___x_6807_);
                    if v_isShared_6825_ == 0 {
                        lean_ctor_set(v___x_6824_, 0, v_a_6833_);
                        v___x_6838_ = v___x_6824_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6843_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6843_, 0, v_a_6833_);
                        v___x_6838_ = v_reuseFailAlloc_6843_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6835_);
                    lean_del_object(v___x_6824_);
                    lean_dec(v_snd_6805_);
                    v_a_6844_ = lean_ctor_get(v_a_6833_, 0);
                    lean_inc(v_a_6844_);
                    lean_dec_ref_known(v_a_6833_, 1);
                    v_a_6811_ = v_a_6844_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_6839_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6839_, 0, v___x_6838_);
                lean_ctor_set(v___x_6839_, 1, v_snd_6805_);
                if v_isShared_6836_ == 0 {
                    lean_ctor_set(v___x_6835_, 0, v___x_6839_);
                    v___x_6841_ = v___x_6835_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6842_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6842_, 0, v___x_6839_);
                    v___x_6841_ = v_reuseFailAlloc_6842_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6841_;
            }
            9 => {
                if v_isShared_6849_ == 0 {
                    v___x_6851_ = v___x_6848_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6852_, 0, v_a_6846_);
                    v___x_6851_ = v_reuseFailAlloc_6852_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6851_;
            }
            11 => {
                if v_isShared_6857_ == 0 {
                    v___x_6859_ = v___x_6856_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6860_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6860_, 0, v_a_6854_);
                    v___x_6859_ = v_reuseFailAlloc_6860_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3___boxed(
    mut v_as_6865_: *mut LeanObject,
    mut v_sz_6866_: *mut LeanObject,
    mut v_i_6867_: *mut LeanObject,
    mut v_b_6868_: *mut LeanObject,
    mut v___y_6869_: *mut LeanObject,
    mut v___y_6870_: *mut LeanObject,
    mut v___y_6871_: *mut LeanObject,
    mut v___y_6872_: *mut LeanObject,
    mut v___y_6873_: *mut LeanObject,
    mut v___y_6874_: *mut LeanObject,
    mut v___y_6875_: *mut LeanObject,
    mut v___y_6876_: *mut LeanObject,
    mut v___y_6877_: *mut LeanObject,
    mut v___y_6878_: *mut LeanObject,
    mut v___y_6879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6880_: usize = 0;
    let mut v_i_boxed_6881_: usize = 0;
    let mut v_res_6882_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6880_ = lean_unbox_usize(v_sz_6866_);
    lean_dec(v_sz_6866_);
    v_i_boxed_6881_ = lean_unbox_usize(v_i_6867_);
    lean_dec(v_i_6867_);
    v_res_6882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_as_6865_, v_sz_boxed_6880_, v_i_boxed_6881_, v_b_6868_, v___y_6869_, v___y_6870_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
    lean_dec(v___y_6878_);
    lean_dec_ref(v___y_6877_);
    lean_dec(v___y_6876_);
    lean_dec_ref(v___y_6875_);
    lean_dec(v___y_6874_);
    lean_dec_ref(v___y_6873_);
    lean_dec(v___y_6872_);
    lean_dec_ref(v___y_6871_);
    lean_dec(v___y_6870_);
    lean_dec(v___y_6869_);
    lean_dec_ref(v_as_6865_);
    return v_res_6882_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(
    mut v_init_6883_: *mut LeanObject,
    mut v_n_6884_: *mut LeanObject,
    mut v_b_6885_: *mut LeanObject,
    mut v___y_6886_: *mut LeanObject,
    mut v___y_6887_: *mut LeanObject,
    mut v___y_6888_: *mut LeanObject,
    mut v___y_6889_: *mut LeanObject,
    mut v___y_6890_: *mut LeanObject,
    mut v___y_6891_: *mut LeanObject,
    mut v___y_6892_: *mut LeanObject,
    mut v___y_6893_: *mut LeanObject,
    mut v___y_6894_: *mut LeanObject,
    mut v___y_6895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6900_: usize = 0;
    let mut v___x_6901_: usize = 0;
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6906_: u8 = 0;
    let mut v_fst_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6917_: u8 = 0;
    let mut v_a_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6921_: u8 = 0;
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut v_vs_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6929_: usize = 0;
    let mut v___x_6930_: usize = 0;
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6935_: u8 = 0;
    let mut v_fst_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6946_: u8 = 0;
    let mut v_a_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6950_: u8 = 0;
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_6884_) == 0 {
                    v_cs_6897_ = lean_ctor_get(v_n_6884_, 0);
                    v___x_6898_ = lean_box(0);
                    v___x_6899_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6899_, 0, v___x_6898_);
                    lean_ctor_set(v___x_6899_, 1, v_b_6885_);
                    v_sz_6900_ = lean_array_size(v_cs_6897_);
                    v___x_6901_ = 0usize;
                    v___x_6902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_6883_, v_cs_6897_, v_sz_6900_, v___x_6901_, v___x_6899_, v___y_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_, v___y_6894_, v___y_6895_);
                    if lean_obj_tag(v___x_6902_) == 0 {
                        v_a_6903_ = lean_ctor_get(v___x_6902_, 0);
                        v_isSharedCheck_6917_ = (!lean_is_exclusive(v___x_6902_)) as u8;
                        if v_isSharedCheck_6917_ == 0 {
                            v___x_6905_ = v___x_6902_;
                            v_isShared_6906_ = v_isSharedCheck_6917_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6903_);
                            lean_dec(v___x_6902_);
                            v___x_6905_ = lean_box(0);
                            v_isShared_6906_ = v_isSharedCheck_6917_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6918_ = lean_ctor_get(v___x_6902_, 0);
                        v_isSharedCheck_6925_ = (!lean_is_exclusive(v___x_6902_)) as u8;
                        if v_isSharedCheck_6925_ == 0 {
                            v___x_6920_ = v___x_6902_;
                            v_isShared_6921_ = v_isSharedCheck_6925_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6918_);
                            lean_dec(v___x_6902_);
                            v___x_6920_ = lean_box(0);
                            v_isShared_6921_ = v_isSharedCheck_6925_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6926_ = lean_ctor_get(v_n_6884_, 0);
                    v___x_6927_ = lean_box(0);
                    v___x_6928_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6928_, 0, v___x_6927_);
                    lean_ctor_set(v___x_6928_, 1, v_b_6885_);
                    v_sz_6929_ = lean_array_size(v_vs_6926_);
                    v___x_6930_ = 0usize;
                    v___x_6931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3(v_vs_6926_, v_sz_6929_, v___x_6930_, v___x_6928_, v___y_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_, v___y_6894_, v___y_6895_);
                    if lean_obj_tag(v___x_6931_) == 0 {
                        v_a_6932_ = lean_ctor_get(v___x_6931_, 0);
                        v_isSharedCheck_6946_ = (!lean_is_exclusive(v___x_6931_)) as u8;
                        if v_isSharedCheck_6946_ == 0 {
                            v___x_6934_ = v___x_6931_;
                            v_isShared_6935_ = v_isSharedCheck_6946_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6932_);
                            lean_dec(v___x_6931_);
                            v___x_6934_ = lean_box(0);
                            v_isShared_6935_ = v_isSharedCheck_6946_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6947_ = lean_ctor_get(v___x_6931_, 0);
                        v_isSharedCheck_6954_ = (!lean_is_exclusive(v___x_6931_)) as u8;
                        if v_isSharedCheck_6954_ == 0 {
                            v___x_6949_ = v___x_6931_;
                            v_isShared_6950_ = v_isSharedCheck_6954_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6947_);
                            lean_dec(v___x_6931_);
                            v___x_6949_ = lean_box(0);
                            v_isShared_6950_ = v_isSharedCheck_6954_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6907_ = lean_ctor_get(v_a_6903_, 0);
                if lean_obj_tag(v_fst_6907_) == 0 {
                    v_snd_6908_ = lean_ctor_get(v_a_6903_, 1);
                    lean_inc(v_snd_6908_);
                    lean_dec(v_a_6903_);
                    v___x_6909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6909_, 0, v_snd_6908_);
                    if v_isShared_6906_ == 0 {
                        lean_ctor_set(v___x_6905_, 0, v___x_6909_);
                        v___x_6911_ = v___x_6905_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6912_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6912_, 0, v___x_6909_);
                        v___x_6911_ = v_reuseFailAlloc_6912_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6907_);
                    lean_dec(v_a_6903_);
                    v_val_6913_ = lean_ctor_get(v_fst_6907_, 0);
                    lean_inc(v_val_6913_);
                    lean_dec_ref_known(v_fst_6907_, 1);
                    if v_isShared_6906_ == 0 {
                        lean_ctor_set(v___x_6905_, 0, v_val_6913_);
                        v___x_6915_ = v___x_6905_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6916_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6916_, 0, v_val_6913_);
                        v___x_6915_ = v_reuseFailAlloc_6916_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6911_;
            }
            3 => {
                return v___x_6915_;
            }
            4 => {
                if v_isShared_6921_ == 0 {
                    v___x_6923_ = v___x_6920_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_a_6918_);
                    v___x_6923_ = v_reuseFailAlloc_6924_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6923_;
            }
            6 => {
                v_fst_6936_ = lean_ctor_get(v_a_6932_, 0);
                if lean_obj_tag(v_fst_6936_) == 0 {
                    v_snd_6937_ = lean_ctor_get(v_a_6932_, 1);
                    lean_inc(v_snd_6937_);
                    lean_dec(v_a_6932_);
                    v___x_6938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6938_, 0, v_snd_6937_);
                    if v_isShared_6935_ == 0 {
                        lean_ctor_set(v___x_6934_, 0, v___x_6938_);
                        v___x_6940_ = v___x_6934_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6941_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6941_, 0, v___x_6938_);
                        v___x_6940_ = v_reuseFailAlloc_6941_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6936_);
                    lean_dec(v_a_6932_);
                    v_val_6942_ = lean_ctor_get(v_fst_6936_, 0);
                    lean_inc(v_val_6942_);
                    lean_dec_ref_known(v_fst_6936_, 1);
                    if v_isShared_6935_ == 0 {
                        lean_ctor_set(v___x_6934_, 0, v_val_6942_);
                        v___x_6944_ = v___x_6934_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6945_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6945_, 0, v_val_6942_);
                        v___x_6944_ = v_reuseFailAlloc_6945_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6940_;
            }
            8 => {
                return v___x_6944_;
            }
            9 => {
                if v_isShared_6950_ == 0 {
                    v___x_6952_ = v___x_6949_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6953_, 0, v_a_6947_);
                    v___x_6952_ = v_reuseFailAlloc_6953_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(
    mut v_init_6955_: *mut LeanObject,
    mut v_as_6956_: *mut LeanObject,
    mut v_sz_6957_: usize,
    mut v_i_6958_: usize,
    mut v_b_6959_: *mut LeanObject,
    mut v___y_6960_: *mut LeanObject,
    mut v___y_6961_: *mut LeanObject,
    mut v___y_6962_: *mut LeanObject,
    mut v___y_6963_: *mut LeanObject,
    mut v___y_6964_: *mut LeanObject,
    mut v___y_6965_: *mut LeanObject,
    mut v___y_6966_: *mut LeanObject,
    mut v___y_6967_: *mut LeanObject,
    mut v___y_6968_: *mut LeanObject,
    mut v___y_6969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6971_: u8 = 0;
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6976_: u8 = 0;
    let mut v_a_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6982_: u8 = 0;
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: usize = 0;
    let mut v___x_6995_: usize = 0;
    let mut v_reuseFailAlloc_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6998_: u8 = 0;
    let mut v_a_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7002_: u8 = 0;
    let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7006_: u8 = 0;
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v_unused_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6971_ = lean_usize_dec_lt(v_i_6958_, v_sz_6957_);
                if v___x_6971_ == 0 {
                    v___x_6972_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6972_, 0, v_b_6959_);
                    return v___x_6972_;
                } else {
                    v_snd_6973_ = lean_ctor_get(v_b_6959_, 1);
                    v_isSharedCheck_7007_ = (!lean_is_exclusive(v_b_6959_)) as u8;
                    if v_isSharedCheck_7007_ == 0 {
                        v_unused_7008_ = lean_ctor_get(v_b_6959_, 0);
                        lean_dec(v_unused_7008_);
                        v___x_6975_ = v_b_6959_;
                        v_isShared_6976_ = v_isSharedCheck_7007_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6973_);
                        lean_dec(v_b_6959_);
                        v___x_6975_ = lean_box(0);
                        v_isShared_6976_ = v_isSharedCheck_7007_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6977_ = lean_array_uget_borrowed(v_as_6956_, v_i_6958_);
                lean_inc(v_snd_6973_);
                v___x_6978_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_6955_, v_a_6977_, v_snd_6973_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_);
                if lean_obj_tag(v___x_6978_) == 0 {
                    v_a_6979_ = lean_ctor_get(v___x_6978_, 0);
                    v_isSharedCheck_6998_ = (!lean_is_exclusive(v___x_6978_)) as u8;
                    if v_isSharedCheck_6998_ == 0 {
                        v___x_6981_ = v___x_6978_;
                        v_isShared_6982_ = v_isSharedCheck_6998_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6979_);
                        lean_dec(v___x_6978_);
                        v___x_6981_ = lean_box(0);
                        v_isShared_6982_ = v_isSharedCheck_6998_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6975_);
                    lean_dec(v_snd_6973_);
                    v_a_6999_ = lean_ctor_get(v___x_6978_, 0);
                    v_isSharedCheck_7006_ = (!lean_is_exclusive(v___x_6978_)) as u8;
                    if v_isSharedCheck_7006_ == 0 {
                        v___x_7001_ = v___x_6978_;
                        v_isShared_7002_ = v_isSharedCheck_7006_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6999_);
                        lean_dec(v___x_6978_);
                        v___x_7001_ = lean_box(0);
                        v_isShared_7002_ = v_isSharedCheck_7006_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6979_) == 0 {
                    v___x_6983_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6983_, 0, v_a_6979_);
                    if v_isShared_6976_ == 0 {
                        lean_ctor_set(v___x_6975_, 0, v___x_6983_);
                        v___x_6985_ = v___x_6975_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6989_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6989_, 0, v___x_6983_);
                        lean_ctor_set(v_reuseFailAlloc_6989_, 1, v_snd_6973_);
                        v___x_6985_ = v_reuseFailAlloc_6989_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6981_);
                    lean_dec(v_snd_6973_);
                    v_a_6990_ = lean_ctor_get(v_a_6979_, 0);
                    lean_inc(v_a_6990_);
                    lean_dec_ref_known(v_a_6979_, 1);
                    v___x_6991_ = lean_box(0);
                    if v_isShared_6976_ == 0 {
                        lean_ctor_set(v___x_6975_, 1, v_a_6990_);
                        lean_ctor_set(v___x_6975_, 0, v___x_6991_);
                        v___x_6993_ = v___x_6975_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6997_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6997_, 0, v___x_6991_);
                        lean_ctor_set(v_reuseFailAlloc_6997_, 1, v_a_6990_);
                        v___x_6993_ = v_reuseFailAlloc_6997_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6982_ == 0 {
                    lean_ctor_set(v___x_6981_, 0, v___x_6985_);
                    v___x_6987_ = v___x_6981_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6988_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6988_, 0, v___x_6985_);
                    v___x_6987_ = v_reuseFailAlloc_6988_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6987_;
            }
            5 => {
                v___x_6994_ = 1usize;
                v___x_6995_ = lean_usize_add(v_i_6958_, v___x_6994_);
                v_i_6958_ = v___x_6995_;
                v_b_6959_ = v___x_6993_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_7002_ == 0 {
                    v___x_7004_ = v___x_7001_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7005_, 0, v_a_6999_);
                    v___x_7004_ = v_reuseFailAlloc_7005_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2___boxed(
    mut v_init_7009_: *mut LeanObject,
    mut v_as_7010_: *mut LeanObject,
    mut v_sz_7011_: *mut LeanObject,
    mut v_i_7012_: *mut LeanObject,
    mut v_b_7013_: *mut LeanObject,
    mut v___y_7014_: *mut LeanObject,
    mut v___y_7015_: *mut LeanObject,
    mut v___y_7016_: *mut LeanObject,
    mut v___y_7017_: *mut LeanObject,
    mut v___y_7018_: *mut LeanObject,
    mut v___y_7019_: *mut LeanObject,
    mut v___y_7020_: *mut LeanObject,
    mut v___y_7021_: *mut LeanObject,
    mut v___y_7022_: *mut LeanObject,
    mut v___y_7023_: *mut LeanObject,
    mut v___y_7024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7025_: usize = 0;
    let mut v_i_boxed_7026_: usize = 0;
    let mut v_res_7027_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7025_ = lean_unbox_usize(v_sz_7011_);
    lean_dec(v_sz_7011_);
    v_i_boxed_7026_ = lean_unbox_usize(v_i_7012_);
    lean_dec(v_i_7012_);
    v_res_7027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__2(v_init_7009_, v_as_7010_, v_sz_boxed_7025_, v_i_boxed_7026_, v_b_7013_, v___y_7014_, v___y_7015_, v___y_7016_, v___y_7017_, v___y_7018_, v___y_7019_, v___y_7020_, v___y_7021_, v___y_7022_, v___y_7023_);
    lean_dec(v___y_7023_);
    lean_dec_ref(v___y_7022_);
    lean_dec(v___y_7021_);
    lean_dec_ref(v___y_7020_);
    lean_dec(v___y_7019_);
    lean_dec_ref(v___y_7018_);
    lean_dec(v___y_7017_);
    lean_dec_ref(v___y_7016_);
    lean_dec(v___y_7015_);
    lean_dec(v___y_7014_);
    lean_dec_ref(v_as_7010_);
    lean_dec(v_init_7009_);
    return v_res_7027_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1___boxed(
    mut v_init_7028_: *mut LeanObject,
    mut v_n_7029_: *mut LeanObject,
    mut v_b_7030_: *mut LeanObject,
    mut v___y_7031_: *mut LeanObject,
    mut v___y_7032_: *mut LeanObject,
    mut v___y_7033_: *mut LeanObject,
    mut v___y_7034_: *mut LeanObject,
    mut v___y_7035_: *mut LeanObject,
    mut v___y_7036_: *mut LeanObject,
    mut v___y_7037_: *mut LeanObject,
    mut v___y_7038_: *mut LeanObject,
    mut v___y_7039_: *mut LeanObject,
    mut v___y_7040_: *mut LeanObject,
    mut v___y_7041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7042_: *mut LeanObject = core::ptr::null_mut();
    v_res_7042_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_7028_, v_n_7029_, v_b_7030_, v___y_7031_, v___y_7032_, v___y_7033_, v___y_7034_, v___y_7035_, v___y_7036_, v___y_7037_, v___y_7038_, v___y_7039_, v___y_7040_);
    lean_dec(v___y_7040_);
    lean_dec_ref(v___y_7039_);
    lean_dec(v___y_7038_);
    lean_dec_ref(v___y_7037_);
    lean_dec(v___y_7036_);
    lean_dec_ref(v___y_7035_);
    lean_dec(v___y_7034_);
    lean_dec_ref(v___y_7033_);
    lean_dec(v___y_7032_);
    lean_dec(v___y_7031_);
    lean_dec_ref(v_n_7029_);
    lean_dec(v_init_7028_);
    return v_res_7042_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(
    mut v_as_7043_: *mut LeanObject,
    mut v_sz_7044_: usize,
    mut v_i_7045_: usize,
    mut v_b_7046_: *mut LeanObject,
    mut v___y_7047_: *mut LeanObject,
    mut v___y_7048_: *mut LeanObject,
    mut v___y_7049_: *mut LeanObject,
    mut v___y_7050_: *mut LeanObject,
    mut v___y_7051_: *mut LeanObject,
    mut v___y_7052_: *mut LeanObject,
    mut v___y_7053_: *mut LeanObject,
    mut v___y_7054_: *mut LeanObject,
    mut v___y_7055_: *mut LeanObject,
    mut v___y_7056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7058_: u8 = 0;
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7063_: u8 = 0;
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: usize = 0;
    let mut v___x_7070_: usize = 0;
    let mut v_reuseFailAlloc_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7080_: u8 = 0;
    let mut v_d_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: u8 = 0;
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7091_: u8 = 0;
    let mut v_a_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7101_: u8 = 0;
    let mut v_a_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7105_: u8 = 0;
    let mut v___x_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7109_: u8 = 0;
    let mut v_a_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7113_: u8 = 0;
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7117_: u8 = 0;
    let mut v_isSharedCheck_7118_: u8 = 0;
    let mut v_isSharedCheck_7119_: u8 = 0;
    let mut v_unused_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7058_ = lean_usize_dec_lt(v_i_7045_, v_sz_7044_);
                if v___x_7058_ == 0 {
                    v___x_7059_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7059_, 0, v_b_7046_);
                    return v___x_7059_;
                } else {
                    v_snd_7060_ = lean_ctor_get(v_b_7046_, 1);
                    v_isSharedCheck_7119_ = (!lean_is_exclusive(v_b_7046_)) as u8;
                    if v_isSharedCheck_7119_ == 0 {
                        v_unused_7120_ = lean_ctor_get(v_b_7046_, 0);
                        lean_dec(v_unused_7120_);
                        v___x_7062_ = v_b_7046_;
                        v_isShared_7063_ = v_isSharedCheck_7119_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7060_);
                        lean_dec(v_b_7046_);
                        v___x_7062_ = lean_box(0);
                        v_isShared_7063_ = v_isSharedCheck_7119_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7064_ = lean_box(0);
                v_a_7076_ = lean_array_uget(v_as_7043_, v_i_7045_);
                if lean_obj_tag(v_a_7076_) == 1 {
                    v_val_7077_ = lean_ctor_get(v_a_7076_, 0);
                    v_isSharedCheck_7118_ = (!lean_is_exclusive(v_a_7076_)) as u8;
                    if v_isSharedCheck_7118_ == 0 {
                        v___x_7079_ = v_a_7076_;
                        v_isShared_7080_ = v_isSharedCheck_7118_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_7077_);
                        lean_dec(v_a_7076_);
                        v___x_7079_ = lean_box(0);
                        v_isShared_7080_ = v_isSharedCheck_7118_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_7076_);
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_7063_ == 0 {
                    lean_ctor_set(v___x_7062_, 1, v_a_7066_);
                    lean_ctor_set(v___x_7062_, 0, v___x_7064_);
                    v___x_7068_ = v___x_7062_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7072_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 0, v___x_7064_);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 1, v_a_7066_);
                    v___x_7068_ = v_reuseFailAlloc_7072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7069_ = 1usize;
                v___x_7070_ = lean_usize_add(v_i_7045_, v___x_7069_);
                v_i_7045_ = v___x_7070_;
                v_b_7046_ = v___x_7068_;
                state = 0;
                continue;
            }
            4 => {
                v___x_7074_ = lean_unsigned_to_nat(1);
                v___x_7075_ = lean_nat_add(v_snd_7060_, v___x_7074_);
                lean_dec(v_snd_7060_);
                v_a_7066_ = v___x_7075_;
                state = 2;
                continue;
            }
            5 => {
                v_d_7081_ = lean_ctor_get(v_val_7077_, 0);
                lean_inc(v_d_7081_);
                v_p_7082_ = lean_ctor_get(v_val_7077_, 1);
                lean_inc_ref(v_p_7082_);
                lean_dec(v_val_7077_);
                v___x_7083_ = l_Int_Linear_Poly_checkCnstrOf(
                    v_p_7082_,
                    v_snd_7060_,
                    v___y_7047_,
                    v___y_7048_,
                    v___y_7049_,
                    v___y_7050_,
                    v___y_7051_,
                    v___y_7052_,
                    v___y_7053_,
                    v___y_7054_,
                    v___y_7055_,
                    v___y_7056_,
                );
                lean_dec_ref(v_p_7082_);
                if lean_obj_tag(v___x_7083_) == 0 {
                    lean_dec_ref_known(v___x_7083_, 1);
                    v___x_7084_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
                    v___x_7085_ = lean_int_dec_lt(v___x_7084_, v_d_7081_);
                    lean_dec(v_d_7081_);
                    if v___x_7085_ == 0 {
                        v___x_7086_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
                        v___x_7087_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_7086_,
                                v___y_7047_,
                                v___y_7048_,
                                v___y_7049_,
                                v___y_7050_,
                                v___y_7051_,
                                v___y_7052_,
                                v___y_7053_,
                                v___y_7054_,
                                v___y_7055_,
                                v___y_7056_,
                            );
                        if lean_obj_tag(v___x_7087_) == 0 {
                            v_a_7088_ = lean_ctor_get(v___x_7087_, 0);
                            v_isSharedCheck_7101_ = (!lean_is_exclusive(v___x_7087_)) as u8;
                            if v_isSharedCheck_7101_ == 0 {
                                v___x_7090_ = v___x_7087_;
                                v_isShared_7091_ = v_isSharedCheck_7101_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_7088_);
                                lean_dec(v___x_7087_);
                                v___x_7090_ = lean_box(0);
                                v_isShared_7091_ = v_isSharedCheck_7101_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7079_);
                            lean_del_object(v___x_7062_);
                            lean_dec(v_snd_7060_);
                            v_a_7102_ = lean_ctor_get(v___x_7087_, 0);
                            v_isSharedCheck_7109_ = (!lean_is_exclusive(v___x_7087_)) as u8;
                            if v_isSharedCheck_7109_ == 0 {
                                v___x_7104_ = v___x_7087_;
                                v_isShared_7105_ = v_isSharedCheck_7109_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_7102_);
                                lean_dec(v___x_7087_);
                                v___x_7104_ = lean_box(0);
                                v_isShared_7105_ = v_isSharedCheck_7109_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_7079_);
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_d_7081_);
                    lean_del_object(v___x_7079_);
                    lean_del_object(v___x_7062_);
                    lean_dec(v_snd_7060_);
                    v_a_7110_ = lean_ctor_get(v___x_7083_, 0);
                    v_isSharedCheck_7117_ = (!lean_is_exclusive(v___x_7083_)) as u8;
                    if v_isSharedCheck_7117_ == 0 {
                        v___x_7112_ = v___x_7083_;
                        v_isShared_7113_ = v_isSharedCheck_7117_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_7110_);
                        lean_dec(v___x_7083_);
                        v___x_7112_ = lean_box(0);
                        v_isShared_7113_ = v_isSharedCheck_7117_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_7088_) == 0 {
                    lean_del_object(v___x_7062_);
                    v_a_7092_ = lean_ctor_get(v_a_7088_, 0);
                    lean_inc(v_a_7092_);
                    lean_dec_ref_known(v_a_7088_, 1);
                    if v_isShared_7080_ == 0 {
                        lean_ctor_set(v___x_7079_, 0, v_a_7092_);
                        v___x_7094_ = v___x_7079_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7099_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7099_, 0, v_a_7092_);
                        v___x_7094_ = v_reuseFailAlloc_7099_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7090_);
                    lean_del_object(v___x_7079_);
                    lean_dec(v_snd_7060_);
                    v_a_7100_ = lean_ctor_get(v_a_7088_, 0);
                    lean_inc(v_a_7100_);
                    lean_dec_ref_known(v_a_7088_, 1);
                    v_a_7066_ = v_a_7100_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_7095_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7095_, 0, v___x_7094_);
                lean_ctor_set(v___x_7095_, 1, v_snd_7060_);
                if v_isShared_7091_ == 0 {
                    lean_ctor_set(v___x_7090_, 0, v___x_7095_);
                    v___x_7097_ = v___x_7090_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7098_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7098_, 0, v___x_7095_);
                    v___x_7097_ = v_reuseFailAlloc_7098_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7097_;
            }
            9 => {
                if v_isShared_7105_ == 0 {
                    v___x_7107_ = v___x_7104_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7108_, 0, v_a_7102_);
                    v___x_7107_ = v_reuseFailAlloc_7108_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7107_;
            }
            11 => {
                if v_isShared_7113_ == 0 {
                    v___x_7115_ = v___x_7112_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7116_, 0, v_a_7110_);
                    v___x_7115_ = v_reuseFailAlloc_7116_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5___boxed(
    mut v_as_7121_: *mut LeanObject,
    mut v_sz_7122_: *mut LeanObject,
    mut v_i_7123_: *mut LeanObject,
    mut v_b_7124_: *mut LeanObject,
    mut v___y_7125_: *mut LeanObject,
    mut v___y_7126_: *mut LeanObject,
    mut v___y_7127_: *mut LeanObject,
    mut v___y_7128_: *mut LeanObject,
    mut v___y_7129_: *mut LeanObject,
    mut v___y_7130_: *mut LeanObject,
    mut v___y_7131_: *mut LeanObject,
    mut v___y_7132_: *mut LeanObject,
    mut v___y_7133_: *mut LeanObject,
    mut v___y_7134_: *mut LeanObject,
    mut v___y_7135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7136_: usize = 0;
    let mut v_i_boxed_7137_: usize = 0;
    let mut v_res_7138_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7136_ = lean_unbox_usize(v_sz_7122_);
    lean_dec(v_sz_7122_);
    v_i_boxed_7137_ = lean_unbox_usize(v_i_7123_);
    lean_dec(v_i_7123_);
    v_res_7138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_7121_, v_sz_boxed_7136_, v_i_boxed_7137_, v_b_7124_, v___y_7125_, v___y_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_, v___y_7131_, v___y_7132_, v___y_7133_, v___y_7134_);
    lean_dec(v___y_7134_);
    lean_dec_ref(v___y_7133_);
    lean_dec(v___y_7132_);
    lean_dec_ref(v___y_7131_);
    lean_dec(v___y_7130_);
    lean_dec_ref(v___y_7129_);
    lean_dec(v___y_7128_);
    lean_dec_ref(v___y_7127_);
    lean_dec(v___y_7126_);
    lean_dec(v___y_7125_);
    lean_dec_ref(v_as_7121_);
    return v_res_7138_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(
    mut v_as_7139_: *mut LeanObject,
    mut v_sz_7140_: usize,
    mut v_i_7141_: usize,
    mut v_b_7142_: *mut LeanObject,
    mut v___y_7143_: *mut LeanObject,
    mut v___y_7144_: *mut LeanObject,
    mut v___y_7145_: *mut LeanObject,
    mut v___y_7146_: *mut LeanObject,
    mut v___y_7147_: *mut LeanObject,
    mut v___y_7148_: *mut LeanObject,
    mut v___y_7149_: *mut LeanObject,
    mut v___y_7150_: *mut LeanObject,
    mut v___y_7151_: *mut LeanObject,
    mut v___y_7152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7154_: u8 = 0;
    let mut v___x_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7159_: u8 = 0;
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: usize = 0;
    let mut v___x_7166_: usize = 0;
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7176_: u8 = 0;
    let mut v_d_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: u8 = 0;
    let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7187_: u8 = 0;
    let mut v_a_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7197_: u8 = 0;
    let mut v_a_7198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7201_: u8 = 0;
    let mut v___x_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7205_: u8 = 0;
    let mut v_a_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7209_: u8 = 0;
    let mut v___x_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7213_: u8 = 0;
    let mut v_isSharedCheck_7214_: u8 = 0;
    let mut v_isSharedCheck_7215_: u8 = 0;
    let mut v_unused_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7154_ = lean_usize_dec_lt(v_i_7141_, v_sz_7140_);
                if v___x_7154_ == 0 {
                    v___x_7155_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7155_, 0, v_b_7142_);
                    return v___x_7155_;
                } else {
                    v_snd_7156_ = lean_ctor_get(v_b_7142_, 1);
                    v_isSharedCheck_7215_ = (!lean_is_exclusive(v_b_7142_)) as u8;
                    if v_isSharedCheck_7215_ == 0 {
                        v_unused_7216_ = lean_ctor_get(v_b_7142_, 0);
                        lean_dec(v_unused_7216_);
                        v___x_7158_ = v_b_7142_;
                        v_isShared_7159_ = v_isSharedCheck_7215_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7156_);
                        lean_dec(v_b_7142_);
                        v___x_7158_ = lean_box(0);
                        v_isShared_7159_ = v_isSharedCheck_7215_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7160_ = lean_box(0);
                v_a_7172_ = lean_array_uget(v_as_7139_, v_i_7141_);
                if lean_obj_tag(v_a_7172_) == 1 {
                    v_val_7173_ = lean_ctor_get(v_a_7172_, 0);
                    v_isSharedCheck_7214_ = (!lean_is_exclusive(v_a_7172_)) as u8;
                    if v_isSharedCheck_7214_ == 0 {
                        v___x_7175_ = v_a_7172_;
                        v_isShared_7176_ = v_isSharedCheck_7214_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_7173_);
                        lean_dec(v_a_7172_);
                        v___x_7175_ = lean_box(0);
                        v_isShared_7176_ = v_isSharedCheck_7214_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_7172_);
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_7159_ == 0 {
                    lean_ctor_set(v___x_7158_, 1, v_a_7162_);
                    lean_ctor_set(v___x_7158_, 0, v___x_7160_);
                    v___x_7164_ = v___x_7158_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7168_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7168_, 0, v___x_7160_);
                    lean_ctor_set(v_reuseFailAlloc_7168_, 1, v_a_7162_);
                    v___x_7164_ = v_reuseFailAlloc_7168_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7165_ = 1usize;
                v___x_7166_ = lean_usize_add(v_i_7141_, v___x_7165_);
                v___x_7167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2_spec__5(v_as_7139_, v_sz_7140_, v___x_7166_, v___x_7164_, v___y_7143_, v___y_7144_, v___y_7145_, v___y_7146_, v___y_7147_, v___y_7148_, v___y_7149_, v___y_7150_, v___y_7151_, v___y_7152_);
                return v___x_7167_;
            }
            4 => {
                v___x_7170_ = lean_unsigned_to_nat(1);
                v___x_7171_ = lean_nat_add(v_snd_7156_, v___x_7170_);
                lean_dec(v_snd_7156_);
                v_a_7162_ = v___x_7171_;
                state = 2;
                continue;
            }
            5 => {
                v_d_7177_ = lean_ctor_get(v_val_7173_, 0);
                lean_inc(v_d_7177_);
                v_p_7178_ = lean_ctor_get(v_val_7173_, 1);
                lean_inc_ref(v_p_7178_);
                lean_dec(v_val_7173_);
                v___x_7179_ = l_Int_Linear_Poly_checkCnstrOf(
                    v_p_7178_,
                    v_snd_7156_,
                    v___y_7143_,
                    v___y_7144_,
                    v___y_7145_,
                    v___y_7146_,
                    v___y_7147_,
                    v___y_7148_,
                    v___y_7149_,
                    v___y_7150_,
                    v___y_7151_,
                    v___y_7152_,
                );
                lean_dec_ref(v_p_7178_);
                if lean_obj_tag(v___x_7179_) == 0 {
                    lean_dec_ref_known(v___x_7179_, 1);
                    v___x_7180_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__0);
                    v___x_7181_ = lean_int_dec_lt(v___x_7180_, v_d_7177_);
                    lean_dec(v_d_7177_);
                    if v___x_7181_ == 0 {
                        v___x_7182_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__3);
                        v___x_7183_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_7182_,
                                v___y_7143_,
                                v___y_7144_,
                                v___y_7145_,
                                v___y_7146_,
                                v___y_7147_,
                                v___y_7148_,
                                v___y_7149_,
                                v___y_7150_,
                                v___y_7151_,
                                v___y_7152_,
                            );
                        if lean_obj_tag(v___x_7183_) == 0 {
                            v_a_7184_ = lean_ctor_get(v___x_7183_, 0);
                            v_isSharedCheck_7197_ = (!lean_is_exclusive(v___x_7183_)) as u8;
                            if v_isSharedCheck_7197_ == 0 {
                                v___x_7186_ = v___x_7183_;
                                v_isShared_7187_ = v_isSharedCheck_7197_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_7184_);
                                lean_dec(v___x_7183_);
                                v___x_7186_ = lean_box(0);
                                v_isShared_7187_ = v_isSharedCheck_7197_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7175_);
                            lean_del_object(v___x_7158_);
                            lean_dec(v_snd_7156_);
                            v_a_7198_ = lean_ctor_get(v___x_7183_, 0);
                            v_isSharedCheck_7205_ = (!lean_is_exclusive(v___x_7183_)) as u8;
                            if v_isSharedCheck_7205_ == 0 {
                                v___x_7200_ = v___x_7183_;
                                v_isShared_7201_ = v_isSharedCheck_7205_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_7198_);
                                lean_dec(v___x_7183_);
                                v___x_7200_ = lean_box(0);
                                v_isShared_7201_ = v_isSharedCheck_7205_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_7175_);
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_d_7177_);
                    lean_del_object(v___x_7175_);
                    lean_del_object(v___x_7158_);
                    lean_dec(v_snd_7156_);
                    v_a_7206_ = lean_ctor_get(v___x_7179_, 0);
                    v_isSharedCheck_7213_ = (!lean_is_exclusive(v___x_7179_)) as u8;
                    if v_isSharedCheck_7213_ == 0 {
                        v___x_7208_ = v___x_7179_;
                        v_isShared_7209_ = v_isSharedCheck_7213_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_7206_);
                        lean_dec(v___x_7179_);
                        v___x_7208_ = lean_box(0);
                        v_isShared_7209_ = v_isSharedCheck_7213_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_7184_) == 0 {
                    lean_del_object(v___x_7158_);
                    v_a_7188_ = lean_ctor_get(v_a_7184_, 0);
                    lean_inc(v_a_7188_);
                    lean_dec_ref_known(v_a_7184_, 1);
                    if v_isShared_7176_ == 0 {
                        lean_ctor_set(v___x_7175_, 0, v_a_7188_);
                        v___x_7190_ = v___x_7175_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7195_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7195_, 0, v_a_7188_);
                        v___x_7190_ = v_reuseFailAlloc_7195_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7186_);
                    lean_del_object(v___x_7175_);
                    lean_dec(v_snd_7156_);
                    v_a_7196_ = lean_ctor_get(v_a_7184_, 0);
                    lean_inc(v_a_7196_);
                    lean_dec_ref_known(v_a_7184_, 1);
                    v_a_7162_ = v_a_7196_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_7191_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7191_, 0, v___x_7190_);
                lean_ctor_set(v___x_7191_, 1, v_snd_7156_);
                if v_isShared_7187_ == 0 {
                    lean_ctor_set(v___x_7186_, 0, v___x_7191_);
                    v___x_7193_ = v___x_7186_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7194_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7194_, 0, v___x_7191_);
                    v___x_7193_ = v_reuseFailAlloc_7194_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7193_;
            }
            9 => {
                if v_isShared_7201_ == 0 {
                    v___x_7203_ = v___x_7200_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7204_, 0, v_a_7198_);
                    v___x_7203_ = v_reuseFailAlloc_7204_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7203_;
            }
            11 => {
                if v_isShared_7209_ == 0 {
                    v___x_7211_ = v___x_7208_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7212_, 0, v_a_7206_);
                    v___x_7211_ = v_reuseFailAlloc_7212_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2___boxed(
    mut v_as_7217_: *mut LeanObject,
    mut v_sz_7218_: *mut LeanObject,
    mut v_i_7219_: *mut LeanObject,
    mut v_b_7220_: *mut LeanObject,
    mut v___y_7221_: *mut LeanObject,
    mut v___y_7222_: *mut LeanObject,
    mut v___y_7223_: *mut LeanObject,
    mut v___y_7224_: *mut LeanObject,
    mut v___y_7225_: *mut LeanObject,
    mut v___y_7226_: *mut LeanObject,
    mut v___y_7227_: *mut LeanObject,
    mut v___y_7228_: *mut LeanObject,
    mut v___y_7229_: *mut LeanObject,
    mut v___y_7230_: *mut LeanObject,
    mut v___y_7231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7232_: usize = 0;
    let mut v_i_boxed_7233_: usize = 0;
    let mut v_res_7234_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7232_ = lean_unbox_usize(v_sz_7218_);
    lean_dec(v_sz_7218_);
    v_i_boxed_7233_ = lean_unbox_usize(v_i_7219_);
    lean_dec(v_i_7219_);
    v_res_7234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_as_7217_, v_sz_boxed_7232_, v_i_boxed_7233_, v_b_7220_, v___y_7221_, v___y_7222_, v___y_7223_, v___y_7224_, v___y_7225_, v___y_7226_, v___y_7227_, v___y_7228_, v___y_7229_, v___y_7230_);
    lean_dec(v___y_7230_);
    lean_dec_ref(v___y_7229_);
    lean_dec(v___y_7228_);
    lean_dec_ref(v___y_7227_);
    lean_dec(v___y_7226_);
    lean_dec_ref(v___y_7225_);
    lean_dec(v___y_7224_);
    lean_dec_ref(v___y_7223_);
    lean_dec(v___y_7222_);
    lean_dec(v___y_7221_);
    lean_dec_ref(v_as_7217_);
    return v_res_7234_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(
    mut v_t_7235_: *mut LeanObject,
    mut v_init_7236_: *mut LeanObject,
    mut v___y_7237_: *mut LeanObject,
    mut v___y_7238_: *mut LeanObject,
    mut v___y_7239_: *mut LeanObject,
    mut v___y_7240_: *mut LeanObject,
    mut v___y_7241_: *mut LeanObject,
    mut v___y_7242_: *mut LeanObject,
    mut v___y_7243_: *mut LeanObject,
    mut v___y_7244_: *mut LeanObject,
    mut v___y_7245_: *mut LeanObject,
    mut v___y_7246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7254_: u8 = 0;
    let mut v_a_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7262_: usize = 0;
    let mut v___x_7263_: usize = 0;
    let mut v___x_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7268_: u8 = 0;
    let mut v_fst_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7278_: u8 = 0;
    let mut v_a_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7282_: u8 = 0;
    let mut v___x_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7286_: u8 = 0;
    let mut v_isSharedCheck_7287_: u8 = 0;
    let mut v_a_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7291_: u8 = 0;
    let mut v___x_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7248_ = lean_ctor_get(v_t_7235_, 0);
                v_tail_7249_ = lean_ctor_get(v_t_7235_, 1);
                lean_inc(v_init_7236_);
                v___x_7250_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1(v_init_7236_, v_root_7248_, v_init_7236_, v___y_7237_, v___y_7238_, v___y_7239_, v___y_7240_, v___y_7241_, v___y_7242_, v___y_7243_, v___y_7244_, v___y_7245_, v___y_7246_);
                lean_dec(v_init_7236_);
                if lean_obj_tag(v___x_7250_) == 0 {
                    v_a_7251_ = lean_ctor_get(v___x_7250_, 0);
                    v_isSharedCheck_7287_ = (!lean_is_exclusive(v___x_7250_)) as u8;
                    if v_isSharedCheck_7287_ == 0 {
                        v___x_7253_ = v___x_7250_;
                        v_isShared_7254_ = v_isSharedCheck_7287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7251_);
                        lean_dec(v___x_7250_);
                        v___x_7253_ = lean_box(0);
                        v_isShared_7254_ = v_isSharedCheck_7287_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7288_ = lean_ctor_get(v___x_7250_, 0);
                    v_isSharedCheck_7295_ = (!lean_is_exclusive(v___x_7250_)) as u8;
                    if v_isSharedCheck_7295_ == 0 {
                        v___x_7290_ = v___x_7250_;
                        v_isShared_7291_ = v_isSharedCheck_7295_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7288_);
                        lean_dec(v___x_7250_);
                        v___x_7290_ = lean_box(0);
                        v_isShared_7291_ = v_isSharedCheck_7295_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_7251_) == 0 {
                    v_a_7255_ = lean_ctor_get(v_a_7251_, 0);
                    lean_inc(v_a_7255_);
                    lean_dec_ref_known(v_a_7251_, 1);
                    if v_isShared_7254_ == 0 {
                        lean_ctor_set(v___x_7253_, 0, v_a_7255_);
                        v___x_7257_ = v___x_7253_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7258_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7258_, 0, v_a_7255_);
                        v___x_7257_ = v_reuseFailAlloc_7258_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7253_);
                    v_a_7259_ = lean_ctor_get(v_a_7251_, 0);
                    lean_inc(v_a_7259_);
                    lean_dec_ref_known(v_a_7251_, 1);
                    v___x_7260_ = lean_box(0);
                    v___x_7261_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7261_, 0, v___x_7260_);
                    lean_ctor_set(v___x_7261_, 1, v_a_7259_);
                    v_sz_7262_ = lean_array_size(v_tail_7249_);
                    v___x_7263_ = 0usize;
                    v___x_7264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__2(v_tail_7249_, v_sz_7262_, v___x_7263_, v___x_7261_, v___y_7237_, v___y_7238_, v___y_7239_, v___y_7240_, v___y_7241_, v___y_7242_, v___y_7243_, v___y_7244_, v___y_7245_, v___y_7246_);
                    if lean_obj_tag(v___x_7264_) == 0 {
                        v_a_7265_ = lean_ctor_get(v___x_7264_, 0);
                        v_isSharedCheck_7278_ = (!lean_is_exclusive(v___x_7264_)) as u8;
                        if v_isSharedCheck_7278_ == 0 {
                            v___x_7267_ = v___x_7264_;
                            v_isShared_7268_ = v_isSharedCheck_7278_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7265_);
                            lean_dec(v___x_7264_);
                            v___x_7267_ = lean_box(0);
                            v_isShared_7268_ = v_isSharedCheck_7278_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7279_ = lean_ctor_get(v___x_7264_, 0);
                        v_isSharedCheck_7286_ = (!lean_is_exclusive(v___x_7264_)) as u8;
                        if v_isSharedCheck_7286_ == 0 {
                            v___x_7281_ = v___x_7264_;
                            v_isShared_7282_ = v_isSharedCheck_7286_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7279_);
                            lean_dec(v___x_7264_);
                            v___x_7281_ = lean_box(0);
                            v_isShared_7282_ = v_isSharedCheck_7286_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7257_;
            }
            3 => {
                v_fst_7269_ = lean_ctor_get(v_a_7265_, 0);
                if lean_obj_tag(v_fst_7269_) == 0 {
                    v_snd_7270_ = lean_ctor_get(v_a_7265_, 1);
                    lean_inc(v_snd_7270_);
                    lean_dec(v_a_7265_);
                    if v_isShared_7268_ == 0 {
                        lean_ctor_set(v___x_7267_, 0, v_snd_7270_);
                        v___x_7272_ = v___x_7267_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7273_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7273_, 0, v_snd_7270_);
                        v___x_7272_ = v_reuseFailAlloc_7273_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7269_);
                    lean_dec(v_a_7265_);
                    v_val_7274_ = lean_ctor_get(v_fst_7269_, 0);
                    lean_inc(v_val_7274_);
                    lean_dec_ref_known(v_fst_7269_, 1);
                    if v_isShared_7268_ == 0 {
                        lean_ctor_set(v___x_7267_, 0, v_val_7274_);
                        v___x_7276_ = v___x_7267_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7277_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7277_, 0, v_val_7274_);
                        v___x_7276_ = v_reuseFailAlloc_7277_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7272_;
            }
            5 => {
                return v___x_7276_;
            }
            6 => {
                if v_isShared_7282_ == 0 {
                    v___x_7284_ = v___x_7281_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7285_, 0, v_a_7279_);
                    v___x_7284_ = v_reuseFailAlloc_7285_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7284_;
            }
            8 => {
                if v_isShared_7291_ == 0 {
                    v___x_7293_ = v___x_7290_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7294_, 0, v_a_7288_);
                    v___x_7293_ = v_reuseFailAlloc_7294_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1___boxed(
    mut v_t_7296_: *mut LeanObject,
    mut v_init_7297_: *mut LeanObject,
    mut v___y_7298_: *mut LeanObject,
    mut v___y_7299_: *mut LeanObject,
    mut v___y_7300_: *mut LeanObject,
    mut v___y_7301_: *mut LeanObject,
    mut v___y_7302_: *mut LeanObject,
    mut v___y_7303_: *mut LeanObject,
    mut v___y_7304_: *mut LeanObject,
    mut v___y_7305_: *mut LeanObject,
    mut v___y_7306_: *mut LeanObject,
    mut v___y_7307_: *mut LeanObject,
    mut v___y_7308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7309_: *mut LeanObject = core::ptr::null_mut();
    v_res_7309_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(
            v_t_7296_,
            v_init_7297_,
            v___y_7298_,
            v___y_7299_,
            v___y_7300_,
            v___y_7301_,
            v___y_7302_,
            v___y_7303_,
            v___y_7304_,
            v___y_7305_,
            v___y_7306_,
            v___y_7307_,
        );
    lean_dec(v___y_7307_);
    lean_dec_ref(v___y_7306_);
    lean_dec(v___y_7305_);
    lean_dec_ref(v___y_7304_);
    lean_dec(v___y_7303_);
    lean_dec_ref(v___y_7302_);
    lean_dec(v___y_7301_);
    lean_dec_ref(v___y_7300_);
    lean_dec(v___y_7299_);
    lean_dec(v___y_7298_);
    lean_dec_ref(v_t_7296_);
    return v_res_7309_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1() -> *mut LeanObject {
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
    v___x_7311_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__0;
    v___x_7312_ = lean_unsigned_to_nat(2);
    v___x_7313_ = lean_unsigned_to_nat(65);
    v___x_7314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1_spec__1_spec__3_spec__4___closed__1;
    v___x_7315_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_7316_ = l_mkPanicMessageWithDecl(
        v___x_7315_,
        v___x_7314_,
        v___x_7313_,
        v___x_7312_,
        v___x_7311_,
    );
    return v___x_7316_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(
    mut v_a_7317_: *mut LeanObject,
    mut v_a_7318_: *mut LeanObject,
    mut v_a_7319_: *mut LeanObject,
    mut v_a_7320_: *mut LeanObject,
    mut v_a_7321_: *mut LeanObject,
    mut v_a_7322_: *mut LeanObject,
    mut v_a_7323_: *mut LeanObject,
    mut v_a_7324_: *mut LeanObject,
    mut v_a_7325_: *mut LeanObject,
    mut v_a_7326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_7330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: u8 = 0;
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7341_: u8 = 0;
    let mut v___x_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7346_: u8 = 0;
    let mut v_unused_7347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7351_: u8 = 0;
    let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7355_: u8 = 0;
    let mut v_a_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7359_: u8 = 0;
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7328_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_7317_, v_a_7325_);
                if lean_obj_tag(v___x_7328_) == 0 {
                    v_a_7329_ = lean_ctor_get(v___x_7328_, 0);
                    lean_inc(v_a_7329_);
                    lean_dec_ref_known(v___x_7328_, 1);
                    v_vars_7330_ = lean_ctor_get(v_a_7329_, 0);
                    lean_inc_ref(v_vars_7330_);
                    v_dvds_7331_ = lean_ctor_get(v_a_7329_, 6);
                    lean_inc_ref(v_dvds_7331_);
                    lean_dec(v_a_7329_);
                    v_size_7332_ = lean_ctor_get(v_vars_7330_, 2);
                    lean_inc(v_size_7332_);
                    lean_dec_ref(v_vars_7330_);
                    v_size_7333_ = lean_ctor_get(v_dvds_7331_, 2);
                    v___x_7334_ = lean_nat_dec_eq(v_size_7332_, v_size_7333_);
                    lean_dec(v_size_7332_);
                    if v___x_7334_ == 0 {
                        lean_dec_ref(v_dvds_7331_);
                        v___x_7335_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___closed__1,
                        );
                        v___x_7336_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_7335_,
                            v_a_7317_,
                            v_a_7318_,
                            v_a_7319_,
                            v_a_7320_,
                            v_a_7321_,
                            v_a_7322_,
                            v_a_7323_,
                            v_a_7324_,
                            v_a_7325_,
                            v_a_7326_,
                        );
                        return v___x_7336_;
                    } else {
                        v___x_7337_ = lean_unsigned_to_nat(0);
                        v___x_7338_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__1(v_dvds_7331_, v___x_7337_, v_a_7317_, v_a_7318_, v_a_7319_, v_a_7320_, v_a_7321_, v_a_7322_, v_a_7323_, v_a_7324_, v_a_7325_, v_a_7326_);
                        lean_dec_ref(v_dvds_7331_);
                        if lean_obj_tag(v___x_7338_) == 0 {
                            v_isSharedCheck_7346_ = (!lean_is_exclusive(v___x_7338_)) as u8;
                            if v_isSharedCheck_7346_ == 0 {
                                v_unused_7347_ = lean_ctor_get(v___x_7338_, 0);
                                lean_dec(v_unused_7347_);
                                v___x_7340_ = v___x_7338_;
                                v_isShared_7341_ = v_isSharedCheck_7346_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_7338_);
                                v___x_7340_ = lean_box(0);
                                v_isShared_7341_ = v_isSharedCheck_7346_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_7348_ = lean_ctor_get(v___x_7338_, 0);
                            v_isSharedCheck_7355_ = (!lean_is_exclusive(v___x_7338_)) as u8;
                            if v_isSharedCheck_7355_ == 0 {
                                v___x_7350_ = v___x_7338_;
                                v_isShared_7351_ = v_isSharedCheck_7355_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_7348_);
                                lean_dec(v___x_7338_);
                                v___x_7350_ = lean_box(0);
                                v_isShared_7351_ = v_isSharedCheck_7355_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_7356_ = lean_ctor_get(v___x_7328_, 0);
                    v_isSharedCheck_7363_ = (!lean_is_exclusive(v___x_7328_)) as u8;
                    if v_isSharedCheck_7363_ == 0 {
                        v___x_7358_ = v___x_7328_;
                        v_isShared_7359_ = v_isSharedCheck_7363_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7356_);
                        lean_dec(v___x_7328_);
                        v___x_7358_ = lean_box(0);
                        v_isShared_7359_ = v_isSharedCheck_7363_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7342_ = lean_box(0);
                if v_isShared_7341_ == 0 {
                    lean_ctor_set(v___x_7340_, 0, v___x_7342_);
                    v___x_7344_ = v___x_7340_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7345_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7345_, 0, v___x_7342_);
                    v___x_7344_ = v_reuseFailAlloc_7345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7344_;
            }
            3 => {
                if v_isShared_7351_ == 0 {
                    v___x_7353_ = v___x_7350_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7354_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7354_, 0, v_a_7348_);
                    v___x_7353_ = v_reuseFailAlloc_7354_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7353_;
            }
            5 => {
                if v_isShared_7359_ == 0 {
                    v___x_7361_ = v___x_7358_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7362_, 0, v_a_7356_);
                    v___x_7361_ = v_reuseFailAlloc_7362_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkDvds___boxed(
    mut v_a_7364_: *mut LeanObject,
    mut v_a_7365_: *mut LeanObject,
    mut v_a_7366_: *mut LeanObject,
    mut v_a_7367_: *mut LeanObject,
    mut v_a_7368_: *mut LeanObject,
    mut v_a_7369_: *mut LeanObject,
    mut v_a_7370_: *mut LeanObject,
    mut v_a_7371_: *mut LeanObject,
    mut v_a_7372_: *mut LeanObject,
    mut v_a_7373_: *mut LeanObject,
    mut v_a_7374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7375_: *mut LeanObject = core::ptr::null_mut();
    v_res_7375_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(
        v_a_7364_, v_a_7365_, v_a_7366_, v_a_7367_, v_a_7368_, v_a_7369_, v_a_7370_, v_a_7371_,
        v_a_7372_, v_a_7373_,
    );
    lean_dec(v_a_7373_);
    lean_dec_ref(v_a_7372_);
    lean_dec(v_a_7371_);
    lean_dec_ref(v_a_7370_);
    lean_dec(v_a_7369_);
    lean_dec_ref(v_a_7368_);
    lean_dec(v_a_7367_);
    lean_dec_ref(v_a_7366_);
    lean_dec(v_a_7365_);
    lean_dec(v_a_7364_);
    return v_res_7375_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    v___x_7377_ = l_Int_Linear_Poly_checkCnstrOf___closed__3;
    v___x_7378_ = lean_unsigned_to_nat(6);
    v___x_7379_ = lean_unsigned_to_nat(81);
    v___x_7380_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0;
    v___x_7381_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_7382_ = l_mkPanicMessageWithDecl(
        v___x_7381_,
        v___x_7380_,
        v___x_7379_,
        v___x_7378_,
        v___x_7377_,
    );
    return v___x_7382_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    v___x_7384_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__2;
    v___x_7385_ = lean_unsigned_to_nat(6);
    v___x_7386_ = lean_unsigned_to_nat(79);
    v___x_7387_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0;
    v___x_7388_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_7389_ = l_mkPanicMessageWithDecl(
        v___x_7388_,
        v___x_7387_,
        v___x_7386_,
        v___x_7385_,
        v___x_7384_,
    );
    return v___x_7389_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(
    mut v_vars_7390_: *mut LeanObject,
    mut v_x_7391_: *mut LeanObject,
    mut v_____s_7392_: *mut LeanObject,
    mut v___y_7393_: *mut LeanObject,
    mut v___y_7394_: *mut LeanObject,
    mut v___y_7395_: *mut LeanObject,
    mut v___y_7396_: *mut LeanObject,
    mut v___y_7397_: *mut LeanObject,
    mut v___y_7398_: *mut LeanObject,
    mut v___y_7399_: *mut LeanObject,
    mut v___y_7400_: *mut LeanObject,
    mut v___y_7401_: *mut LeanObject,
    mut v___y_7402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: u8 = 0;
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7418_: u8 = 0;
    let mut v___x_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7422_: u8 = 0;
    let mut v___x_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: u8 = 0;
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_7409_ = lean_ctor_get(v_x_7391_, 0);
                v_snd_7410_ = lean_ctor_get(v_x_7391_, 1);
                v_size_7411_ = lean_ctor_get(v_vars_7390_, 2);
                v___x_7412_ = lean_nat_dec_lt(v_snd_7410_, v_size_7411_);
                if v___x_7412_ == 0 {
                    v___x_7413_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__1,
                    );
                    v___x_7414_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                        v___x_7413_,
                        v___y_7393_,
                        v___y_7394_,
                        v___y_7395_,
                        v___y_7396_,
                        v___y_7397_,
                        v___y_7398_,
                        v___y_7399_,
                        v___y_7400_,
                        v___y_7401_,
                        v___y_7402_,
                    );
                    if lean_obj_tag(v___x_7414_) == 0 {
                        lean_dec_ref_known(v___x_7414_, 1);
                        state = 1;
                        continue;
                    } else {
                        v_a_7415_ = lean_ctor_get(v___x_7414_, 0);
                        v_isSharedCheck_7422_ = (!lean_is_exclusive(v___x_7414_)) as u8;
                        if v_isSharedCheck_7422_ == 0 {
                            v___x_7417_ = v___x_7414_;
                            v_isShared_7418_ = v_isSharedCheck_7422_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_7415_);
                            lean_dec(v___x_7414_);
                            v___x_7417_ = lean_box(0);
                            v_isShared_7418_ = v_isSharedCheck_7422_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_7423_ = l_Lean_instInhabitedExpr;
                    v___x_7424_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_7423_,
                        v_vars_7390_,
                        v_snd_7410_,
                    );
                    v___x_7425_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_7409_,
                            v___x_7424_,
                        );
                    lean_dec(v___x_7424_);
                    if v___x_7425_ == 0 {
                        v___x_7426_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__3,
                        );
                        v___x_7427_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_7426_,
                                v___y_7393_,
                                v___y_7394_,
                                v___y_7395_,
                                v___y_7396_,
                                v___y_7397_,
                                v___y_7398_,
                                v___y_7399_,
                                v___y_7400_,
                                v___y_7401_,
                                v___y_7402_,
                            );
                        return v___x_7427_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7405_ = lean_unsigned_to_nat(1);
                v___x_7406_ = lean_nat_add(v_____s_7392_, v___x_7405_);
                v___x_7407_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7407_, 0, v___x_7406_);
                v___x_7408_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7408_, 0, v___x_7407_);
                return v___x_7408_;
            }
            2 => {
                if v_isShared_7418_ == 0 {
                    v___x_7420_ = v___x_7417_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7421_, 0, v_a_7415_);
                    v___x_7420_ = v_reuseFailAlloc_7421_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed(
    mut v_vars_7428_: *mut LeanObject,
    mut v_x_7429_: *mut LeanObject,
    mut v_____s_7430_: *mut LeanObject,
    mut v___y_7431_: *mut LeanObject,
    mut v___y_7432_: *mut LeanObject,
    mut v___y_7433_: *mut LeanObject,
    mut v___y_7434_: *mut LeanObject,
    mut v___y_7435_: *mut LeanObject,
    mut v___y_7436_: *mut LeanObject,
    mut v___y_7437_: *mut LeanObject,
    mut v___y_7438_: *mut LeanObject,
    mut v___y_7439_: *mut LeanObject,
    mut v___y_7440_: *mut LeanObject,
    mut v___y_7441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7442_: *mut LeanObject = core::ptr::null_mut();
    v_res_7442_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0(
        v_vars_7428_,
        v_x_7429_,
        v_____s_7430_,
        v___y_7431_,
        v___y_7432_,
        v___y_7433_,
        v___y_7434_,
        v___y_7435_,
        v___y_7436_,
        v___y_7437_,
        v___y_7438_,
        v___y_7439_,
        v___y_7440_,
    );
    lean_dec(v___y_7440_);
    lean_dec_ref(v___y_7439_);
    lean_dec(v___y_7438_);
    lean_dec_ref(v___y_7437_);
    lean_dec(v___y_7436_);
    lean_dec_ref(v___y_7435_);
    lean_dec(v___y_7434_);
    lean_dec_ref(v___y_7433_);
    lean_dec(v___y_7432_);
    lean_dec(v___y_7431_);
    lean_dec(v_____s_7430_);
    lean_dec_ref(v_x_7429_);
    lean_dec_ref(v_vars_7428_);
    return v_res_7442_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_f_7443_: *mut LeanObject,
    mut v_keys_7444_: *mut LeanObject,
    mut v_vals_7445_: *mut LeanObject,
    mut v_i_7446_: *mut LeanObject,
    mut v_acc_7447_: *mut LeanObject,
    mut v___y_7448_: *mut LeanObject,
    mut v___y_7449_: *mut LeanObject,
    mut v___y_7450_: *mut LeanObject,
    mut v___y_7451_: *mut LeanObject,
    mut v___y_7452_: *mut LeanObject,
    mut v___y_7453_: *mut LeanObject,
    mut v___y_7454_: *mut LeanObject,
    mut v___y_7455_: *mut LeanObject,
    mut v___y_7456_: *mut LeanObject,
    mut v___y_7457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7459_ = lean_array_get_size(v_keys_7444_);
                v___x_7460_ = lean_nat_dec_lt(v_i_7446_, v___x_7459_);
                if v___x_7460_ == 0 {
                    lean_dec(v_i_7446_);
                    lean_dec_ref(v_f_7443_);
                    v___x_7461_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7461_, 0, v_acc_7447_);
                    v___x_7462_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7462_, 0, v___x_7461_);
                    return v___x_7462_;
                } else {
                    v_k_7463_ = lean_array_fget_borrowed(v_keys_7444_, v_i_7446_);
                    v_v_7464_ = lean_array_fget_borrowed(v_vals_7445_, v_i_7446_);
                    lean_inc_ref(v_f_7443_);
                    lean_inc(v___y_7457_);
                    lean_inc_ref(v___y_7456_);
                    lean_inc(v___y_7455_);
                    lean_inc_ref(v___y_7454_);
                    lean_inc(v___y_7453_);
                    lean_inc_ref(v___y_7452_);
                    lean_inc(v___y_7451_);
                    lean_inc_ref(v___y_7450_);
                    lean_inc(v___y_7449_);
                    lean_inc(v___y_7448_);
                    lean_inc(v_v_7464_);
                    lean_inc(v_k_7463_);
                    v___x_7465_ = lean_apply_14(
                        v_f_7443_,
                        v_acc_7447_,
                        v_k_7463_,
                        v_v_7464_,
                        v___y_7448_,
                        v___y_7449_,
                        v___y_7450_,
                        v___y_7451_,
                        v___y_7452_,
                        v___y_7453_,
                        v___y_7454_,
                        v___y_7455_,
                        v___y_7456_,
                        v___y_7457_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_7465_) == 0 {
                        v_a_7466_ = lean_ctor_get(v___x_7465_, 0);
                        lean_inc(v_a_7466_);
                        if lean_obj_tag(v_a_7466_) == 0 {
                            lean_dec_ref_known(v_a_7466_, 1);
                            lean_dec(v_i_7446_);
                            lean_dec_ref(v_f_7443_);
                            return v___x_7465_;
                        } else {
                            lean_dec_ref_known(v___x_7465_, 1);
                            v_a_7467_ = lean_ctor_get(v_a_7466_, 0);
                            lean_inc(v_a_7467_);
                            lean_dec_ref_known(v_a_7466_, 1);
                            v___x_7468_ = lean_unsigned_to_nat(1);
                            v___x_7469_ = lean_nat_add(v_i_7446_, v___x_7468_);
                            lean_dec(v_i_7446_);
                            v_i_7446_ = v___x_7469_;
                            v_acc_7447_ = v_a_7467_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_7446_);
                        lean_dec_ref(v_f_7443_);
                        return v___x_7465_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_f_7471_: *mut LeanObject,
    mut v_keys_7472_: *mut LeanObject,
    mut v_vals_7473_: *mut LeanObject,
    mut v_i_7474_: *mut LeanObject,
    mut v_acc_7475_: *mut LeanObject,
    mut v___y_7476_: *mut LeanObject,
    mut v___y_7477_: *mut LeanObject,
    mut v___y_7478_: *mut LeanObject,
    mut v___y_7479_: *mut LeanObject,
    mut v___y_7480_: *mut LeanObject,
    mut v___y_7481_: *mut LeanObject,
    mut v___y_7482_: *mut LeanObject,
    mut v___y_7483_: *mut LeanObject,
    mut v___y_7484_: *mut LeanObject,
    mut v___y_7485_: *mut LeanObject,
    mut v___y_7486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7487_: *mut LeanObject = core::ptr::null_mut();
    v_res_7487_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7471_, v_keys_7472_, v_vals_7473_, v_i_7474_, v_acc_7475_, v___y_7476_, v___y_7477_, v___y_7478_, v___y_7479_, v___y_7480_, v___y_7481_, v___y_7482_, v___y_7483_, v___y_7484_, v___y_7485_);
    lean_dec(v___y_7485_);
    lean_dec_ref(v___y_7484_);
    lean_dec(v___y_7483_);
    lean_dec_ref(v___y_7482_);
    lean_dec(v___y_7481_);
    lean_dec_ref(v___y_7480_);
    lean_dec(v___y_7479_);
    lean_dec_ref(v___y_7478_);
    lean_dec(v___y_7477_);
    lean_dec(v___y_7476_);
    lean_dec_ref(v_vals_7473_);
    lean_dec_ref(v_keys_7472_);
    return v_res_7487_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(
    mut v_f_7488_: *mut LeanObject,
    mut v_x_7489_: *mut LeanObject,
    mut v_x_7490_: *mut LeanObject,
    mut v___y_7491_: *mut LeanObject,
    mut v___y_7492_: *mut LeanObject,
    mut v___y_7493_: *mut LeanObject,
    mut v___y_7494_: *mut LeanObject,
    mut v___y_7495_: *mut LeanObject,
    mut v___y_7496_: *mut LeanObject,
    mut v___y_7497_: *mut LeanObject,
    mut v___y_7498_: *mut LeanObject,
    mut v___y_7499_: *mut LeanObject,
    mut v___y_7500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7505_: u8 = 0;
    let mut v___x_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: u8 = 0;
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: u8 = 0;
    let mut v___x_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: usize = 0;
    let mut v___x_7519_: usize = 0;
    let mut v___x_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: usize = 0;
    let mut v___x_7522_: usize = 0;
    let mut v___x_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7524_: u8 = 0;
    let mut v_ks_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7489_) == 0 {
                    v_es_7502_ = lean_ctor_get(v_x_7489_, 0);
                    v_isSharedCheck_7524_ = (!lean_is_exclusive(v_x_7489_)) as u8;
                    if v_isSharedCheck_7524_ == 0 {
                        v___x_7504_ = v_x_7489_;
                        v_isShared_7505_ = v_isSharedCheck_7524_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_7502_);
                        lean_dec(v_x_7489_);
                        v___x_7504_ = lean_box(0);
                        v_isShared_7505_ = v_isSharedCheck_7524_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_7525_ = lean_ctor_get(v_x_7489_, 0);
                    lean_inc_ref(v_ks_7525_);
                    v_vs_7526_ = lean_ctor_get(v_x_7489_, 1);
                    lean_inc_ref(v_vs_7526_);
                    lean_dec_ref_known(v_x_7489_, 2);
                    v___x_7527_ = lean_unsigned_to_nat(0);
                    v___x_7528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7488_, v_ks_7525_, v_vs_7526_, v___x_7527_, v_x_7490_, v___y_7491_, v___y_7492_, v___y_7493_, v___y_7494_, v___y_7495_, v___y_7496_, v___y_7497_, v___y_7498_, v___y_7499_, v___y_7500_);
                    lean_dec_ref(v_vs_7526_);
                    lean_dec_ref(v_ks_7525_);
                    return v___x_7528_;
                }
            }
            1 => {
                v___x_7506_ = lean_unsigned_to_nat(0);
                v___x_7507_ = lean_array_get_size(v_es_7502_);
                v___x_7508_ = lean_nat_dec_lt(v___x_7506_, v___x_7507_);
                if v___x_7508_ == 0 {
                    lean_dec_ref(v_es_7502_);
                    lean_dec_ref(v_f_7488_);
                    if v_isShared_7505_ == 0 {
                        lean_ctor_set_tag(v___x_7504_, 1);
                        lean_ctor_set(v___x_7504_, 0, v_x_7490_);
                        v___x_7510_ = v___x_7504_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7512_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7512_, 0, v_x_7490_);
                        v___x_7510_ = v_reuseFailAlloc_7512_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7513_ = lean_nat_dec_le(v___x_7507_, v___x_7507_);
                    if v___x_7513_ == 0 {
                        if v___x_7508_ == 0 {
                            lean_dec_ref(v_es_7502_);
                            lean_dec_ref(v_f_7488_);
                            if v_isShared_7505_ == 0 {
                                lean_ctor_set_tag(v___x_7504_, 1);
                                lean_ctor_set(v___x_7504_, 0, v_x_7490_);
                                v___x_7515_ = v___x_7504_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_7517_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7517_, 0, v_x_7490_);
                                v___x_7515_ = v_reuseFailAlloc_7517_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7504_);
                            v___x_7518_ = 0usize;
                            v___x_7519_ = lean_usize_of_nat(v___x_7507_);
                            v___x_7520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_7488_, v_es_7502_, v___x_7518_, v___x_7519_, v_x_7490_, v___y_7491_, v___y_7492_, v___y_7493_, v___y_7494_, v___y_7495_, v___y_7496_, v___y_7497_, v___y_7498_, v___y_7499_, v___y_7500_);
                            lean_dec_ref(v_es_7502_);
                            return v___x_7520_;
                        }
                    } else {
                        lean_del_object(v___x_7504_);
                        v___x_7521_ = 0usize;
                        v___x_7522_ = lean_usize_of_nat(v___x_7507_);
                        v___x_7523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_7488_, v_es_7502_, v___x_7521_, v___x_7522_, v_x_7490_, v___y_7491_, v___y_7492_, v___y_7493_, v___y_7494_, v___y_7495_, v___y_7496_, v___y_7497_, v___y_7498_, v___y_7499_, v___y_7500_);
                        lean_dec_ref(v_es_7502_);
                        return v___x_7523_;
                    }
                }
            }
            2 => {
                v___x_7511_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7511_, 0, v___x_7510_);
                return v___x_7511_;
            }
            3 => {
                v___x_7516_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7516_, 0, v___x_7515_);
                return v___x_7516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_f_7529_: *mut LeanObject,
    mut v_as_7530_: *mut LeanObject,
    mut v_i_7531_: usize,
    mut v_stop_7532_: usize,
    mut v_b_7533_: *mut LeanObject,
    mut v___y_7534_: *mut LeanObject,
    mut v___y_7535_: *mut LeanObject,
    mut v___y_7536_: *mut LeanObject,
    mut v___y_7537_: *mut LeanObject,
    mut v___y_7538_: *mut LeanObject,
    mut v___y_7539_: *mut LeanObject,
    mut v___y_7540_: *mut LeanObject,
    mut v___y_7541_: *mut LeanObject,
    mut v___y_7542_: *mut LeanObject,
    mut v___y_7543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: usize = 0;
    let mut v___x_7548_: usize = 0;
    let mut v___y_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7554_: u8 = 0;
    let mut v___x_7555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_7556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7554_ = lean_usize_dec_eq(v_i_7531_, v_stop_7532_);
                if v___x_7554_ == 0 {
                    v___x_7555_ = lean_array_uget_borrowed(v_as_7530_, v_i_7531_);
                    match lean_obj_tag(v___x_7555_) {
                        0 => {
                            v_key_7556_ = lean_ctor_get(v___x_7555_, 0);
                            v_val_7557_ = lean_ctor_get(v___x_7555_, 1);
                            lean_inc_ref(v_f_7529_);
                            lean_inc(v___y_7543_);
                            lean_inc_ref(v___y_7542_);
                            lean_inc(v___y_7541_);
                            lean_inc_ref(v___y_7540_);
                            lean_inc(v___y_7539_);
                            lean_inc_ref(v___y_7538_);
                            lean_inc(v___y_7537_);
                            lean_inc_ref(v___y_7536_);
                            lean_inc(v___y_7535_);
                            lean_inc(v___y_7534_);
                            lean_inc(v_val_7557_);
                            lean_inc(v_key_7556_);
                            v___x_7558_ = lean_apply_14(
                                v_f_7529_,
                                v_b_7533_,
                                v_key_7556_,
                                v_val_7557_,
                                v___y_7534_,
                                v___y_7535_,
                                v___y_7536_,
                                v___y_7537_,
                                v___y_7538_,
                                v___y_7539_,
                                v___y_7540_,
                                v___y_7541_,
                                v___y_7542_,
                                v___y_7543_,
                                lean_box(0),
                            );
                            v___y_7551_ = v___x_7558_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_7559_ = lean_ctor_get(v___x_7555_, 0);
                            lean_inc(v_node_7559_);
                            lean_inc_ref(v_f_7529_);
                            v___x_7560_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_7529_, v_node_7559_, v_b_7533_, v___y_7534_, v___y_7535_, v___y_7536_, v___y_7537_, v___y_7538_, v___y_7539_, v___y_7540_, v___y_7541_, v___y_7542_, v___y_7543_);
                            v___y_7551_ = v___x_7560_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_7546_ = v_b_7533_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_7529_);
                    v___x_7561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7561_, 0, v_b_7533_);
                    v___x_7562_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7562_, 0, v___x_7561_);
                    return v___x_7562_;
                }
            }
            1 => {
                v___x_7547_ = 1usize;
                v___x_7548_ = lean_usize_add(v_i_7531_, v___x_7547_);
                v_i_7531_ = v___x_7548_;
                v_b_7533_ = v_a_7546_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_7551_) == 0 {
                    v_a_7552_ = lean_ctor_get(v___y_7551_, 0);
                    if lean_obj_tag(v_a_7552_) == 0 {
                        lean_dec_ref(v_f_7529_);
                        return v___y_7551_;
                    } else {
                        lean_inc_ref(v_a_7552_);
                        lean_dec_ref_known(v___y_7551_, 1);
                        v_a_7553_ = lean_ctor_get(v_a_7552_, 0);
                        lean_inc(v_a_7553_);
                        lean_dec_ref_known(v_a_7552_, 1);
                        v_a_7546_ = v_a_7553_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_7529_);
                    return v___y_7551_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_f_7563_: *mut LeanObject,
    mut v_as_7564_: *mut LeanObject,
    mut v_i_7565_: *mut LeanObject,
    mut v_stop_7566_: *mut LeanObject,
    mut v_b_7567_: *mut LeanObject,
    mut v___y_7568_: *mut LeanObject,
    mut v___y_7569_: *mut LeanObject,
    mut v___y_7570_: *mut LeanObject,
    mut v___y_7571_: *mut LeanObject,
    mut v___y_7572_: *mut LeanObject,
    mut v___y_7573_: *mut LeanObject,
    mut v___y_7574_: *mut LeanObject,
    mut v___y_7575_: *mut LeanObject,
    mut v___y_7576_: *mut LeanObject,
    mut v___y_7577_: *mut LeanObject,
    mut v___y_7578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7579_: usize = 0;
    let mut v_stop_boxed_7580_: usize = 0;
    let mut v_res_7581_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7579_ = lean_unbox_usize(v_i_7565_);
    lean_dec(v_i_7565_);
    v_stop_boxed_7580_ = lean_unbox_usize(v_stop_7566_);
    lean_dec(v_stop_7566_);
    v_res_7581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_7563_, v_as_7564_, v_i_boxed_7579_, v_stop_boxed_7580_, v_b_7567_, v___y_7568_, v___y_7569_, v___y_7570_, v___y_7571_, v___y_7572_, v___y_7573_, v___y_7574_, v___y_7575_, v___y_7576_, v___y_7577_);
    lean_dec(v___y_7577_);
    lean_dec_ref(v___y_7576_);
    lean_dec(v___y_7575_);
    lean_dec_ref(v___y_7574_);
    lean_dec(v___y_7573_);
    lean_dec_ref(v___y_7572_);
    lean_dec(v___y_7571_);
    lean_dec_ref(v___y_7570_);
    lean_dec(v___y_7569_);
    lean_dec(v___y_7568_);
    lean_dec_ref(v_as_7564_);
    return v_res_7581_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_7582_: *mut LeanObject,
    mut v_x_7583_: *mut LeanObject,
    mut v_x_7584_: *mut LeanObject,
    mut v___y_7585_: *mut LeanObject,
    mut v___y_7586_: *mut LeanObject,
    mut v___y_7587_: *mut LeanObject,
    mut v___y_7588_: *mut LeanObject,
    mut v___y_7589_: *mut LeanObject,
    mut v___y_7590_: *mut LeanObject,
    mut v___y_7591_: *mut LeanObject,
    mut v___y_7592_: *mut LeanObject,
    mut v___y_7593_: *mut LeanObject,
    mut v___y_7594_: *mut LeanObject,
    mut v___y_7595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7596_: *mut LeanObject = core::ptr::null_mut();
    v_res_7596_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_7582_, v_x_7583_, v_x_7584_, v___y_7585_, v___y_7586_, v___y_7587_, v___y_7588_, v___y_7589_, v___y_7590_, v___y_7591_, v___y_7592_, v___y_7593_, v___y_7594_);
    lean_dec(v___y_7594_);
    lean_dec_ref(v___y_7593_);
    lean_dec(v___y_7592_);
    lean_dec_ref(v___y_7591_);
    lean_dec(v___y_7590_);
    lean_dec_ref(v___y_7589_);
    lean_dec(v___y_7588_);
    lean_dec_ref(v___y_7587_);
    lean_dec(v___y_7586_);
    lean_dec(v___y_7585_);
    return v_res_7596_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(
    mut v_f_7597_: *mut LeanObject,
    mut v_s_7598_: *mut LeanObject,
    mut v_a_7599_: *mut LeanObject,
    mut v_b_7600_: *mut LeanObject,
    mut v___y_7601_: *mut LeanObject,
    mut v___y_7602_: *mut LeanObject,
    mut v___y_7603_: *mut LeanObject,
    mut v___y_7604_: *mut LeanObject,
    mut v___y_7605_: *mut LeanObject,
    mut v___y_7606_: *mut LeanObject,
    mut v___y_7607_: *mut LeanObject,
    mut v___y_7608_: *mut LeanObject,
    mut v___y_7609_: *mut LeanObject,
    mut v___y_7610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7617_: u8 = 0;
    let mut v_a_7618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7621_: u8 = 0;
    let mut v___x_7623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7628_: u8 = 0;
    let mut v_a_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7632_: u8 = 0;
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7639_: u8 = 0;
    let mut v_isSharedCheck_7640_: u8 = 0;
    let mut v_a_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7644_: u8 = 0;
    let mut v___x_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7612_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7612_, 0, v_a_7599_);
                lean_ctor_set(v___x_7612_, 1, v_b_7600_);
                lean_inc(v___y_7610_);
                lean_inc_ref(v___y_7609_);
                lean_inc(v___y_7608_);
                lean_inc_ref(v___y_7607_);
                lean_inc(v___y_7606_);
                lean_inc_ref(v___y_7605_);
                lean_inc(v___y_7604_);
                lean_inc_ref(v___y_7603_);
                lean_inc(v___y_7602_);
                lean_inc(v___y_7601_);
                v___x_7613_ = lean_apply_13(
                    v_f_7597_,
                    v___x_7612_,
                    v_s_7598_,
                    v___y_7601_,
                    v___y_7602_,
                    v___y_7603_,
                    v___y_7604_,
                    v___y_7605_,
                    v___y_7606_,
                    v___y_7607_,
                    v___y_7608_,
                    v___y_7609_,
                    v___y_7610_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_7613_) == 0 {
                    v_a_7614_ = lean_ctor_get(v___x_7613_, 0);
                    v_isSharedCheck_7640_ = (!lean_is_exclusive(v___x_7613_)) as u8;
                    if v_isSharedCheck_7640_ == 0 {
                        v___x_7616_ = v___x_7613_;
                        v_isShared_7617_ = v_isSharedCheck_7640_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7614_);
                        lean_dec(v___x_7613_);
                        v___x_7616_ = lean_box(0);
                        v_isShared_7617_ = v_isSharedCheck_7640_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7641_ = lean_ctor_get(v___x_7613_, 0);
                    v_isSharedCheck_7648_ = (!lean_is_exclusive(v___x_7613_)) as u8;
                    if v_isSharedCheck_7648_ == 0 {
                        v___x_7643_ = v___x_7613_;
                        v_isShared_7644_ = v_isSharedCheck_7648_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7641_);
                        lean_dec(v___x_7613_);
                        v___x_7643_ = lean_box(0);
                        v_isShared_7644_ = v_isSharedCheck_7648_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_7614_) == 0 {
                    v_a_7618_ = lean_ctor_get(v_a_7614_, 0);
                    v_isSharedCheck_7628_ = (!lean_is_exclusive(v_a_7614_)) as u8;
                    if v_isSharedCheck_7628_ == 0 {
                        v___x_7620_ = v_a_7614_;
                        v_isShared_7621_ = v_isSharedCheck_7628_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7618_);
                        lean_dec(v_a_7614_);
                        v___x_7620_ = lean_box(0);
                        v_isShared_7621_ = v_isSharedCheck_7628_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_7629_ = lean_ctor_get(v_a_7614_, 0);
                    v_isSharedCheck_7639_ = (!lean_is_exclusive(v_a_7614_)) as u8;
                    if v_isSharedCheck_7639_ == 0 {
                        v___x_7631_ = v_a_7614_;
                        v_isShared_7632_ = v_isSharedCheck_7639_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7629_);
                        lean_dec(v_a_7614_);
                        v___x_7631_ = lean_box(0);
                        v_isShared_7632_ = v_isSharedCheck_7639_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7621_ == 0 {
                    v___x_7623_ = v___x_7620_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7627_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7627_, 0, v_a_7618_);
                    v___x_7623_ = v_reuseFailAlloc_7627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7617_ == 0 {
                    lean_ctor_set(v___x_7616_, 0, v___x_7623_);
                    v___x_7625_ = v___x_7616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7626_, 0, v___x_7623_);
                    v___x_7625_ = v_reuseFailAlloc_7626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7625_;
            }
            5 => {
                if v_isShared_7632_ == 0 {
                    v___x_7634_ = v___x_7631_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7638_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7638_, 0, v_a_7629_);
                    v___x_7634_ = v_reuseFailAlloc_7638_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7617_ == 0 {
                    lean_ctor_set(v___x_7616_, 0, v___x_7634_);
                    v___x_7636_ = v___x_7616_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7637_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7637_, 0, v___x_7634_);
                    v___x_7636_ = v_reuseFailAlloc_7637_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7636_;
            }
            8 => {
                if v_isShared_7644_ == 0 {
                    v___x_7646_ = v___x_7643_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7647_, 0, v_a_7641_);
                    v___x_7646_ = v_reuseFailAlloc_7647_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed(
    mut v_f_7649_: *mut LeanObject,
    mut v_s_7650_: *mut LeanObject,
    mut v_a_7651_: *mut LeanObject,
    mut v_b_7652_: *mut LeanObject,
    mut v___y_7653_: *mut LeanObject,
    mut v___y_7654_: *mut LeanObject,
    mut v___y_7655_: *mut LeanObject,
    mut v___y_7656_: *mut LeanObject,
    mut v___y_7657_: *mut LeanObject,
    mut v___y_7658_: *mut LeanObject,
    mut v___y_7659_: *mut LeanObject,
    mut v___y_7660_: *mut LeanObject,
    mut v___y_7661_: *mut LeanObject,
    mut v___y_7662_: *mut LeanObject,
    mut v___y_7663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7664_: *mut LeanObject = core::ptr::null_mut();
    v_res_7664_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0(v_f_7649_, v_s_7650_, v_a_7651_, v_b_7652_, v___y_7653_, v___y_7654_, v___y_7655_, v___y_7656_, v___y_7657_, v___y_7658_, v___y_7659_, v___y_7660_, v___y_7661_, v___y_7662_);
    lean_dec(v___y_7662_);
    lean_dec_ref(v___y_7661_);
    lean_dec(v___y_7660_);
    lean_dec_ref(v___y_7659_);
    lean_dec(v___y_7658_);
    lean_dec_ref(v___y_7657_);
    lean_dec(v___y_7656_);
    lean_dec_ref(v___y_7655_);
    lean_dec(v___y_7654_);
    lean_dec(v___y_7653_);
    return v_res_7664_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(
    mut v_map_7665_: *mut LeanObject,
    mut v_init_7666_: *mut LeanObject,
    mut v_f_7667_: *mut LeanObject,
    mut v___y_7668_: *mut LeanObject,
    mut v___y_7669_: *mut LeanObject,
    mut v___y_7670_: *mut LeanObject,
    mut v___y_7671_: *mut LeanObject,
    mut v___y_7672_: *mut LeanObject,
    mut v___y_7673_: *mut LeanObject,
    mut v___y_7674_: *mut LeanObject,
    mut v___y_7675_: *mut LeanObject,
    mut v___y_7676_: *mut LeanObject,
    mut v___y_7677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7684_: u8 = 0;
    let mut v_a_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7689_: u8 = 0;
    let mut v_a_7690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7693_: u8 = 0;
    let mut v___x_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_7679_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 1);
                lean_closure_set(v___f_7679_, 0, v_f_7667_);
                lean_inc_ref(v_map_7665_);
                v___x_7680_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v___f_7679_, v_map_7665_, v_init_7666_, v___y_7668_, v___y_7669_, v___y_7670_, v___y_7671_, v___y_7672_, v___y_7673_, v___y_7674_, v___y_7675_, v___y_7676_, v___y_7677_);
                if lean_obj_tag(v___x_7680_) == 0 {
                    v_a_7681_ = lean_ctor_get(v___x_7680_, 0);
                    v_isSharedCheck_7689_ = (!lean_is_exclusive(v___x_7680_)) as u8;
                    if v_isSharedCheck_7689_ == 0 {
                        v___x_7683_ = v___x_7680_;
                        v_isShared_7684_ = v_isSharedCheck_7689_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7681_);
                        lean_dec(v___x_7680_);
                        v___x_7683_ = lean_box(0);
                        v_isShared_7684_ = v_isSharedCheck_7689_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7690_ = lean_ctor_get(v___x_7680_, 0);
                    v_isSharedCheck_7697_ = (!lean_is_exclusive(v___x_7680_)) as u8;
                    if v_isSharedCheck_7697_ == 0 {
                        v___x_7692_ = v___x_7680_;
                        v_isShared_7693_ = v_isSharedCheck_7697_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7690_);
                        lean_dec(v___x_7680_);
                        v___x_7692_ = lean_box(0);
                        v_isShared_7693_ = v_isSharedCheck_7697_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_7685_ = lean_ctor_get(v_a_7681_, 0);
                lean_inc(v_a_7685_);
                lean_dec(v_a_7681_);
                if v_isShared_7684_ == 0 {
                    lean_ctor_set(v___x_7683_, 0, v_a_7685_);
                    v___x_7687_ = v___x_7683_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7688_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7688_, 0, v_a_7685_);
                    v___x_7687_ = v_reuseFailAlloc_7688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7687_;
            }
            3 => {
                if v_isShared_7693_ == 0 {
                    v___x_7695_ = v___x_7692_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7696_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7696_, 0, v_a_7690_);
                    v___x_7695_ = v_reuseFailAlloc_7696_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg___boxed(
    mut v_map_7698_: *mut LeanObject,
    mut v_init_7699_: *mut LeanObject,
    mut v_f_7700_: *mut LeanObject,
    mut v___y_7701_: *mut LeanObject,
    mut v___y_7702_: *mut LeanObject,
    mut v___y_7703_: *mut LeanObject,
    mut v___y_7704_: *mut LeanObject,
    mut v___y_7705_: *mut LeanObject,
    mut v___y_7706_: *mut LeanObject,
    mut v___y_7707_: *mut LeanObject,
    mut v___y_7708_: *mut LeanObject,
    mut v___y_7709_: *mut LeanObject,
    mut v___y_7710_: *mut LeanObject,
    mut v___y_7711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7712_: *mut LeanObject = core::ptr::null_mut();
    v_res_7712_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_7698_, v_init_7699_, v_f_7700_, v___y_7701_, v___y_7702_, v___y_7703_, v___y_7704_, v___y_7705_, v___y_7706_, v___y_7707_, v___y_7708_, v___y_7709_, v___y_7710_);
    lean_dec(v___y_7710_);
    lean_dec_ref(v___y_7709_);
    lean_dec(v___y_7708_);
    lean_dec_ref(v___y_7707_);
    lean_dec(v___y_7706_);
    lean_dec_ref(v___y_7705_);
    lean_dec(v___y_7704_);
    lean_dec_ref(v___y_7703_);
    lean_dec(v___y_7702_);
    lean_dec(v___y_7701_);
    lean_dec_ref(v_map_7698_);
    return v_res_7712_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1() -> *mut LeanObject {
    let mut v___x_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut LeanObject = core::ptr::null_mut();
    v___x_7714_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__0;
    v___x_7715_ = lean_unsigned_to_nat(2);
    v___x_7716_ = lean_unsigned_to_nat(83);
    v___x_7717_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___closed__0;
    v___x_7718_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_7719_ = l_mkPanicMessageWithDecl(
        v___x_7718_,
        v___x_7717_,
        v___x_7716_,
        v___x_7715_,
        v___x_7714_,
    );
    return v___x_7719_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkVars(
    mut v_a_7720_: *mut LeanObject,
    mut v_a_7721_: *mut LeanObject,
    mut v_a_7722_: *mut LeanObject,
    mut v_a_7723_: *mut LeanObject,
    mut v_a_7724_: *mut LeanObject,
    mut v_a_7725_: *mut LeanObject,
    mut v_a_7726_: *mut LeanObject,
    mut v_a_7727_: *mut LeanObject,
    mut v_a_7728_: *mut LeanObject,
    mut v_a_7729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7741_: u8 = 0;
    let mut v_size_7742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: u8 = 0;
    let mut v___x_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7750_: u8 = 0;
    let mut v_a_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7754_: u8 = 0;
    let mut v___x_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7758_: u8 = 0;
    let mut v_a_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7762_: u8 = 0;
    let mut v___x_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7731_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_7720_, v_a_7728_);
                if lean_obj_tag(v___x_7731_) == 0 {
                    v_a_7732_ = lean_ctor_get(v___x_7731_, 0);
                    lean_inc(v_a_7732_);
                    lean_dec_ref_known(v___x_7731_, 1);
                    v_vars_7733_ = lean_ctor_get(v_a_7732_, 0);
                    lean_inc_ref_n(v_vars_7733_, 2);
                    v_varMap_7734_ = lean_ctor_get(v_a_7732_, 1);
                    lean_inc_ref(v_varMap_7734_);
                    lean_dec(v_a_7732_);
                    v___f_7735_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_Cutsat_checkVars___lam__0___boxed
                            as *mut core::ffi::c_void,
                        14,
                        1,
                    );
                    lean_closure_set(v___f_7735_, 0, v_vars_7733_);
                    v___x_7736_ = lean_unsigned_to_nat(0);
                    v___x_7737_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_varMap_7734_, v___x_7736_, v___f_7735_, v_a_7720_, v_a_7721_, v_a_7722_, v_a_7723_, v_a_7724_, v_a_7725_, v_a_7726_, v_a_7727_, v_a_7728_, v_a_7729_);
                    lean_dec_ref(v_varMap_7734_);
                    if lean_obj_tag(v___x_7737_) == 0 {
                        v_a_7738_ = lean_ctor_get(v___x_7737_, 0);
                        v_isSharedCheck_7750_ = (!lean_is_exclusive(v___x_7737_)) as u8;
                        if v_isSharedCheck_7750_ == 0 {
                            v___x_7740_ = v___x_7737_;
                            v_isShared_7741_ = v_isSharedCheck_7750_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7738_);
                            lean_dec(v___x_7737_);
                            v___x_7740_ = lean_box(0);
                            v_isShared_7741_ = v_isSharedCheck_7750_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_vars_7733_);
                        v_a_7751_ = lean_ctor_get(v___x_7737_, 0);
                        v_isSharedCheck_7758_ = (!lean_is_exclusive(v___x_7737_)) as u8;
                        if v_isSharedCheck_7758_ == 0 {
                            v___x_7753_ = v___x_7737_;
                            v_isShared_7754_ = v_isSharedCheck_7758_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7751_);
                            lean_dec(v___x_7737_);
                            v___x_7753_ = lean_box(0);
                            v_isShared_7754_ = v_isSharedCheck_7758_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_7759_ = lean_ctor_get(v___x_7731_, 0);
                    v_isSharedCheck_7766_ = (!lean_is_exclusive(v___x_7731_)) as u8;
                    if v_isSharedCheck_7766_ == 0 {
                        v___x_7761_ = v___x_7731_;
                        v_isShared_7762_ = v_isSharedCheck_7766_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7759_);
                        lean_dec(v___x_7731_);
                        v___x_7761_ = lean_box(0);
                        v_isShared_7762_ = v_isSharedCheck_7766_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_size_7742_ = lean_ctor_get(v_vars_7733_, 2);
                lean_inc(v_size_7742_);
                lean_dec_ref(v_vars_7733_);
                v___x_7743_ = lean_nat_dec_eq(v_size_7742_, v_a_7738_);
                lean_dec(v_a_7738_);
                lean_dec(v_size_7742_);
                if v___x_7743_ == 0 {
                    lean_del_object(v___x_7740_);
                    v___x_7744_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_checkVars___closed__1,
                    );
                    v___x_7745_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                        v___x_7744_,
                        v_a_7720_,
                        v_a_7721_,
                        v_a_7722_,
                        v_a_7723_,
                        v_a_7724_,
                        v_a_7725_,
                        v_a_7726_,
                        v_a_7727_,
                        v_a_7728_,
                        v_a_7729_,
                    );
                    return v___x_7745_;
                } else {
                    v___x_7746_ = lean_box(0);
                    if v_isShared_7741_ == 0 {
                        lean_ctor_set(v___x_7740_, 0, v___x_7746_);
                        v___x_7748_ = v___x_7740_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7749_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7749_, 0, v___x_7746_);
                        v___x_7748_ = v_reuseFailAlloc_7749_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7748_;
            }
            3 => {
                if v_isShared_7754_ == 0 {
                    v___x_7756_ = v___x_7753_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7757_, 0, v_a_7751_);
                    v___x_7756_ = v_reuseFailAlloc_7757_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7756_;
            }
            5 => {
                if v_isShared_7762_ == 0 {
                    v___x_7764_ = v___x_7761_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7765_, 0, v_a_7759_);
                    v___x_7764_ = v_reuseFailAlloc_7765_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkVars___boxed(
    mut v_a_7767_: *mut LeanObject,
    mut v_a_7768_: *mut LeanObject,
    mut v_a_7769_: *mut LeanObject,
    mut v_a_7770_: *mut LeanObject,
    mut v_a_7771_: *mut LeanObject,
    mut v_a_7772_: *mut LeanObject,
    mut v_a_7773_: *mut LeanObject,
    mut v_a_7774_: *mut LeanObject,
    mut v_a_7775_: *mut LeanObject,
    mut v_a_7776_: *mut LeanObject,
    mut v_a_7777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7778_: *mut LeanObject = core::ptr::null_mut();
    v_res_7778_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(
        v_a_7767_, v_a_7768_, v_a_7769_, v_a_7770_, v_a_7771_, v_a_7772_, v_a_7773_, v_a_7774_,
        v_a_7775_, v_a_7776_,
    );
    lean_dec(v_a_7776_);
    lean_dec_ref(v_a_7775_);
    lean_dec(v_a_7774_);
    lean_dec_ref(v_a_7773_);
    lean_dec(v_a_7772_);
    lean_dec_ref(v_a_7771_);
    lean_dec(v_a_7770_);
    lean_dec_ref(v_a_7769_);
    lean_dec(v_a_7768_);
    lean_dec(v_a_7767_);
    return v_res_7778_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(
    mut v_00_u03c3_7779_: *mut LeanObject,
    mut v_00_u03b2_7780_: *mut LeanObject,
    mut v_map_7781_: *mut LeanObject,
    mut v_init_7782_: *mut LeanObject,
    mut v_f_7783_: *mut LeanObject,
    mut v___y_7784_: *mut LeanObject,
    mut v___y_7785_: *mut LeanObject,
    mut v___y_7786_: *mut LeanObject,
    mut v___y_7787_: *mut LeanObject,
    mut v___y_7788_: *mut LeanObject,
    mut v___y_7789_: *mut LeanObject,
    mut v___y_7790_: *mut LeanObject,
    mut v___y_7791_: *mut LeanObject,
    mut v___y_7792_: *mut LeanObject,
    mut v___y_7793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7795_: *mut LeanObject = core::ptr::null_mut();
    v___x_7795_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___redArg(v_map_7781_, v_init_7782_, v_f_7783_, v___y_7784_, v___y_7785_, v___y_7786_, v___y_7787_, v___y_7788_, v___y_7789_, v___y_7790_, v___y_7791_, v___y_7792_, v___y_7793_);
    return v___x_7795_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0___boxed(
    mut v_00_u03c3_7796_: *mut LeanObject,
    mut v_00_u03b2_7797_: *mut LeanObject,
    mut v_map_7798_: *mut LeanObject,
    mut v_init_7799_: *mut LeanObject,
    mut v_f_7800_: *mut LeanObject,
    mut v___y_7801_: *mut LeanObject,
    mut v___y_7802_: *mut LeanObject,
    mut v___y_7803_: *mut LeanObject,
    mut v___y_7804_: *mut LeanObject,
    mut v___y_7805_: *mut LeanObject,
    mut v___y_7806_: *mut LeanObject,
    mut v___y_7807_: *mut LeanObject,
    mut v___y_7808_: *mut LeanObject,
    mut v___y_7809_: *mut LeanObject,
    mut v___y_7810_: *mut LeanObject,
    mut v___y_7811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7812_: *mut LeanObject = core::ptr::null_mut();
    v_res_7812_ =
        l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0(
            v_00_u03c3_7796_,
            v_00_u03b2_7797_,
            v_map_7798_,
            v_init_7799_,
            v_f_7800_,
            v___y_7801_,
            v___y_7802_,
            v___y_7803_,
            v___y_7804_,
            v___y_7805_,
            v___y_7806_,
            v___y_7807_,
            v___y_7808_,
            v___y_7809_,
            v___y_7810_,
        );
    lean_dec(v___y_7810_);
    lean_dec_ref(v___y_7809_);
    lean_dec(v___y_7808_);
    lean_dec_ref(v___y_7807_);
    lean_dec(v___y_7806_);
    lean_dec_ref(v___y_7805_);
    lean_dec(v___y_7804_);
    lean_dec_ref(v___y_7803_);
    lean_dec(v___y_7802_);
    lean_dec(v___y_7801_);
    lean_dec_ref(v_map_7798_);
    return v_res_7812_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(
    mut v_map_7813_: *mut LeanObject,
    mut v_f_7814_: *mut LeanObject,
    mut v_init_7815_: *mut LeanObject,
    mut v___y_7816_: *mut LeanObject,
    mut v___y_7817_: *mut LeanObject,
    mut v___y_7818_: *mut LeanObject,
    mut v___y_7819_: *mut LeanObject,
    mut v___y_7820_: *mut LeanObject,
    mut v___y_7821_: *mut LeanObject,
    mut v___y_7822_: *mut LeanObject,
    mut v___y_7823_: *mut LeanObject,
    mut v___y_7824_: *mut LeanObject,
    mut v___y_7825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7827_: *mut LeanObject = core::ptr::null_mut();
    v___x_7827_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_7814_, v_map_7813_, v_init_7815_, v___y_7816_, v___y_7817_, v___y_7818_, v___y_7819_, v___y_7820_, v___y_7821_, v___y_7822_, v___y_7823_, v___y_7824_, v___y_7825_);
    return v___x_7827_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg___boxed(
    mut v_map_7828_: *mut LeanObject,
    mut v_f_7829_: *mut LeanObject,
    mut v_init_7830_: *mut LeanObject,
    mut v___y_7831_: *mut LeanObject,
    mut v___y_7832_: *mut LeanObject,
    mut v___y_7833_: *mut LeanObject,
    mut v___y_7834_: *mut LeanObject,
    mut v___y_7835_: *mut LeanObject,
    mut v___y_7836_: *mut LeanObject,
    mut v___y_7837_: *mut LeanObject,
    mut v___y_7838_: *mut LeanObject,
    mut v___y_7839_: *mut LeanObject,
    mut v___y_7840_: *mut LeanObject,
    mut v___y_7841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7842_: *mut LeanObject = core::ptr::null_mut();
    v_res_7842_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___redArg(v_map_7828_, v_f_7829_, v_init_7830_, v___y_7831_, v___y_7832_, v___y_7833_, v___y_7834_, v___y_7835_, v___y_7836_, v___y_7837_, v___y_7838_, v___y_7839_, v___y_7840_);
    lean_dec(v___y_7840_);
    lean_dec_ref(v___y_7839_);
    lean_dec(v___y_7838_);
    lean_dec_ref(v___y_7837_);
    lean_dec(v___y_7836_);
    lean_dec_ref(v___y_7835_);
    lean_dec(v___y_7834_);
    lean_dec_ref(v___y_7833_);
    lean_dec(v___y_7832_);
    lean_dec(v___y_7831_);
    return v_res_7842_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(
    mut v_00_u03c3_7843_: *mut LeanObject,
    mut v_00_u03c3_7844_: *mut LeanObject,
    mut v_00_u03b2_7845_: *mut LeanObject,
    mut v_map_7846_: *mut LeanObject,
    mut v_f_7847_: *mut LeanObject,
    mut v_init_7848_: *mut LeanObject,
    mut v___y_7849_: *mut LeanObject,
    mut v___y_7850_: *mut LeanObject,
    mut v___y_7851_: *mut LeanObject,
    mut v___y_7852_: *mut LeanObject,
    mut v___y_7853_: *mut LeanObject,
    mut v___y_7854_: *mut LeanObject,
    mut v___y_7855_: *mut LeanObject,
    mut v___y_7856_: *mut LeanObject,
    mut v___y_7857_: *mut LeanObject,
    mut v___y_7858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    v___x_7860_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_7847_, v_map_7846_, v_init_7848_, v___y_7849_, v___y_7850_, v___y_7851_, v___y_7852_, v___y_7853_, v___y_7854_, v___y_7855_, v___y_7856_, v___y_7857_, v___y_7858_);
    return v___x_7860_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_7861_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_7862_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b2_7863_: *mut LeanObject = *_args.add(2);
    let mut v_map_7864_: *mut LeanObject = *_args.add(3);
    let mut v_f_7865_: *mut LeanObject = *_args.add(4);
    let mut v_init_7866_: *mut LeanObject = *_args.add(5);
    let mut v___y_7867_: *mut LeanObject = *_args.add(6);
    let mut v___y_7868_: *mut LeanObject = *_args.add(7);
    let mut v___y_7869_: *mut LeanObject = *_args.add(8);
    let mut v___y_7870_: *mut LeanObject = *_args.add(9);
    let mut v___y_7871_: *mut LeanObject = *_args.add(10);
    let mut v___y_7872_: *mut LeanObject = *_args.add(11);
    let mut v___y_7873_: *mut LeanObject = *_args.add(12);
    let mut v___y_7874_: *mut LeanObject = *_args.add(13);
    let mut v___y_7875_: *mut LeanObject = *_args.add(14);
    let mut v___y_7876_: *mut LeanObject = *_args.add(15);
    let mut v___y_7877_: *mut LeanObject = *_args.add(16);
    let mut v_res_7878_: *mut LeanObject = core::ptr::null_mut();
    v_res_7878_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0(v_00_u03c3_7861_, v_00_u03c3_7862_, v_00_u03b2_7863_, v_map_7864_, v_f_7865_, v_init_7866_, v___y_7867_, v___y_7868_, v___y_7869_, v___y_7870_, v___y_7871_, v___y_7872_, v___y_7873_, v___y_7874_, v___y_7875_, v___y_7876_);
    lean_dec(v___y_7876_);
    lean_dec_ref(v___y_7875_);
    lean_dec(v___y_7874_);
    lean_dec_ref(v___y_7873_);
    lean_dec(v___y_7872_);
    lean_dec_ref(v___y_7871_);
    lean_dec(v___y_7870_);
    lean_dec_ref(v___y_7869_);
    lean_dec(v___y_7868_);
    lean_dec(v___y_7867_);
    return v_res_7878_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(
    mut v_00_u03c3_7879_: *mut LeanObject,
    mut v_00_u03c3_7880_: *mut LeanObject,
    mut v_00_u03b1_7881_: *mut LeanObject,
    mut v_00_u03b2_7882_: *mut LeanObject,
    mut v_f_7883_: *mut LeanObject,
    mut v_x_7884_: *mut LeanObject,
    mut v_x_7885_: *mut LeanObject,
    mut v___y_7886_: *mut LeanObject,
    mut v___y_7887_: *mut LeanObject,
    mut v___y_7888_: *mut LeanObject,
    mut v___y_7889_: *mut LeanObject,
    mut v___y_7890_: *mut LeanObject,
    mut v___y_7891_: *mut LeanObject,
    mut v___y_7892_: *mut LeanObject,
    mut v___y_7893_: *mut LeanObject,
    mut v___y_7894_: *mut LeanObject,
    mut v___y_7895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7897_: *mut LeanObject = core::ptr::null_mut();
    v___x_7897_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___redArg(v_f_7883_, v_x_7884_, v_x_7885_, v___y_7886_, v___y_7887_, v___y_7888_, v___y_7889_, v___y_7890_, v___y_7891_, v___y_7892_, v___y_7893_, v___y_7894_, v___y_7895_);
    return v___x_7897_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_7898_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_7899_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b1_7900_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03b2_7901_: *mut LeanObject = *_args.add(3);
    let mut v_f_7902_: *mut LeanObject = *_args.add(4);
    let mut v_x_7903_: *mut LeanObject = *_args.add(5);
    let mut v_x_7904_: *mut LeanObject = *_args.add(6);
    let mut v___y_7905_: *mut LeanObject = *_args.add(7);
    let mut v___y_7906_: *mut LeanObject = *_args.add(8);
    let mut v___y_7907_: *mut LeanObject = *_args.add(9);
    let mut v___y_7908_: *mut LeanObject = *_args.add(10);
    let mut v___y_7909_: *mut LeanObject = *_args.add(11);
    let mut v___y_7910_: *mut LeanObject = *_args.add(12);
    let mut v___y_7911_: *mut LeanObject = *_args.add(13);
    let mut v___y_7912_: *mut LeanObject = *_args.add(14);
    let mut v___y_7913_: *mut LeanObject = *_args.add(15);
    let mut v___y_7914_: *mut LeanObject = *_args.add(16);
    let mut v___y_7915_: *mut LeanObject = *_args.add(17);
    let mut v_res_7916_: *mut LeanObject = core::ptr::null_mut();
    v_res_7916_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1(v_00_u03c3_7898_, v_00_u03c3_7899_, v_00_u03b1_7900_, v_00_u03b2_7901_, v_f_7902_, v_x_7903_, v_x_7904_, v___y_7905_, v___y_7906_, v___y_7907_, v___y_7908_, v___y_7909_, v___y_7910_, v___y_7911_, v___y_7912_, v___y_7913_, v___y_7914_);
    lean_dec(v___y_7914_);
    lean_dec_ref(v___y_7913_);
    lean_dec(v___y_7912_);
    lean_dec_ref(v___y_7911_);
    lean_dec(v___y_7910_);
    lean_dec_ref(v___y_7909_);
    lean_dec(v___y_7908_);
    lean_dec_ref(v___y_7907_);
    lean_dec(v___y_7906_);
    lean_dec(v___y_7905_);
    return v_res_7916_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_7917_: *mut LeanObject,
    mut v_00_u03b2_7918_: *mut LeanObject,
    mut v_00_u03c3_7919_: *mut LeanObject,
    mut v_00_u03c3_7920_: *mut LeanObject,
    mut v_f_7921_: *mut LeanObject,
    mut v_as_7922_: *mut LeanObject,
    mut v_i_7923_: usize,
    mut v_stop_7924_: usize,
    mut v_b_7925_: *mut LeanObject,
    mut v___y_7926_: *mut LeanObject,
    mut v___y_7927_: *mut LeanObject,
    mut v___y_7928_: *mut LeanObject,
    mut v___y_7929_: *mut LeanObject,
    mut v___y_7930_: *mut LeanObject,
    mut v___y_7931_: *mut LeanObject,
    mut v___y_7932_: *mut LeanObject,
    mut v___y_7933_: *mut LeanObject,
    mut v___y_7934_: *mut LeanObject,
    mut v___y_7935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7937_: *mut LeanObject = core::ptr::null_mut();
    v___x_7937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___redArg(v_f_7921_, v_as_7922_, v_i_7923_, v_stop_7924_, v_b_7925_, v___y_7926_, v___y_7927_, v___y_7928_, v___y_7929_, v___y_7930_, v___y_7931_, v___y_7932_, v___y_7933_, v___y_7934_, v___y_7935_);
    return v___x_7937_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_7938_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03b2_7939_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03c3_7940_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03c3_7941_: *mut LeanObject = *_args.add(3);
    let mut v_f_7942_: *mut LeanObject = *_args.add(4);
    let mut v_as_7943_: *mut LeanObject = *_args.add(5);
    let mut v_i_7944_: *mut LeanObject = *_args.add(6);
    let mut v_stop_7945_: *mut LeanObject = *_args.add(7);
    let mut v_b_7946_: *mut LeanObject = *_args.add(8);
    let mut v___y_7947_: *mut LeanObject = *_args.add(9);
    let mut v___y_7948_: *mut LeanObject = *_args.add(10);
    let mut v___y_7949_: *mut LeanObject = *_args.add(11);
    let mut v___y_7950_: *mut LeanObject = *_args.add(12);
    let mut v___y_7951_: *mut LeanObject = *_args.add(13);
    let mut v___y_7952_: *mut LeanObject = *_args.add(14);
    let mut v___y_7953_: *mut LeanObject = *_args.add(15);
    let mut v___y_7954_: *mut LeanObject = *_args.add(16);
    let mut v___y_7955_: *mut LeanObject = *_args.add(17);
    let mut v___y_7956_: *mut LeanObject = *_args.add(18);
    let mut v___y_7957_: *mut LeanObject = *_args.add(19);
    let mut v_i_boxed_7958_: usize = 0;
    let mut v_stop_boxed_7959_: usize = 0;
    let mut v_res_7960_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7958_ = lean_unbox_usize(v_i_7944_);
    lean_dec(v_i_7944_);
    v_stop_boxed_7959_ = lean_unbox_usize(v_stop_7945_);
    lean_dec(v_stop_7945_);
    v_res_7960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_7938_, v_00_u03b2_7939_, v_00_u03c3_7940_, v_00_u03c3_7941_, v_f_7942_, v_as_7943_, v_i_boxed_7958_, v_stop_boxed_7959_, v_b_7946_, v___y_7947_, v___y_7948_, v___y_7949_, v___y_7950_, v___y_7951_, v___y_7952_, v___y_7953_, v___y_7954_, v___y_7955_, v___y_7956_);
    lean_dec(v___y_7956_);
    lean_dec_ref(v___y_7955_);
    lean_dec(v___y_7954_);
    lean_dec_ref(v___y_7953_);
    lean_dec(v___y_7952_);
    lean_dec_ref(v___y_7951_);
    lean_dec(v___y_7950_);
    lean_dec_ref(v___y_7949_);
    lean_dec(v___y_7948_);
    lean_dec(v___y_7947_);
    lean_dec_ref(v_as_7943_);
    return v_res_7960_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03c3_7961_: *mut LeanObject,
    mut v_00_u03c3_7962_: *mut LeanObject,
    mut v_00_u03b1_7963_: *mut LeanObject,
    mut v_00_u03b2_7964_: *mut LeanObject,
    mut v_f_7965_: *mut LeanObject,
    mut v_keys_7966_: *mut LeanObject,
    mut v_vals_7967_: *mut LeanObject,
    mut v_heq_7968_: *mut LeanObject,
    mut v_i_7969_: *mut LeanObject,
    mut v_acc_7970_: *mut LeanObject,
    mut v___y_7971_: *mut LeanObject,
    mut v___y_7972_: *mut LeanObject,
    mut v___y_7973_: *mut LeanObject,
    mut v___y_7974_: *mut LeanObject,
    mut v___y_7975_: *mut LeanObject,
    mut v___y_7976_: *mut LeanObject,
    mut v___y_7977_: *mut LeanObject,
    mut v___y_7978_: *mut LeanObject,
    mut v___y_7979_: *mut LeanObject,
    mut v___y_7980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7982_: *mut LeanObject = core::ptr::null_mut();
    v___x_7982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___redArg(v_f_7965_, v_keys_7966_, v_vals_7967_, v_i_7969_, v_acc_7970_, v___y_7971_, v___y_7972_, v___y_7973_, v___y_7974_, v___y_7975_, v___y_7976_, v___y_7977_, v___y_7978_, v___y_7979_, v___y_7980_);
    return v___x_7982_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_7983_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_7984_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b1_7985_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03b2_7986_: *mut LeanObject = *_args.add(3);
    let mut v_f_7987_: *mut LeanObject = *_args.add(4);
    let mut v_keys_7988_: *mut LeanObject = *_args.add(5);
    let mut v_vals_7989_: *mut LeanObject = *_args.add(6);
    let mut v_heq_7990_: *mut LeanObject = *_args.add(7);
    let mut v_i_7991_: *mut LeanObject = *_args.add(8);
    let mut v_acc_7992_: *mut LeanObject = *_args.add(9);
    let mut v___y_7993_: *mut LeanObject = *_args.add(10);
    let mut v___y_7994_: *mut LeanObject = *_args.add(11);
    let mut v___y_7995_: *mut LeanObject = *_args.add(12);
    let mut v___y_7996_: *mut LeanObject = *_args.add(13);
    let mut v___y_7997_: *mut LeanObject = *_args.add(14);
    let mut v___y_7998_: *mut LeanObject = *_args.add(15);
    let mut v___y_7999_: *mut LeanObject = *_args.add(16);
    let mut v___y_8000_: *mut LeanObject = *_args.add(17);
    let mut v___y_8001_: *mut LeanObject = *_args.add(18);
    let mut v___y_8002_: *mut LeanObject = *_args.add(19);
    let mut v___y_8003_: *mut LeanObject = *_args.add(20);
    let mut v_res_8004_: *mut LeanObject = core::ptr::null_mut();
    v_res_8004_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkVars_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_7983_, v_00_u03c3_7984_, v_00_u03b1_7985_, v_00_u03b2_7986_, v_f_7987_, v_keys_7988_, v_vals_7989_, v_heq_7990_, v_i_7991_, v_acc_7992_, v___y_7993_, v___y_7994_, v___y_7995_, v___y_7996_, v___y_7997_, v___y_7998_, v___y_7999_, v___y_8000_, v___y_8001_, v___y_8002_);
    lean_dec(v___y_8002_);
    lean_dec_ref(v___y_8001_);
    lean_dec(v___y_8000_);
    lean_dec_ref(v___y_7999_);
    lean_dec(v___y_7998_);
    lean_dec_ref(v___y_7997_);
    lean_dec(v___y_7996_);
    lean_dec_ref(v___y_7995_);
    lean_dec(v___y_7994_);
    lean_dec(v___y_7993_);
    lean_dec_ref(v_vals_7989_);
    lean_dec_ref(v_keys_7988_);
    return v_res_8004_;
}
pub unsafe fn l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(
    mut v_a_8005_: *mut LeanObject,
    mut v_x_8006_: *mut LeanObject,
) -> u8 {
    let mut v___x_8007_: u8 = 0;
    let mut v_head_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8006_) == 0 {
                    v___x_8007_ = 0;
                    return v___x_8007_;
                } else {
                    v_head_8008_ = lean_ctor_get(v_x_8006_, 0);
                    v_tail_8009_ = lean_ctor_get(v_x_8006_, 1);
                    v___x_8010_ = lean_nat_dec_eq(v_a_8005_, v_head_8008_);
                    if v___x_8010_ == 0 {
                        v_x_8006_ = v_tail_8009_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_8010_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0___boxed(
    mut v_a_8012_: *mut LeanObject,
    mut v_x_8013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8014_: u8 = 0;
    let mut v_r_8015_: *mut LeanObject = core::ptr::null_mut();
    v_res_8014_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(
        v_a_8012_, v_x_8013_,
    );
    lean_dec(v_x_8013_);
    lean_dec(v_a_8012_);
    v_r_8015_ = lean_box((v_res_8014_) as usize);
    return v_r_8015_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2()
-> *mut LeanObject {
    let mut v___x_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    v___x_8018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__1;
    v___x_8019_ = lean_unsigned_to_nat(6);
    v___x_8020_ = lean_unsigned_to_nat(94);
    v___x_8021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0;
    v___x_8022_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_8023_ = l_mkPanicMessageWithDecl(
        v___x_8022_,
        v___x_8021_,
        v___x_8020_,
        v___x_8019_,
        v___x_8018_,
    );
    return v___x_8023_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4()
-> *mut LeanObject {
    let mut v___x_8025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8030_: *mut LeanObject = core::ptr::null_mut();
    v___x_8025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__3;
    v___x_8026_ = lean_unsigned_to_nat(6);
    v___x_8027_ = lean_unsigned_to_nat(91);
    v___x_8028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0;
    v___x_8029_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_8030_ = l_mkPanicMessageWithDecl(
        v___x_8029_,
        v___x_8028_,
        v___x_8027_,
        v___x_8026_,
        v___x_8025_,
    );
    return v___x_8030_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6()
-> *mut LeanObject {
    let mut v___x_8032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut LeanObject = core::ptr::null_mut();
    v___x_8032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__5;
    v___x_8033_ = lean_unsigned_to_nat(6);
    v___x_8034_ = lean_unsigned_to_nat(92);
    v___x_8035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0;
    v___x_8036_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_8037_ = l_mkPanicMessageWithDecl(
        v___x_8036_,
        v___x_8035_,
        v___x_8034_,
        v___x_8033_,
        v___x_8032_,
    );
    return v___x_8037_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8()
-> *mut LeanObject {
    let mut v___x_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8044_: *mut LeanObject = core::ptr::null_mut();
    v___x_8039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__7;
    v___x_8040_ = lean_unsigned_to_nat(6);
    v___x_8041_ = lean_unsigned_to_nat(93);
    v___x_8042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0;
    v___x_8043_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_8044_ = l_mkPanicMessageWithDecl(
        v___x_8043_,
        v___x_8042_,
        v___x_8041_,
        v___x_8040_,
        v___x_8039_,
    );
    return v___x_8044_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(
    mut v_a_8045_: *mut LeanObject,
    mut v_as_8046_: *mut LeanObject,
    mut v_sz_8047_: usize,
    mut v_i_8048_: usize,
    mut v_b_8049_: *mut LeanObject,
    mut v___y_8050_: *mut LeanObject,
    mut v___y_8051_: *mut LeanObject,
    mut v___y_8052_: *mut LeanObject,
    mut v___y_8053_: *mut LeanObject,
    mut v___y_8054_: *mut LeanObject,
    mut v___y_8055_: *mut LeanObject,
    mut v___y_8056_: *mut LeanObject,
    mut v___y_8057_: *mut LeanObject,
    mut v___y_8058_: *mut LeanObject,
    mut v___y_8059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8061_: u8 = 0;
    let mut v___x_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8066_: u8 = 0;
    let mut v___x_8067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: usize = 0;
    let mut v___x_8073_: usize = 0;
    let mut v_reuseFailAlloc_8075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8084_: u8 = 0;
    let mut v___x_8085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8091_: u8 = 0;
    let mut v_a_8092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8095_: u8 = 0;
    let mut v___x_8097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8099_: u8 = 0;
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: u8 = 0;
    let mut v___x_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: u8 = 0;
    let mut v___x_8110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8113_: u8 = 0;
    let mut v___x_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: u8 = 0;
    let mut v_isSharedCheck_8119_: u8 = 0;
    let mut v_unused_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8061_ = lean_usize_dec_lt(v_i_8048_, v_sz_8047_);
                if v___x_8061_ == 0 {
                    v___x_8062_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8062_, 0, v_b_8049_);
                    return v___x_8062_;
                } else {
                    v_snd_8063_ = lean_ctor_get(v_b_8049_, 1);
                    v_isSharedCheck_8119_ = (!lean_is_exclusive(v_b_8049_)) as u8;
                    if v_isSharedCheck_8119_ == 0 {
                        v_unused_8120_ = lean_ctor_get(v_b_8049_, 0);
                        lean_dec(v_unused_8120_);
                        v___x_8065_ = v_b_8049_;
                        v_isShared_8066_ = v_isSharedCheck_8119_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_8063_);
                        lean_dec(v_b_8049_);
                        v___x_8065_ = lean_box(0);
                        v_isShared_8066_ = v_isSharedCheck_8119_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8067_ = lean_box(0);
                v_a_8103_ = lean_array_uget_borrowed(v_as_8046_, v_i_8048_);
                if lean_obj_tag(v_a_8103_) == 1 {
                    v_val_8104_ = lean_ctor_get(v_a_8103_, 0);
                    v_p_8105_ = lean_ctor_get(v_val_8104_, 0);
                    v___x_8106_ = l_Int_Linear_Poly_isSorted(v_p_8105_);
                    if v___x_8106_ == 0 {
                        v___x_8107_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
                        v___x_8108_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_8107_,
                                v___y_8050_,
                                v___y_8051_,
                                v___y_8052_,
                                v___y_8053_,
                                v___y_8054_,
                                v___y_8055_,
                                v___y_8056_,
                                v___y_8057_,
                                v___y_8058_,
                                v___y_8059_,
                            );
                        v___y_8080_ = v___x_8108_;
                        state = 5;
                        continue;
                    } else {
                        v___x_8109_ = l_Int_Linear_Poly_checkCoeffs(v_p_8105_);
                        if v___x_8109_ == 0 {
                            v___x_8110_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
                            v___x_8111_ =
                                l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                    v___x_8110_,
                                    v___y_8050_,
                                    v___y_8051_,
                                    v___y_8052_,
                                    v___y_8053_,
                                    v___y_8054_,
                                    v___y_8055_,
                                    v___y_8056_,
                                    v___y_8057_,
                                    v___y_8058_,
                                    v___y_8059_,
                                );
                            v___y_8080_ = v___x_8111_;
                            state = 5;
                            continue;
                        } else {
                            v_elimStack_8112_ = lean_ctor_get(v_a_8045_, 11);
                            v___x_8113_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_8063_, v_elimStack_8112_);
                            if v___x_8113_ == 0 {
                                v___x_8114_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
                                v___x_8115_ =
                                    l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                        v___x_8114_,
                                        v___y_8050_,
                                        v___y_8051_,
                                        v___y_8052_,
                                        v___y_8053_,
                                        v___y_8054_,
                                        v___y_8055_,
                                        v___y_8056_,
                                        v___y_8057_,
                                        v___y_8058_,
                                        v___y_8059_,
                                    );
                                v___y_8080_ = v___x_8115_;
                                state = 5;
                                continue;
                            } else {
                                v___x_8116_ = l_Int_Linear_Poly_coeff(v_p_8105_, v_snd_8063_);
                                v___x_8117_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Int_Linear_Poly_checkCoeffs___closed__0
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Int_Linear_Poly_checkCoeffs___closed__0_once
                                    ),
                                    _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                                );
                                v___x_8118_ = lean_int_dec_eq(v___x_8116_, v___x_8117_);
                                lean_dec(v___x_8116_);
                                if v___x_8118_ == 0 {
                                    if v___x_8113_ == 0 {
                                        state = 10;
                                        continue;
                                    } else {
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_8066_ == 0 {
                    lean_ctor_set(v___x_8065_, 1, v_a_8069_);
                    lean_ctor_set(v___x_8065_, 0, v___x_8067_);
                    v___x_8071_ = v___x_8065_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8075_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8075_, 0, v___x_8067_);
                    lean_ctor_set(v_reuseFailAlloc_8075_, 1, v_a_8069_);
                    v___x_8071_ = v_reuseFailAlloc_8075_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8072_ = 1usize;
                v___x_8073_ = lean_usize_add(v_i_8048_, v___x_8072_);
                v_i_8048_ = v___x_8073_;
                v_b_8049_ = v___x_8071_;
                state = 0;
                continue;
            }
            4 => {
                v___x_8077_ = lean_unsigned_to_nat(1);
                v___x_8078_ = lean_nat_add(v_snd_8063_, v___x_8077_);
                lean_dec(v_snd_8063_);
                v_a_8069_ = v___x_8078_;
                state = 2;
                continue;
            }
            5 => {
                if lean_obj_tag(v___y_8080_) == 0 {
                    v_a_8081_ = lean_ctor_get(v___y_8080_, 0);
                    v_isSharedCheck_8091_ = (!lean_is_exclusive(v___y_8080_)) as u8;
                    if v_isSharedCheck_8091_ == 0 {
                        v___x_8083_ = v___y_8080_;
                        v_isShared_8084_ = v_isSharedCheck_8091_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8081_);
                        lean_dec(v___y_8080_);
                        v___x_8083_ = lean_box(0);
                        v_isShared_8084_ = v_isSharedCheck_8091_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8065_);
                    lean_dec(v_snd_8063_);
                    v_a_8092_ = lean_ctor_get(v___y_8080_, 0);
                    v_isSharedCheck_8099_ = (!lean_is_exclusive(v___y_8080_)) as u8;
                    if v_isSharedCheck_8099_ == 0 {
                        v___x_8094_ = v___y_8080_;
                        v_isShared_8095_ = v_isSharedCheck_8099_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_8092_);
                        lean_dec(v___y_8080_);
                        v___x_8094_ = lean_box(0);
                        v_isShared_8095_ = v_isSharedCheck_8099_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_8081_) == 0 {
                    lean_del_object(v___x_8065_);
                    v___x_8085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8085_, 0, v_a_8081_);
                    v___x_8086_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8086_, 0, v___x_8085_);
                    lean_ctor_set(v___x_8086_, 1, v_snd_8063_);
                    if v_isShared_8084_ == 0 {
                        lean_ctor_set(v___x_8083_, 0, v___x_8086_);
                        v___x_8088_ = v___x_8083_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_8089_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8089_, 0, v___x_8086_);
                        v___x_8088_ = v_reuseFailAlloc_8089_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8083_);
                    lean_dec(v_snd_8063_);
                    v_a_8090_ = lean_ctor_get(v_a_8081_, 0);
                    lean_inc(v_a_8090_);
                    lean_dec_ref_known(v_a_8081_, 1);
                    v_a_8069_ = v_a_8090_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                return v___x_8088_;
            }
            8 => {
                if v_isShared_8095_ == 0 {
                    v___x_8097_ = v___x_8094_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8098_, 0, v_a_8092_);
                    v___x_8097_ = v_reuseFailAlloc_8098_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8097_;
            }
            10 => {
                v___x_8101_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
                v___x_8102_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                    v___x_8101_,
                    v___y_8050_,
                    v___y_8051_,
                    v___y_8052_,
                    v___y_8053_,
                    v___y_8054_,
                    v___y_8055_,
                    v___y_8056_,
                    v___y_8057_,
                    v___y_8058_,
                    v___y_8059_,
                );
                v___y_8080_ = v___x_8102_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___boxed(
    mut v_a_8121_: *mut LeanObject,
    mut v_as_8122_: *mut LeanObject,
    mut v_sz_8123_: *mut LeanObject,
    mut v_i_8124_: *mut LeanObject,
    mut v_b_8125_: *mut LeanObject,
    mut v___y_8126_: *mut LeanObject,
    mut v___y_8127_: *mut LeanObject,
    mut v___y_8128_: *mut LeanObject,
    mut v___y_8129_: *mut LeanObject,
    mut v___y_8130_: *mut LeanObject,
    mut v___y_8131_: *mut LeanObject,
    mut v___y_8132_: *mut LeanObject,
    mut v___y_8133_: *mut LeanObject,
    mut v___y_8134_: *mut LeanObject,
    mut v___y_8135_: *mut LeanObject,
    mut v___y_8136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8137_: usize = 0;
    let mut v_i_boxed_8138_: usize = 0;
    let mut v_res_8139_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8137_ = lean_unbox_usize(v_sz_8123_);
    lean_dec(v_sz_8123_);
    v_i_boxed_8138_ = lean_unbox_usize(v_i_8124_);
    lean_dec(v_i_8124_);
    v_res_8139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_8121_, v_as_8122_, v_sz_boxed_8137_, v_i_boxed_8138_, v_b_8125_, v___y_8126_, v___y_8127_, v___y_8128_, v___y_8129_, v___y_8130_, v___y_8131_, v___y_8132_, v___y_8133_, v___y_8134_, v___y_8135_);
    lean_dec(v___y_8135_);
    lean_dec_ref(v___y_8134_);
    lean_dec(v___y_8133_);
    lean_dec_ref(v___y_8132_);
    lean_dec(v___y_8131_);
    lean_dec_ref(v___y_8130_);
    lean_dec(v___y_8129_);
    lean_dec_ref(v___y_8128_);
    lean_dec(v___y_8127_);
    lean_dec(v___y_8126_);
    lean_dec_ref(v_as_8122_);
    lean_dec_ref(v_a_8121_);
    return v_res_8139_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(
    mut v_a_8140_: *mut LeanObject,
    mut v_as_8141_: *mut LeanObject,
    mut v_sz_8142_: usize,
    mut v_i_8143_: usize,
    mut v_b_8144_: *mut LeanObject,
    mut v___y_8145_: *mut LeanObject,
    mut v___y_8146_: *mut LeanObject,
    mut v___y_8147_: *mut LeanObject,
    mut v___y_8148_: *mut LeanObject,
    mut v___y_8149_: *mut LeanObject,
    mut v___y_8150_: *mut LeanObject,
    mut v___y_8151_: *mut LeanObject,
    mut v___y_8152_: *mut LeanObject,
    mut v___y_8153_: *mut LeanObject,
    mut v___y_8154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8156_: u8 = 0;
    let mut v___x_8157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8161_: u8 = 0;
    let mut v___x_8162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8167_: usize = 0;
    let mut v___x_8168_: usize = 0;
    let mut v___x_8169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8179_: u8 = 0;
    let mut v___x_8180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8186_: u8 = 0;
    let mut v_a_8187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8190_: u8 = 0;
    let mut v___x_8192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8194_: u8 = 0;
    let mut v___x_8196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_8200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8201_: u8 = 0;
    let mut v___x_8202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8204_: u8 = 0;
    let mut v___x_8205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_8207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8208_: u8 = 0;
    let mut v___x_8209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8213_: u8 = 0;
    let mut v_isSharedCheck_8214_: u8 = 0;
    let mut v_unused_8215_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8156_ = lean_usize_dec_lt(v_i_8143_, v_sz_8142_);
                if v___x_8156_ == 0 {
                    v___x_8157_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8157_, 0, v_b_8144_);
                    return v___x_8157_;
                } else {
                    v_snd_8158_ = lean_ctor_get(v_b_8144_, 1);
                    v_isSharedCheck_8214_ = (!lean_is_exclusive(v_b_8144_)) as u8;
                    if v_isSharedCheck_8214_ == 0 {
                        v_unused_8215_ = lean_ctor_get(v_b_8144_, 0);
                        lean_dec(v_unused_8215_);
                        v___x_8160_ = v_b_8144_;
                        v_isShared_8161_ = v_isSharedCheck_8214_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_8158_);
                        lean_dec(v_b_8144_);
                        v___x_8160_ = lean_box(0);
                        v_isShared_8161_ = v_isSharedCheck_8214_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8162_ = lean_box(0);
                v_a_8198_ = lean_array_uget_borrowed(v_as_8141_, v_i_8143_);
                if lean_obj_tag(v_a_8198_) == 1 {
                    v_val_8199_ = lean_ctor_get(v_a_8198_, 0);
                    v_p_8200_ = lean_ctor_get(v_val_8199_, 0);
                    v___x_8201_ = l_Int_Linear_Poly_isSorted(v_p_8200_);
                    if v___x_8201_ == 0 {
                        v___x_8202_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
                        v___x_8203_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_8202_,
                                v___y_8145_,
                                v___y_8146_,
                                v___y_8147_,
                                v___y_8148_,
                                v___y_8149_,
                                v___y_8150_,
                                v___y_8151_,
                                v___y_8152_,
                                v___y_8153_,
                                v___y_8154_,
                            );
                        v___y_8175_ = v___x_8203_;
                        state = 5;
                        continue;
                    } else {
                        v___x_8204_ = l_Int_Linear_Poly_checkCoeffs(v_p_8200_);
                        if v___x_8204_ == 0 {
                            v___x_8205_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
                            v___x_8206_ =
                                l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                    v___x_8205_,
                                    v___y_8145_,
                                    v___y_8146_,
                                    v___y_8147_,
                                    v___y_8148_,
                                    v___y_8149_,
                                    v___y_8150_,
                                    v___y_8151_,
                                    v___y_8152_,
                                    v___y_8153_,
                                    v___y_8154_,
                                );
                            v___y_8175_ = v___x_8206_;
                            state = 5;
                            continue;
                        } else {
                            v_elimStack_8207_ = lean_ctor_get(v_a_8140_, 11);
                            v___x_8208_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_8158_, v_elimStack_8207_);
                            if v___x_8208_ == 0 {
                                v___x_8209_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
                                v___x_8210_ =
                                    l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                        v___x_8209_,
                                        v___y_8145_,
                                        v___y_8146_,
                                        v___y_8147_,
                                        v___y_8148_,
                                        v___y_8149_,
                                        v___y_8150_,
                                        v___y_8151_,
                                        v___y_8152_,
                                        v___y_8153_,
                                        v___y_8154_,
                                    );
                                v___y_8175_ = v___x_8210_;
                                state = 5;
                                continue;
                            } else {
                                v___x_8211_ = l_Int_Linear_Poly_coeff(v_p_8200_, v_snd_8158_);
                                v___x_8212_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Int_Linear_Poly_checkCoeffs___closed__0
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Int_Linear_Poly_checkCoeffs___closed__0_once
                                    ),
                                    _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                                );
                                v___x_8213_ = lean_int_dec_eq(v___x_8211_, v___x_8212_);
                                lean_dec(v___x_8211_);
                                if v___x_8213_ == 0 {
                                    if v___x_8208_ == 0 {
                                        state = 10;
                                        continue;
                                    } else {
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_8161_ == 0 {
                    lean_ctor_set(v___x_8160_, 1, v_a_8164_);
                    lean_ctor_set(v___x_8160_, 0, v___x_8162_);
                    v___x_8166_ = v___x_8160_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8170_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8170_, 0, v___x_8162_);
                    lean_ctor_set(v_reuseFailAlloc_8170_, 1, v_a_8164_);
                    v___x_8166_ = v_reuseFailAlloc_8170_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8167_ = 1usize;
                v___x_8168_ = lean_usize_add(v_i_8143_, v___x_8167_);
                v___x_8169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4(v_a_8140_, v_as_8141_, v_sz_8142_, v___x_8168_, v___x_8166_, v___y_8145_, v___y_8146_, v___y_8147_, v___y_8148_, v___y_8149_, v___y_8150_, v___y_8151_, v___y_8152_, v___y_8153_, v___y_8154_);
                return v___x_8169_;
            }
            4 => {
                v___x_8172_ = lean_unsigned_to_nat(1);
                v___x_8173_ = lean_nat_add(v_snd_8158_, v___x_8172_);
                lean_dec(v_snd_8158_);
                v_a_8164_ = v___x_8173_;
                state = 2;
                continue;
            }
            5 => {
                if lean_obj_tag(v___y_8175_) == 0 {
                    v_a_8176_ = lean_ctor_get(v___y_8175_, 0);
                    v_isSharedCheck_8186_ = (!lean_is_exclusive(v___y_8175_)) as u8;
                    if v_isSharedCheck_8186_ == 0 {
                        v___x_8178_ = v___y_8175_;
                        v_isShared_8179_ = v_isSharedCheck_8186_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8176_);
                        lean_dec(v___y_8175_);
                        v___x_8178_ = lean_box(0);
                        v_isShared_8179_ = v_isSharedCheck_8186_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8160_);
                    lean_dec(v_snd_8158_);
                    v_a_8187_ = lean_ctor_get(v___y_8175_, 0);
                    v_isSharedCheck_8194_ = (!lean_is_exclusive(v___y_8175_)) as u8;
                    if v_isSharedCheck_8194_ == 0 {
                        v___x_8189_ = v___y_8175_;
                        v_isShared_8190_ = v_isSharedCheck_8194_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_8187_);
                        lean_dec(v___y_8175_);
                        v___x_8189_ = lean_box(0);
                        v_isShared_8190_ = v_isSharedCheck_8194_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_8176_) == 0 {
                    lean_del_object(v___x_8160_);
                    v___x_8180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8180_, 0, v_a_8176_);
                    v___x_8181_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8181_, 0, v___x_8180_);
                    lean_ctor_set(v___x_8181_, 1, v_snd_8158_);
                    if v_isShared_8179_ == 0 {
                        lean_ctor_set(v___x_8178_, 0, v___x_8181_);
                        v___x_8183_ = v___x_8178_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_8184_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8184_, 0, v___x_8181_);
                        v___x_8183_ = v_reuseFailAlloc_8184_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8178_);
                    lean_dec(v_snd_8158_);
                    v_a_8185_ = lean_ctor_get(v_a_8176_, 0);
                    lean_inc(v_a_8185_);
                    lean_dec_ref_known(v_a_8176_, 1);
                    v_a_8164_ = v_a_8185_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                return v___x_8183_;
            }
            8 => {
                if v_isShared_8190_ == 0 {
                    v___x_8192_ = v___x_8189_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8193_, 0, v_a_8187_);
                    v___x_8192_ = v_reuseFailAlloc_8193_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8192_;
            }
            10 => {
                v___x_8196_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
                v___x_8197_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                    v___x_8196_,
                    v___y_8145_,
                    v___y_8146_,
                    v___y_8147_,
                    v___y_8148_,
                    v___y_8149_,
                    v___y_8150_,
                    v___y_8151_,
                    v___y_8152_,
                    v___y_8153_,
                    v___y_8154_,
                );
                v___y_8175_ = v___x_8197_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3___boxed(
    mut v_a_8216_: *mut LeanObject,
    mut v_as_8217_: *mut LeanObject,
    mut v_sz_8218_: *mut LeanObject,
    mut v_i_8219_: *mut LeanObject,
    mut v_b_8220_: *mut LeanObject,
    mut v___y_8221_: *mut LeanObject,
    mut v___y_8222_: *mut LeanObject,
    mut v___y_8223_: *mut LeanObject,
    mut v___y_8224_: *mut LeanObject,
    mut v___y_8225_: *mut LeanObject,
    mut v___y_8226_: *mut LeanObject,
    mut v___y_8227_: *mut LeanObject,
    mut v___y_8228_: *mut LeanObject,
    mut v___y_8229_: *mut LeanObject,
    mut v___y_8230_: *mut LeanObject,
    mut v___y_8231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8232_: usize = 0;
    let mut v_i_boxed_8233_: usize = 0;
    let mut v_res_8234_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8232_ = lean_unbox_usize(v_sz_8218_);
    lean_dec(v_sz_8218_);
    v_i_boxed_8233_ = lean_unbox_usize(v_i_8219_);
    lean_dec(v_i_8219_);
    v_res_8234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_8216_, v_as_8217_, v_sz_boxed_8232_, v_i_boxed_8233_, v_b_8220_, v___y_8221_, v___y_8222_, v___y_8223_, v___y_8224_, v___y_8225_, v___y_8226_, v___y_8227_, v___y_8228_, v___y_8229_, v___y_8230_);
    lean_dec(v___y_8230_);
    lean_dec_ref(v___y_8229_);
    lean_dec(v___y_8228_);
    lean_dec_ref(v___y_8227_);
    lean_dec(v___y_8226_);
    lean_dec_ref(v___y_8225_);
    lean_dec(v___y_8224_);
    lean_dec_ref(v___y_8223_);
    lean_dec(v___y_8222_);
    lean_dec(v___y_8221_);
    lean_dec_ref(v_as_8217_);
    lean_dec_ref(v_a_8216_);
    return v_res_8234_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(
    mut v_init_8235_: *mut LeanObject,
    mut v_a_8236_: *mut LeanObject,
    mut v_n_8237_: *mut LeanObject,
    mut v_b_8238_: *mut LeanObject,
    mut v___y_8239_: *mut LeanObject,
    mut v___y_8240_: *mut LeanObject,
    mut v___y_8241_: *mut LeanObject,
    mut v___y_8242_: *mut LeanObject,
    mut v___y_8243_: *mut LeanObject,
    mut v___y_8244_: *mut LeanObject,
    mut v___y_8245_: *mut LeanObject,
    mut v___y_8246_: *mut LeanObject,
    mut v___y_8247_: *mut LeanObject,
    mut v___y_8248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8253_: usize = 0;
    let mut v___x_8254_: usize = 0;
    let mut v___x_8255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8259_: u8 = 0;
    let mut v_fst_8260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8270_: u8 = 0;
    let mut v_a_8271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8274_: u8 = 0;
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8278_: u8 = 0;
    let mut v_vs_8279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8282_: usize = 0;
    let mut v___x_8283_: usize = 0;
    let mut v___x_8284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8288_: u8 = 0;
    let mut v_fst_8289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8299_: u8 = 0;
    let mut v_a_8300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8303_: u8 = 0;
    let mut v___x_8305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_8237_) == 0 {
                    v_cs_8250_ = lean_ctor_get(v_n_8237_, 0);
                    v___x_8251_ = lean_box(0);
                    v___x_8252_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8252_, 0, v___x_8251_);
                    lean_ctor_set(v___x_8252_, 1, v_b_8238_);
                    v_sz_8253_ = lean_array_size(v_cs_8250_);
                    v___x_8254_ = 0usize;
                    v___x_8255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_8235_, v_a_8236_, v_cs_8250_, v_sz_8253_, v___x_8254_, v___x_8252_, v___y_8239_, v___y_8240_, v___y_8241_, v___y_8242_, v___y_8243_, v___y_8244_, v___y_8245_, v___y_8246_, v___y_8247_, v___y_8248_);
                    if lean_obj_tag(v___x_8255_) == 0 {
                        v_a_8256_ = lean_ctor_get(v___x_8255_, 0);
                        v_isSharedCheck_8270_ = (!lean_is_exclusive(v___x_8255_)) as u8;
                        if v_isSharedCheck_8270_ == 0 {
                            v___x_8258_ = v___x_8255_;
                            v_isShared_8259_ = v_isSharedCheck_8270_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8256_);
                            lean_dec(v___x_8255_);
                            v___x_8258_ = lean_box(0);
                            v_isShared_8259_ = v_isSharedCheck_8270_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_8271_ = lean_ctor_get(v___x_8255_, 0);
                        v_isSharedCheck_8278_ = (!lean_is_exclusive(v___x_8255_)) as u8;
                        if v_isSharedCheck_8278_ == 0 {
                            v___x_8273_ = v___x_8255_;
                            v_isShared_8274_ = v_isSharedCheck_8278_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_8271_);
                            lean_dec(v___x_8255_);
                            v___x_8273_ = lean_box(0);
                            v_isShared_8274_ = v_isSharedCheck_8278_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_8279_ = lean_ctor_get(v_n_8237_, 0);
                    v___x_8280_ = lean_box(0);
                    v___x_8281_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8281_, 0, v___x_8280_);
                    lean_ctor_set(v___x_8281_, 1, v_b_8238_);
                    v_sz_8282_ = lean_array_size(v_vs_8279_);
                    v___x_8283_ = 0usize;
                    v___x_8284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3(v_a_8236_, v_vs_8279_, v_sz_8282_, v___x_8283_, v___x_8281_, v___y_8239_, v___y_8240_, v___y_8241_, v___y_8242_, v___y_8243_, v___y_8244_, v___y_8245_, v___y_8246_, v___y_8247_, v___y_8248_);
                    if lean_obj_tag(v___x_8284_) == 0 {
                        v_a_8285_ = lean_ctor_get(v___x_8284_, 0);
                        v_isSharedCheck_8299_ = (!lean_is_exclusive(v___x_8284_)) as u8;
                        if v_isSharedCheck_8299_ == 0 {
                            v___x_8287_ = v___x_8284_;
                            v_isShared_8288_ = v_isSharedCheck_8299_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_8285_);
                            lean_dec(v___x_8284_);
                            v___x_8287_ = lean_box(0);
                            v_isShared_8288_ = v_isSharedCheck_8299_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_8300_ = lean_ctor_get(v___x_8284_, 0);
                        v_isSharedCheck_8307_ = (!lean_is_exclusive(v___x_8284_)) as u8;
                        if v_isSharedCheck_8307_ == 0 {
                            v___x_8302_ = v___x_8284_;
                            v_isShared_8303_ = v_isSharedCheck_8307_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_8300_);
                            lean_dec(v___x_8284_);
                            v___x_8302_ = lean_box(0);
                            v_isShared_8303_ = v_isSharedCheck_8307_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_8260_ = lean_ctor_get(v_a_8256_, 0);
                if lean_obj_tag(v_fst_8260_) == 0 {
                    v_snd_8261_ = lean_ctor_get(v_a_8256_, 1);
                    lean_inc(v_snd_8261_);
                    lean_dec(v_a_8256_);
                    v___x_8262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8262_, 0, v_snd_8261_);
                    if v_isShared_8259_ == 0 {
                        lean_ctor_set(v___x_8258_, 0, v___x_8262_);
                        v___x_8264_ = v___x_8258_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8265_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8265_, 0, v___x_8262_);
                        v___x_8264_ = v_reuseFailAlloc_8265_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_8260_);
                    lean_dec(v_a_8256_);
                    v_val_8266_ = lean_ctor_get(v_fst_8260_, 0);
                    lean_inc(v_val_8266_);
                    lean_dec_ref_known(v_fst_8260_, 1);
                    if v_isShared_8259_ == 0 {
                        lean_ctor_set(v___x_8258_, 0, v_val_8266_);
                        v___x_8268_ = v___x_8258_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8269_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8269_, 0, v_val_8266_);
                        v___x_8268_ = v_reuseFailAlloc_8269_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8264_;
            }
            3 => {
                return v___x_8268_;
            }
            4 => {
                if v_isShared_8274_ == 0 {
                    v___x_8276_ = v___x_8273_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8277_, 0, v_a_8271_);
                    v___x_8276_ = v_reuseFailAlloc_8277_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8276_;
            }
            6 => {
                v_fst_8289_ = lean_ctor_get(v_a_8285_, 0);
                if lean_obj_tag(v_fst_8289_) == 0 {
                    v_snd_8290_ = lean_ctor_get(v_a_8285_, 1);
                    lean_inc(v_snd_8290_);
                    lean_dec(v_a_8285_);
                    v___x_8291_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8291_, 0, v_snd_8290_);
                    if v_isShared_8288_ == 0 {
                        lean_ctor_set(v___x_8287_, 0, v___x_8291_);
                        v___x_8293_ = v___x_8287_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_8294_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8294_, 0, v___x_8291_);
                        v___x_8293_ = v_reuseFailAlloc_8294_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_8289_);
                    lean_dec(v_a_8285_);
                    v_val_8295_ = lean_ctor_get(v_fst_8289_, 0);
                    lean_inc(v_val_8295_);
                    lean_dec_ref_known(v_fst_8289_, 1);
                    if v_isShared_8288_ == 0 {
                        lean_ctor_set(v___x_8287_, 0, v_val_8295_);
                        v___x_8297_ = v___x_8287_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_8298_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8298_, 0, v_val_8295_);
                        v___x_8297_ = v_reuseFailAlloc_8298_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_8293_;
            }
            8 => {
                return v___x_8297_;
            }
            9 => {
                if v_isShared_8303_ == 0 {
                    v___x_8305_ = v___x_8302_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8306_, 0, v_a_8300_);
                    v___x_8305_ = v_reuseFailAlloc_8306_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(
    mut v_init_8308_: *mut LeanObject,
    mut v_a_8309_: *mut LeanObject,
    mut v_as_8310_: *mut LeanObject,
    mut v_sz_8311_: usize,
    mut v_i_8312_: usize,
    mut v_b_8313_: *mut LeanObject,
    mut v___y_8314_: *mut LeanObject,
    mut v___y_8315_: *mut LeanObject,
    mut v___y_8316_: *mut LeanObject,
    mut v___y_8317_: *mut LeanObject,
    mut v___y_8318_: *mut LeanObject,
    mut v___y_8319_: *mut LeanObject,
    mut v___y_8320_: *mut LeanObject,
    mut v___y_8321_: *mut LeanObject,
    mut v___y_8322_: *mut LeanObject,
    mut v___y_8323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8325_: u8 = 0;
    let mut v___x_8326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8330_: u8 = 0;
    let mut v_a_8331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8336_: u8 = 0;
    let mut v___x_8337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8348_: usize = 0;
    let mut v___x_8349_: usize = 0;
    let mut v_reuseFailAlloc_8351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8352_: u8 = 0;
    let mut v_a_8353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8356_: u8 = 0;
    let mut v___x_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8360_: u8 = 0;
    let mut v_isSharedCheck_8361_: u8 = 0;
    let mut v_unused_8362_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8325_ = lean_usize_dec_lt(v_i_8312_, v_sz_8311_);
                if v___x_8325_ == 0 {
                    v___x_8326_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8326_, 0, v_b_8313_);
                    return v___x_8326_;
                } else {
                    v_snd_8327_ = lean_ctor_get(v_b_8313_, 1);
                    v_isSharedCheck_8361_ = (!lean_is_exclusive(v_b_8313_)) as u8;
                    if v_isSharedCheck_8361_ == 0 {
                        v_unused_8362_ = lean_ctor_get(v_b_8313_, 0);
                        lean_dec(v_unused_8362_);
                        v___x_8329_ = v_b_8313_;
                        v_isShared_8330_ = v_isSharedCheck_8361_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_8327_);
                        lean_dec(v_b_8313_);
                        v___x_8329_ = lean_box(0);
                        v_isShared_8330_ = v_isSharedCheck_8361_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_8331_ = lean_array_uget_borrowed(v_as_8310_, v_i_8312_);
                lean_inc(v_snd_8327_);
                v___x_8332_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_8308_, v_a_8309_, v_a_8331_, v_snd_8327_, v___y_8314_, v___y_8315_, v___y_8316_, v___y_8317_, v___y_8318_, v___y_8319_, v___y_8320_, v___y_8321_, v___y_8322_, v___y_8323_);
                if lean_obj_tag(v___x_8332_) == 0 {
                    v_a_8333_ = lean_ctor_get(v___x_8332_, 0);
                    v_isSharedCheck_8352_ = (!lean_is_exclusive(v___x_8332_)) as u8;
                    if v_isSharedCheck_8352_ == 0 {
                        v___x_8335_ = v___x_8332_;
                        v_isShared_8336_ = v_isSharedCheck_8352_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8333_);
                        lean_dec(v___x_8332_);
                        v___x_8335_ = lean_box(0);
                        v_isShared_8336_ = v_isSharedCheck_8352_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8329_);
                    lean_dec(v_snd_8327_);
                    v_a_8353_ = lean_ctor_get(v___x_8332_, 0);
                    v_isSharedCheck_8360_ = (!lean_is_exclusive(v___x_8332_)) as u8;
                    if v_isSharedCheck_8360_ == 0 {
                        v___x_8355_ = v___x_8332_;
                        v_isShared_8356_ = v_isSharedCheck_8360_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8353_);
                        lean_dec(v___x_8332_);
                        v___x_8355_ = lean_box(0);
                        v_isShared_8356_ = v_isSharedCheck_8360_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_8333_) == 0 {
                    v___x_8337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8337_, 0, v_a_8333_);
                    if v_isShared_8330_ == 0 {
                        lean_ctor_set(v___x_8329_, 0, v___x_8337_);
                        v___x_8339_ = v___x_8329_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8343_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8343_, 0, v___x_8337_);
                        lean_ctor_set(v_reuseFailAlloc_8343_, 1, v_snd_8327_);
                        v___x_8339_ = v_reuseFailAlloc_8343_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8335_);
                    lean_dec(v_snd_8327_);
                    v_a_8344_ = lean_ctor_get(v_a_8333_, 0);
                    lean_inc(v_a_8344_);
                    lean_dec_ref_known(v_a_8333_, 1);
                    v___x_8345_ = lean_box(0);
                    if v_isShared_8330_ == 0 {
                        lean_ctor_set(v___x_8329_, 1, v_a_8344_);
                        lean_ctor_set(v___x_8329_, 0, v___x_8345_);
                        v___x_8347_ = v___x_8329_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8351_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8351_, 0, v___x_8345_);
                        lean_ctor_set(v_reuseFailAlloc_8351_, 1, v_a_8344_);
                        v___x_8347_ = v_reuseFailAlloc_8351_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8336_ == 0 {
                    lean_ctor_set(v___x_8335_, 0, v___x_8339_);
                    v___x_8341_ = v___x_8335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8342_, 0, v___x_8339_);
                    v___x_8341_ = v_reuseFailAlloc_8342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8341_;
            }
            5 => {
                v___x_8348_ = 1usize;
                v___x_8349_ = lean_usize_add(v_i_8312_, v___x_8348_);
                v_i_8312_ = v___x_8349_;
                v_b_8313_ = v___x_8347_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_8356_ == 0 {
                    v___x_8358_ = v___x_8355_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8359_, 0, v_a_8353_);
                    v___x_8358_ = v_reuseFailAlloc_8359_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_8363_: *mut LeanObject = *_args.add(0);
    let mut v_a_8364_: *mut LeanObject = *_args.add(1);
    let mut v_as_8365_: *mut LeanObject = *_args.add(2);
    let mut v_sz_8366_: *mut LeanObject = *_args.add(3);
    let mut v_i_8367_: *mut LeanObject = *_args.add(4);
    let mut v_b_8368_: *mut LeanObject = *_args.add(5);
    let mut v___y_8369_: *mut LeanObject = *_args.add(6);
    let mut v___y_8370_: *mut LeanObject = *_args.add(7);
    let mut v___y_8371_: *mut LeanObject = *_args.add(8);
    let mut v___y_8372_: *mut LeanObject = *_args.add(9);
    let mut v___y_8373_: *mut LeanObject = *_args.add(10);
    let mut v___y_8374_: *mut LeanObject = *_args.add(11);
    let mut v___y_8375_: *mut LeanObject = *_args.add(12);
    let mut v___y_8376_: *mut LeanObject = *_args.add(13);
    let mut v___y_8377_: *mut LeanObject = *_args.add(14);
    let mut v___y_8378_: *mut LeanObject = *_args.add(15);
    let mut v___y_8379_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_8380_: usize = 0;
    let mut v_i_boxed_8381_: usize = 0;
    let mut v_res_8382_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8380_ = lean_unbox_usize(v_sz_8366_);
    lean_dec(v_sz_8366_);
    v_i_boxed_8381_ = lean_unbox_usize(v_i_8367_);
    lean_dec(v_i_8367_);
    v_res_8382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__2(v_init_8363_, v_a_8364_, v_as_8365_, v_sz_boxed_8380_, v_i_boxed_8381_, v_b_8368_, v___y_8369_, v___y_8370_, v___y_8371_, v___y_8372_, v___y_8373_, v___y_8374_, v___y_8375_, v___y_8376_, v___y_8377_, v___y_8378_);
    lean_dec(v___y_8378_);
    lean_dec_ref(v___y_8377_);
    lean_dec(v___y_8376_);
    lean_dec_ref(v___y_8375_);
    lean_dec(v___y_8374_);
    lean_dec_ref(v___y_8373_);
    lean_dec(v___y_8372_);
    lean_dec_ref(v___y_8371_);
    lean_dec(v___y_8370_);
    lean_dec(v___y_8369_);
    lean_dec_ref(v_as_8365_);
    lean_dec_ref(v_a_8364_);
    lean_dec(v_init_8363_);
    return v_res_8382_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1___boxed(
    mut v_init_8383_: *mut LeanObject,
    mut v_a_8384_: *mut LeanObject,
    mut v_n_8385_: *mut LeanObject,
    mut v_b_8386_: *mut LeanObject,
    mut v___y_8387_: *mut LeanObject,
    mut v___y_8388_: *mut LeanObject,
    mut v___y_8389_: *mut LeanObject,
    mut v___y_8390_: *mut LeanObject,
    mut v___y_8391_: *mut LeanObject,
    mut v___y_8392_: *mut LeanObject,
    mut v___y_8393_: *mut LeanObject,
    mut v___y_8394_: *mut LeanObject,
    mut v___y_8395_: *mut LeanObject,
    mut v___y_8396_: *mut LeanObject,
    mut v___y_8397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8398_: *mut LeanObject = core::ptr::null_mut();
    v_res_8398_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_8383_, v_a_8384_, v_n_8385_, v_b_8386_, v___y_8387_, v___y_8388_, v___y_8389_, v___y_8390_, v___y_8391_, v___y_8392_, v___y_8393_, v___y_8394_, v___y_8395_, v___y_8396_);
    lean_dec(v___y_8396_);
    lean_dec_ref(v___y_8395_);
    lean_dec(v___y_8394_);
    lean_dec_ref(v___y_8393_);
    lean_dec(v___y_8392_);
    lean_dec_ref(v___y_8391_);
    lean_dec(v___y_8390_);
    lean_dec_ref(v___y_8389_);
    lean_dec(v___y_8388_);
    lean_dec(v___y_8387_);
    lean_dec_ref(v_n_8385_);
    lean_dec_ref(v_a_8384_);
    lean_dec(v_init_8383_);
    return v_res_8398_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(
    mut v_a_8399_: *mut LeanObject,
    mut v_as_8400_: *mut LeanObject,
    mut v_sz_8401_: usize,
    mut v_i_8402_: usize,
    mut v_b_8403_: *mut LeanObject,
    mut v___y_8404_: *mut LeanObject,
    mut v___y_8405_: *mut LeanObject,
    mut v___y_8406_: *mut LeanObject,
    mut v___y_8407_: *mut LeanObject,
    mut v___y_8408_: *mut LeanObject,
    mut v___y_8409_: *mut LeanObject,
    mut v___y_8410_: *mut LeanObject,
    mut v___y_8411_: *mut LeanObject,
    mut v___y_8412_: *mut LeanObject,
    mut v___y_8413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8415_: u8 = 0;
    let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8420_: u8 = 0;
    let mut v___x_8421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8426_: usize = 0;
    let mut v___x_8427_: usize = 0;
    let mut v_reuseFailAlloc_8429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8438_: u8 = 0;
    let mut v_a_8439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8442_: u8 = 0;
    let mut v___x_8444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8450_: u8 = 0;
    let mut v_a_8451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8452_: u8 = 0;
    let mut v_a_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8456_: u8 = 0;
    let mut v___x_8458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8460_: u8 = 0;
    let mut v___x_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_8466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8467_: u8 = 0;
    let mut v___x_8468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8470_: u8 = 0;
    let mut v___x_8471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: u8 = 0;
    let mut v___x_8475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8479_: u8 = 0;
    let mut v_isSharedCheck_8480_: u8 = 0;
    let mut v_unused_8481_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8415_ = lean_usize_dec_lt(v_i_8402_, v_sz_8401_);
                if v___x_8415_ == 0 {
                    v___x_8416_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8416_, 0, v_b_8403_);
                    return v___x_8416_;
                } else {
                    v_snd_8417_ = lean_ctor_get(v_b_8403_, 1);
                    v_isSharedCheck_8480_ = (!lean_is_exclusive(v_b_8403_)) as u8;
                    if v_isSharedCheck_8480_ == 0 {
                        v_unused_8481_ = lean_ctor_get(v_b_8403_, 0);
                        lean_dec(v_unused_8481_);
                        v___x_8419_ = v_b_8403_;
                        v_isShared_8420_ = v_isSharedCheck_8480_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_8417_);
                        lean_dec(v_b_8403_);
                        v___x_8419_ = lean_box(0);
                        v_isShared_8420_ = v_isSharedCheck_8480_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8421_ = lean_box(0);
                v_a_8464_ = lean_array_uget_borrowed(v_as_8400_, v_i_8402_);
                if lean_obj_tag(v_a_8464_) == 1 {
                    v_val_8465_ = lean_ctor_get(v_a_8464_, 0);
                    v_p_8466_ = lean_ctor_get(v_val_8465_, 0);
                    v___x_8467_ = l_Int_Linear_Poly_isSorted(v_p_8466_);
                    if v___x_8467_ == 0 {
                        v___x_8468_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
                        v___x_8469_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_8468_,
                                v___y_8404_,
                                v___y_8405_,
                                v___y_8406_,
                                v___y_8407_,
                                v___y_8408_,
                                v___y_8409_,
                                v___y_8410_,
                                v___y_8411_,
                                v___y_8412_,
                                v___y_8413_,
                            );
                        v___y_8434_ = v___x_8469_;
                        state = 5;
                        continue;
                    } else {
                        v___x_8470_ = l_Int_Linear_Poly_checkCoeffs(v_p_8466_);
                        if v___x_8470_ == 0 {
                            v___x_8471_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
                            v___x_8472_ =
                                l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                    v___x_8471_,
                                    v___y_8404_,
                                    v___y_8405_,
                                    v___y_8406_,
                                    v___y_8407_,
                                    v___y_8408_,
                                    v___y_8409_,
                                    v___y_8410_,
                                    v___y_8411_,
                                    v___y_8412_,
                                    v___y_8413_,
                                );
                            v___y_8434_ = v___x_8472_;
                            state = 5;
                            continue;
                        } else {
                            v_elimStack_8473_ = lean_ctor_get(v_a_8399_, 11);
                            v___x_8474_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_8417_, v_elimStack_8473_);
                            if v___x_8474_ == 0 {
                                v___x_8475_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
                                v___x_8476_ =
                                    l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                        v___x_8475_,
                                        v___y_8404_,
                                        v___y_8405_,
                                        v___y_8406_,
                                        v___y_8407_,
                                        v___y_8408_,
                                        v___y_8409_,
                                        v___y_8410_,
                                        v___y_8411_,
                                        v___y_8412_,
                                        v___y_8413_,
                                    );
                                v___y_8434_ = v___x_8476_;
                                state = 5;
                                continue;
                            } else {
                                v___x_8477_ = l_Int_Linear_Poly_coeff(v_p_8466_, v_snd_8417_);
                                v___x_8478_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Int_Linear_Poly_checkCoeffs___closed__0
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Int_Linear_Poly_checkCoeffs___closed__0_once
                                    ),
                                    _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                                );
                                v___x_8479_ = lean_int_dec_eq(v___x_8477_, v___x_8478_);
                                lean_dec(v___x_8477_);
                                if v___x_8479_ == 0 {
                                    if v___x_8474_ == 0 {
                                        state = 12;
                                        continue;
                                    } else {
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_8420_ == 0 {
                    lean_ctor_set(v___x_8419_, 1, v_a_8423_);
                    lean_ctor_set(v___x_8419_, 0, v___x_8421_);
                    v___x_8425_ = v___x_8419_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8429_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8429_, 0, v___x_8421_);
                    lean_ctor_set(v_reuseFailAlloc_8429_, 1, v_a_8423_);
                    v___x_8425_ = v_reuseFailAlloc_8429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8426_ = 1usize;
                v___x_8427_ = lean_usize_add(v_i_8402_, v___x_8426_);
                v_i_8402_ = v___x_8427_;
                v_b_8403_ = v___x_8425_;
                state = 0;
                continue;
            }
            4 => {
                v___x_8431_ = lean_unsigned_to_nat(1);
                v___x_8432_ = lean_nat_add(v_snd_8417_, v___x_8431_);
                lean_dec(v_snd_8417_);
                v_a_8423_ = v___x_8432_;
                state = 2;
                continue;
            }
            5 => {
                if lean_obj_tag(v___y_8434_) == 0 {
                    v_a_8435_ = lean_ctor_get(v___y_8434_, 0);
                    v_isSharedCheck_8452_ = (!lean_is_exclusive(v___y_8434_)) as u8;
                    if v_isSharedCheck_8452_ == 0 {
                        v___x_8437_ = v___y_8434_;
                        v_isShared_8438_ = v_isSharedCheck_8452_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8435_);
                        lean_dec(v___y_8434_);
                        v___x_8437_ = lean_box(0);
                        v_isShared_8438_ = v_isSharedCheck_8452_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8419_);
                    lean_dec(v_snd_8417_);
                    v_a_8453_ = lean_ctor_get(v___y_8434_, 0);
                    v_isSharedCheck_8460_ = (!lean_is_exclusive(v___y_8434_)) as u8;
                    if v_isSharedCheck_8460_ == 0 {
                        v___x_8455_ = v___y_8434_;
                        v_isShared_8456_ = v_isSharedCheck_8460_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_8453_);
                        lean_dec(v___y_8434_);
                        v___x_8455_ = lean_box(0);
                        v_isShared_8456_ = v_isSharedCheck_8460_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_8435_) == 0 {
                    lean_del_object(v___x_8419_);
                    v_a_8439_ = lean_ctor_get(v_a_8435_, 0);
                    v_isSharedCheck_8450_ = (!lean_is_exclusive(v_a_8435_)) as u8;
                    if v_isSharedCheck_8450_ == 0 {
                        v___x_8441_ = v_a_8435_;
                        v_isShared_8442_ = v_isSharedCheck_8450_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_8439_);
                        lean_dec(v_a_8435_);
                        v___x_8441_ = lean_box(0);
                        v_isShared_8442_ = v_isSharedCheck_8450_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8437_);
                    lean_dec(v_snd_8417_);
                    v_a_8451_ = lean_ctor_get(v_a_8435_, 0);
                    lean_inc(v_a_8451_);
                    lean_dec_ref_known(v_a_8435_, 1);
                    v_a_8423_ = v_a_8451_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                if v_isShared_8442_ == 0 {
                    lean_ctor_set_tag(v___x_8441_, 1);
                    v___x_8444_ = v___x_8441_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8449_, 0, v_a_8439_);
                    v___x_8444_ = v_reuseFailAlloc_8449_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_8445_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8445_, 0, v___x_8444_);
                lean_ctor_set(v___x_8445_, 1, v_snd_8417_);
                if v_isShared_8438_ == 0 {
                    lean_ctor_set(v___x_8437_, 0, v___x_8445_);
                    v___x_8447_ = v___x_8437_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8448_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8448_, 0, v___x_8445_);
                    v___x_8447_ = v_reuseFailAlloc_8448_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8447_;
            }
            10 => {
                if v_isShared_8456_ == 0 {
                    v___x_8458_ = v___x_8455_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8459_, 0, v_a_8453_);
                    v___x_8458_ = v_reuseFailAlloc_8459_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8458_;
            }
            12 => {
                v___x_8462_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
                v___x_8463_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                    v___x_8462_,
                    v___y_8404_,
                    v___y_8405_,
                    v___y_8406_,
                    v___y_8407_,
                    v___y_8408_,
                    v___y_8409_,
                    v___y_8410_,
                    v___y_8411_,
                    v___y_8412_,
                    v___y_8413_,
                );
                v___y_8434_ = v___x_8463_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5___boxed(
    mut v_a_8482_: *mut LeanObject,
    mut v_as_8483_: *mut LeanObject,
    mut v_sz_8484_: *mut LeanObject,
    mut v_i_8485_: *mut LeanObject,
    mut v_b_8486_: *mut LeanObject,
    mut v___y_8487_: *mut LeanObject,
    mut v___y_8488_: *mut LeanObject,
    mut v___y_8489_: *mut LeanObject,
    mut v___y_8490_: *mut LeanObject,
    mut v___y_8491_: *mut LeanObject,
    mut v___y_8492_: *mut LeanObject,
    mut v___y_8493_: *mut LeanObject,
    mut v___y_8494_: *mut LeanObject,
    mut v___y_8495_: *mut LeanObject,
    mut v___y_8496_: *mut LeanObject,
    mut v___y_8497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8498_: usize = 0;
    let mut v_i_boxed_8499_: usize = 0;
    let mut v_res_8500_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8498_ = lean_unbox_usize(v_sz_8484_);
    lean_dec(v_sz_8484_);
    v_i_boxed_8499_ = lean_unbox_usize(v_i_8485_);
    lean_dec(v_i_8485_);
    v_res_8500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_8482_, v_as_8483_, v_sz_boxed_8498_, v_i_boxed_8499_, v_b_8486_, v___y_8487_, v___y_8488_, v___y_8489_, v___y_8490_, v___y_8491_, v___y_8492_, v___y_8493_, v___y_8494_, v___y_8495_, v___y_8496_);
    lean_dec(v___y_8496_);
    lean_dec_ref(v___y_8495_);
    lean_dec(v___y_8494_);
    lean_dec_ref(v___y_8493_);
    lean_dec(v___y_8492_);
    lean_dec_ref(v___y_8491_);
    lean_dec(v___y_8490_);
    lean_dec_ref(v___y_8489_);
    lean_dec(v___y_8488_);
    lean_dec(v___y_8487_);
    lean_dec_ref(v_as_8483_);
    lean_dec_ref(v_a_8482_);
    return v_res_8500_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(
    mut v_a_8501_: *mut LeanObject,
    mut v_as_8502_: *mut LeanObject,
    mut v_sz_8503_: usize,
    mut v_i_8504_: usize,
    mut v_b_8505_: *mut LeanObject,
    mut v___y_8506_: *mut LeanObject,
    mut v___y_8507_: *mut LeanObject,
    mut v___y_8508_: *mut LeanObject,
    mut v___y_8509_: *mut LeanObject,
    mut v___y_8510_: *mut LeanObject,
    mut v___y_8511_: *mut LeanObject,
    mut v___y_8512_: *mut LeanObject,
    mut v___y_8513_: *mut LeanObject,
    mut v___y_8514_: *mut LeanObject,
    mut v___y_8515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8517_: u8 = 0;
    let mut v___x_8518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8522_: u8 = 0;
    let mut v___x_8523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8528_: usize = 0;
    let mut v___x_8529_: usize = 0;
    let mut v___x_8530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8540_: u8 = 0;
    let mut v_a_8541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8544_: u8 = 0;
    let mut v___x_8546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8552_: u8 = 0;
    let mut v_a_8553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8554_: u8 = 0;
    let mut v_a_8555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8558_: u8 = 0;
    let mut v___x_8560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8562_: u8 = 0;
    let mut v___x_8564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_8568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8569_: u8 = 0;
    let mut v___x_8570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8572_: u8 = 0;
    let mut v___x_8573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_8575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8576_: u8 = 0;
    let mut v___x_8577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8581_: u8 = 0;
    let mut v_isSharedCheck_8582_: u8 = 0;
    let mut v_unused_8583_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8517_ = lean_usize_dec_lt(v_i_8504_, v_sz_8503_);
                if v___x_8517_ == 0 {
                    v___x_8518_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8518_, 0, v_b_8505_);
                    return v___x_8518_;
                } else {
                    v_snd_8519_ = lean_ctor_get(v_b_8505_, 1);
                    v_isSharedCheck_8582_ = (!lean_is_exclusive(v_b_8505_)) as u8;
                    if v_isSharedCheck_8582_ == 0 {
                        v_unused_8583_ = lean_ctor_get(v_b_8505_, 0);
                        lean_dec(v_unused_8583_);
                        v___x_8521_ = v_b_8505_;
                        v_isShared_8522_ = v_isSharedCheck_8582_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_8519_);
                        lean_dec(v_b_8505_);
                        v___x_8521_ = lean_box(0);
                        v_isShared_8522_ = v_isSharedCheck_8582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8523_ = lean_box(0);
                v_a_8566_ = lean_array_uget_borrowed(v_as_8502_, v_i_8504_);
                if lean_obj_tag(v_a_8566_) == 1 {
                    v_val_8567_ = lean_ctor_get(v_a_8566_, 0);
                    v_p_8568_ = lean_ctor_get(v_val_8567_, 0);
                    v___x_8569_ = l_Int_Linear_Poly_isSorted(v_p_8568_);
                    if v___x_8569_ == 0 {
                        v___x_8570_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__4);
                        v___x_8571_ =
                            l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                v___x_8570_,
                                v___y_8506_,
                                v___y_8507_,
                                v___y_8508_,
                                v___y_8509_,
                                v___y_8510_,
                                v___y_8511_,
                                v___y_8512_,
                                v___y_8513_,
                                v___y_8514_,
                                v___y_8515_,
                            );
                        v___y_8536_ = v___x_8571_;
                        state = 5;
                        continue;
                    } else {
                        v___x_8572_ = l_Int_Linear_Poly_checkCoeffs(v_p_8568_);
                        if v___x_8572_ == 0 {
                            v___x_8573_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__6);
                            v___x_8574_ =
                                l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                    v___x_8573_,
                                    v___y_8506_,
                                    v___y_8507_,
                                    v___y_8508_,
                                    v___y_8509_,
                                    v___y_8510_,
                                    v___y_8511_,
                                    v___y_8512_,
                                    v___y_8513_,
                                    v___y_8514_,
                                    v___y_8515_,
                                );
                            v___y_8536_ = v___x_8574_;
                            state = 5;
                            continue;
                        } else {
                            v_elimStack_8575_ = lean_ctor_get(v_a_8501_, 11);
                            v___x_8576_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_snd_8519_, v_elimStack_8575_);
                            if v___x_8576_ == 0 {
                                v___x_8577_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__8);
                                v___x_8578_ =
                                    l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                                        v___x_8577_,
                                        v___y_8506_,
                                        v___y_8507_,
                                        v___y_8508_,
                                        v___y_8509_,
                                        v___y_8510_,
                                        v___y_8511_,
                                        v___y_8512_,
                                        v___y_8513_,
                                        v___y_8514_,
                                        v___y_8515_,
                                    );
                                v___y_8536_ = v___x_8578_;
                                state = 5;
                                continue;
                            } else {
                                v___x_8579_ = l_Int_Linear_Poly_coeff(v_p_8568_, v_snd_8519_);
                                v___x_8580_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Int_Linear_Poly_checkCoeffs___closed__0
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Int_Linear_Poly_checkCoeffs___closed__0_once
                                    ),
                                    _init_l_Int_Linear_Poly_checkCoeffs___closed__0,
                                );
                                v___x_8581_ = lean_int_dec_eq(v___x_8579_, v___x_8580_);
                                lean_dec(v___x_8579_);
                                if v___x_8581_ == 0 {
                                    if v___x_8576_ == 0 {
                                        state = 12;
                                        continue;
                                    } else {
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_8522_ == 0 {
                    lean_ctor_set(v___x_8521_, 1, v_a_8525_);
                    lean_ctor_set(v___x_8521_, 0, v___x_8523_);
                    v___x_8527_ = v___x_8521_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8531_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8531_, 0, v___x_8523_);
                    lean_ctor_set(v_reuseFailAlloc_8531_, 1, v_a_8525_);
                    v___x_8527_ = v_reuseFailAlloc_8531_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8528_ = 1usize;
                v___x_8529_ = lean_usize_add(v_i_8504_, v___x_8528_);
                v___x_8530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2_spec__5(v_a_8501_, v_as_8502_, v_sz_8503_, v___x_8529_, v___x_8527_, v___y_8506_, v___y_8507_, v___y_8508_, v___y_8509_, v___y_8510_, v___y_8511_, v___y_8512_, v___y_8513_, v___y_8514_, v___y_8515_);
                return v___x_8530_;
            }
            4 => {
                v___x_8533_ = lean_unsigned_to_nat(1);
                v___x_8534_ = lean_nat_add(v_snd_8519_, v___x_8533_);
                lean_dec(v_snd_8519_);
                v_a_8525_ = v___x_8534_;
                state = 2;
                continue;
            }
            5 => {
                if lean_obj_tag(v___y_8536_) == 0 {
                    v_a_8537_ = lean_ctor_get(v___y_8536_, 0);
                    v_isSharedCheck_8554_ = (!lean_is_exclusive(v___y_8536_)) as u8;
                    if v_isSharedCheck_8554_ == 0 {
                        v___x_8539_ = v___y_8536_;
                        v_isShared_8540_ = v_isSharedCheck_8554_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8537_);
                        lean_dec(v___y_8536_);
                        v___x_8539_ = lean_box(0);
                        v_isShared_8540_ = v_isSharedCheck_8554_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8521_);
                    lean_dec(v_snd_8519_);
                    v_a_8555_ = lean_ctor_get(v___y_8536_, 0);
                    v_isSharedCheck_8562_ = (!lean_is_exclusive(v___y_8536_)) as u8;
                    if v_isSharedCheck_8562_ == 0 {
                        v___x_8557_ = v___y_8536_;
                        v_isShared_8558_ = v_isSharedCheck_8562_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_8555_);
                        lean_dec(v___y_8536_);
                        v___x_8557_ = lean_box(0);
                        v_isShared_8558_ = v_isSharedCheck_8562_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_8537_) == 0 {
                    lean_del_object(v___x_8521_);
                    v_a_8541_ = lean_ctor_get(v_a_8537_, 0);
                    v_isSharedCheck_8552_ = (!lean_is_exclusive(v_a_8537_)) as u8;
                    if v_isSharedCheck_8552_ == 0 {
                        v___x_8543_ = v_a_8537_;
                        v_isShared_8544_ = v_isSharedCheck_8552_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_8541_);
                        lean_dec(v_a_8537_);
                        v___x_8543_ = lean_box(0);
                        v_isShared_8544_ = v_isSharedCheck_8552_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8539_);
                    lean_dec(v_snd_8519_);
                    v_a_8553_ = lean_ctor_get(v_a_8537_, 0);
                    lean_inc(v_a_8553_);
                    lean_dec_ref_known(v_a_8537_, 1);
                    v_a_8525_ = v_a_8553_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                if v_isShared_8544_ == 0 {
                    lean_ctor_set_tag(v___x_8543_, 1);
                    v___x_8546_ = v___x_8543_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8551_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8551_, 0, v_a_8541_);
                    v___x_8546_ = v_reuseFailAlloc_8551_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_8547_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8547_, 0, v___x_8546_);
                lean_ctor_set(v___x_8547_, 1, v_snd_8519_);
                if v_isShared_8540_ == 0 {
                    lean_ctor_set(v___x_8539_, 0, v___x_8547_);
                    v___x_8549_ = v___x_8539_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8550_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8550_, 0, v___x_8547_);
                    v___x_8549_ = v_reuseFailAlloc_8550_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8549_;
            }
            10 => {
                if v_isShared_8558_ == 0 {
                    v___x_8560_ = v___x_8557_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8561_, 0, v_a_8555_);
                    v___x_8560_ = v_reuseFailAlloc_8561_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8560_;
            }
            12 => {
                v___x_8564_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__2);
                v___x_8565_ = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkDvds_spec__0(
                    v___x_8564_,
                    v___y_8506_,
                    v___y_8507_,
                    v___y_8508_,
                    v___y_8509_,
                    v___y_8510_,
                    v___y_8511_,
                    v___y_8512_,
                    v___y_8513_,
                    v___y_8514_,
                    v___y_8515_,
                );
                v___y_8536_ = v___x_8565_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2___boxed(
    mut v_a_8584_: *mut LeanObject,
    mut v_as_8585_: *mut LeanObject,
    mut v_sz_8586_: *mut LeanObject,
    mut v_i_8587_: *mut LeanObject,
    mut v_b_8588_: *mut LeanObject,
    mut v___y_8589_: *mut LeanObject,
    mut v___y_8590_: *mut LeanObject,
    mut v___y_8591_: *mut LeanObject,
    mut v___y_8592_: *mut LeanObject,
    mut v___y_8593_: *mut LeanObject,
    mut v___y_8594_: *mut LeanObject,
    mut v___y_8595_: *mut LeanObject,
    mut v___y_8596_: *mut LeanObject,
    mut v___y_8597_: *mut LeanObject,
    mut v___y_8598_: *mut LeanObject,
    mut v___y_8599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8600_: usize = 0;
    let mut v_i_boxed_8601_: usize = 0;
    let mut v_res_8602_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8600_ = lean_unbox_usize(v_sz_8586_);
    lean_dec(v_sz_8586_);
    v_i_boxed_8601_ = lean_unbox_usize(v_i_8587_);
    lean_dec(v_i_8587_);
    v_res_8602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_8584_, v_as_8585_, v_sz_boxed_8600_, v_i_boxed_8601_, v_b_8588_, v___y_8589_, v___y_8590_, v___y_8591_, v___y_8592_, v___y_8593_, v___y_8594_, v___y_8595_, v___y_8596_, v___y_8597_, v___y_8598_);
    lean_dec(v___y_8598_);
    lean_dec_ref(v___y_8597_);
    lean_dec(v___y_8596_);
    lean_dec_ref(v___y_8595_);
    lean_dec(v___y_8594_);
    lean_dec_ref(v___y_8593_);
    lean_dec(v___y_8592_);
    lean_dec_ref(v___y_8591_);
    lean_dec(v___y_8590_);
    lean_dec(v___y_8589_);
    lean_dec_ref(v_as_8585_);
    lean_dec_ref(v_a_8584_);
    return v_res_8602_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(
    mut v_a_8603_: *mut LeanObject,
    mut v_t_8604_: *mut LeanObject,
    mut v_init_8605_: *mut LeanObject,
    mut v___y_8606_: *mut LeanObject,
    mut v___y_8607_: *mut LeanObject,
    mut v___y_8608_: *mut LeanObject,
    mut v___y_8609_: *mut LeanObject,
    mut v___y_8610_: *mut LeanObject,
    mut v___y_8611_: *mut LeanObject,
    mut v___y_8612_: *mut LeanObject,
    mut v___y_8613_: *mut LeanObject,
    mut v___y_8614_: *mut LeanObject,
    mut v___y_8615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_8617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8623_: u8 = 0;
    let mut v_a_8624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8631_: usize = 0;
    let mut v___x_8632_: usize = 0;
    let mut v___x_8633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8637_: u8 = 0;
    let mut v_fst_8638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8647_: u8 = 0;
    let mut v_a_8648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8651_: u8 = 0;
    let mut v___x_8653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8655_: u8 = 0;
    let mut v_isSharedCheck_8656_: u8 = 0;
    let mut v_a_8657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8660_: u8 = 0;
    let mut v___x_8662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_8617_ = lean_ctor_get(v_t_8604_, 0);
                v_tail_8618_ = lean_ctor_get(v_t_8604_, 1);
                lean_inc(v_init_8605_);
                v___x_8619_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1(v_init_8605_, v_a_8603_, v_root_8617_, v_init_8605_, v___y_8606_, v___y_8607_, v___y_8608_, v___y_8609_, v___y_8610_, v___y_8611_, v___y_8612_, v___y_8613_, v___y_8614_, v___y_8615_);
                lean_dec(v_init_8605_);
                if lean_obj_tag(v___x_8619_) == 0 {
                    v_a_8620_ = lean_ctor_get(v___x_8619_, 0);
                    v_isSharedCheck_8656_ = (!lean_is_exclusive(v___x_8619_)) as u8;
                    if v_isSharedCheck_8656_ == 0 {
                        v___x_8622_ = v___x_8619_;
                        v_isShared_8623_ = v_isSharedCheck_8656_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8620_);
                        lean_dec(v___x_8619_);
                        v___x_8622_ = lean_box(0);
                        v_isShared_8623_ = v_isSharedCheck_8656_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8657_ = lean_ctor_get(v___x_8619_, 0);
                    v_isSharedCheck_8664_ = (!lean_is_exclusive(v___x_8619_)) as u8;
                    if v_isSharedCheck_8664_ == 0 {
                        v___x_8659_ = v___x_8619_;
                        v_isShared_8660_ = v_isSharedCheck_8664_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_8657_);
                        lean_dec(v___x_8619_);
                        v___x_8659_ = lean_box(0);
                        v_isShared_8660_ = v_isSharedCheck_8664_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_8620_) == 0 {
                    v_a_8624_ = lean_ctor_get(v_a_8620_, 0);
                    lean_inc(v_a_8624_);
                    lean_dec_ref_known(v_a_8620_, 1);
                    if v_isShared_8623_ == 0 {
                        lean_ctor_set(v___x_8622_, 0, v_a_8624_);
                        v___x_8626_ = v___x_8622_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8627_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8627_, 0, v_a_8624_);
                        v___x_8626_ = v_reuseFailAlloc_8627_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8622_);
                    v_a_8628_ = lean_ctor_get(v_a_8620_, 0);
                    lean_inc(v_a_8628_);
                    lean_dec_ref_known(v_a_8620_, 1);
                    v___x_8629_ = lean_box(0);
                    v___x_8630_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8630_, 0, v___x_8629_);
                    lean_ctor_set(v___x_8630_, 1, v_a_8628_);
                    v_sz_8631_ = lean_array_size(v_tail_8618_);
                    v___x_8632_ = 0usize;
                    v___x_8633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__2(v_a_8603_, v_tail_8618_, v_sz_8631_, v___x_8632_, v___x_8630_, v___y_8606_, v___y_8607_, v___y_8608_, v___y_8609_, v___y_8610_, v___y_8611_, v___y_8612_, v___y_8613_, v___y_8614_, v___y_8615_);
                    if lean_obj_tag(v___x_8633_) == 0 {
                        v_a_8634_ = lean_ctor_get(v___x_8633_, 0);
                        v_isSharedCheck_8647_ = (!lean_is_exclusive(v___x_8633_)) as u8;
                        if v_isSharedCheck_8647_ == 0 {
                            v___x_8636_ = v___x_8633_;
                            v_isShared_8637_ = v_isSharedCheck_8647_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_8634_);
                            lean_dec(v___x_8633_);
                            v___x_8636_ = lean_box(0);
                            v_isShared_8637_ = v_isSharedCheck_8647_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_8648_ = lean_ctor_get(v___x_8633_, 0);
                        v_isSharedCheck_8655_ = (!lean_is_exclusive(v___x_8633_)) as u8;
                        if v_isSharedCheck_8655_ == 0 {
                            v___x_8650_ = v___x_8633_;
                            v_isShared_8651_ = v_isSharedCheck_8655_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_8648_);
                            lean_dec(v___x_8633_);
                            v___x_8650_ = lean_box(0);
                            v_isShared_8651_ = v_isSharedCheck_8655_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8626_;
            }
            3 => {
                v_fst_8638_ = lean_ctor_get(v_a_8634_, 0);
                if lean_obj_tag(v_fst_8638_) == 0 {
                    v_snd_8639_ = lean_ctor_get(v_a_8634_, 1);
                    lean_inc(v_snd_8639_);
                    lean_dec(v_a_8634_);
                    if v_isShared_8637_ == 0 {
                        lean_ctor_set(v___x_8636_, 0, v_snd_8639_);
                        v___x_8641_ = v___x_8636_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8642_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8642_, 0, v_snd_8639_);
                        v___x_8641_ = v_reuseFailAlloc_8642_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_8638_);
                    lean_dec(v_a_8634_);
                    v_val_8643_ = lean_ctor_get(v_fst_8638_, 0);
                    lean_inc(v_val_8643_);
                    lean_dec_ref_known(v_fst_8638_, 1);
                    if v_isShared_8637_ == 0 {
                        lean_ctor_set(v___x_8636_, 0, v_val_8643_);
                        v___x_8645_ = v___x_8636_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8646_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8646_, 0, v_val_8643_);
                        v___x_8645_ = v_reuseFailAlloc_8646_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_8641_;
            }
            5 => {
                return v___x_8645_;
            }
            6 => {
                if v_isShared_8651_ == 0 {
                    v___x_8653_ = v___x_8650_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8654_, 0, v_a_8648_);
                    v___x_8653_ = v_reuseFailAlloc_8654_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8653_;
            }
            8 => {
                if v_isShared_8660_ == 0 {
                    v___x_8662_ = v___x_8659_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8663_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8663_, 0, v_a_8657_);
                    v___x_8662_ = v_reuseFailAlloc_8663_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1___boxed(
    mut v_a_8665_: *mut LeanObject,
    mut v_t_8666_: *mut LeanObject,
    mut v_init_8667_: *mut LeanObject,
    mut v___y_8668_: *mut LeanObject,
    mut v___y_8669_: *mut LeanObject,
    mut v___y_8670_: *mut LeanObject,
    mut v___y_8671_: *mut LeanObject,
    mut v___y_8672_: *mut LeanObject,
    mut v___y_8673_: *mut LeanObject,
    mut v___y_8674_: *mut LeanObject,
    mut v___y_8675_: *mut LeanObject,
    mut v___y_8676_: *mut LeanObject,
    mut v___y_8677_: *mut LeanObject,
    mut v___y_8678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8679_: *mut LeanObject = core::ptr::null_mut();
    v_res_8679_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(
            v_a_8665_,
            v_t_8666_,
            v_init_8667_,
            v___y_8668_,
            v___y_8669_,
            v___y_8670_,
            v___y_8671_,
            v___y_8672_,
            v___y_8673_,
            v___y_8674_,
            v___y_8675_,
            v___y_8676_,
            v___y_8677_,
        );
    lean_dec(v___y_8677_);
    lean_dec_ref(v___y_8676_);
    lean_dec(v___y_8675_);
    lean_dec_ref(v___y_8674_);
    lean_dec(v___y_8673_);
    lean_dec_ref(v___y_8672_);
    lean_dec(v___y_8671_);
    lean_dec_ref(v___y_8670_);
    lean_dec(v___y_8669_);
    lean_dec(v___y_8668_);
    lean_dec_ref(v_t_8666_);
    lean_dec_ref(v_a_8665_);
    return v_res_8679_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1() -> *mut LeanObject {
    let mut v___x_8681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8686_: *mut LeanObject = core::ptr::null_mut();
    v___x_8681_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__0;
    v___x_8682_ = lean_unsigned_to_nat(2);
    v___x_8683_ = lean_unsigned_to_nat(87);
    v___x_8684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1_spec__1_spec__3_spec__4___closed__0;
    v___x_8685_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_8686_ = l_mkPanicMessageWithDecl(
        v___x_8685_,
        v___x_8684_,
        v___x_8683_,
        v___x_8682_,
        v___x_8681_,
    );
    return v___x_8686_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(
    mut v_a_8687_: *mut LeanObject,
    mut v_a_8688_: *mut LeanObject,
    mut v_a_8689_: *mut LeanObject,
    mut v_a_8690_: *mut LeanObject,
    mut v_a_8691_: *mut LeanObject,
    mut v_a_8692_: *mut LeanObject,
    mut v_a_8693_: *mut LeanObject,
    mut v_a_8694_: *mut LeanObject,
    mut v_a_8695_: *mut LeanObject,
    mut v_a_8696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_8700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_8701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_8702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_8703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8704_: u8 = 0;
    let mut v___x_8705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8711_: u8 = 0;
    let mut v___x_8712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8716_: u8 = 0;
    let mut v_unused_8717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8721_: u8 = 0;
    let mut v___x_8723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8725_: u8 = 0;
    let mut v_a_8726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8729_: u8 = 0;
    let mut v___x_8731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8698_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_8687_, v_a_8695_);
                if lean_obj_tag(v___x_8698_) == 0 {
                    v_a_8699_ = lean_ctor_get(v___x_8698_, 0);
                    lean_inc(v_a_8699_);
                    lean_dec_ref_known(v___x_8698_, 1);
                    v_elimEqs_8700_ = lean_ctor_get(v_a_8699_, 10);
                    lean_inc_ref(v_elimEqs_8700_);
                    v_vars_8701_ = lean_ctor_get(v_a_8699_, 0);
                    v_size_8702_ = lean_ctor_get(v_elimEqs_8700_, 2);
                    v_size_8703_ = lean_ctor_get(v_vars_8701_, 2);
                    v___x_8704_ = lean_nat_dec_eq(v_size_8702_, v_size_8703_);
                    if v___x_8704_ == 0 {
                        lean_dec_ref(v_elimEqs_8700_);
                        lean_dec(v_a_8699_);
                        v___x_8705_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___closed__1,
                        );
                        v___x_8706_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_8705_,
                            v_a_8687_,
                            v_a_8688_,
                            v_a_8689_,
                            v_a_8690_,
                            v_a_8691_,
                            v_a_8692_,
                            v_a_8693_,
                            v_a_8694_,
                            v_a_8695_,
                            v_a_8696_,
                        );
                        return v___x_8706_;
                    } else {
                        v___x_8707_ = lean_unsigned_to_nat(0);
                        v___x_8708_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__1(v_a_8699_, v_elimEqs_8700_, v___x_8707_, v_a_8687_, v_a_8688_, v_a_8689_, v_a_8690_, v_a_8691_, v_a_8692_, v_a_8693_, v_a_8694_, v_a_8695_, v_a_8696_);
                        lean_dec_ref(v_elimEqs_8700_);
                        lean_dec(v_a_8699_);
                        if lean_obj_tag(v___x_8708_) == 0 {
                            v_isSharedCheck_8716_ = (!lean_is_exclusive(v___x_8708_)) as u8;
                            if v_isSharedCheck_8716_ == 0 {
                                v_unused_8717_ = lean_ctor_get(v___x_8708_, 0);
                                lean_dec(v_unused_8717_);
                                v___x_8710_ = v___x_8708_;
                                v_isShared_8711_ = v_isSharedCheck_8716_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_8708_);
                                v___x_8710_ = lean_box(0);
                                v_isShared_8711_ = v_isSharedCheck_8716_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_8718_ = lean_ctor_get(v___x_8708_, 0);
                            v_isSharedCheck_8725_ = (!lean_is_exclusive(v___x_8708_)) as u8;
                            if v_isSharedCheck_8725_ == 0 {
                                v___x_8720_ = v___x_8708_;
                                v_isShared_8721_ = v_isSharedCheck_8725_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_8718_);
                                lean_dec(v___x_8708_);
                                v___x_8720_ = lean_box(0);
                                v_isShared_8721_ = v_isSharedCheck_8725_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_8726_ = lean_ctor_get(v___x_8698_, 0);
                    v_isSharedCheck_8733_ = (!lean_is_exclusive(v___x_8698_)) as u8;
                    if v_isSharedCheck_8733_ == 0 {
                        v___x_8728_ = v___x_8698_;
                        v_isShared_8729_ = v_isSharedCheck_8733_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_8726_);
                        lean_dec(v___x_8698_);
                        v___x_8728_ = lean_box(0);
                        v_isShared_8729_ = v_isSharedCheck_8733_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8712_ = lean_box(0);
                if v_isShared_8711_ == 0 {
                    lean_ctor_set(v___x_8710_, 0, v___x_8712_);
                    v___x_8714_ = v___x_8710_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8715_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8715_, 0, v___x_8712_);
                    v___x_8714_ = v_reuseFailAlloc_8715_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8714_;
            }
            3 => {
                if v_isShared_8721_ == 0 {
                    v___x_8723_ = v___x_8720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8724_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8724_, 0, v_a_8718_);
                    v___x_8723_ = v_reuseFailAlloc_8724_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8723_;
            }
            5 => {
                if v_isShared_8729_ == 0 {
                    v___x_8731_ = v___x_8728_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8732_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8732_, 0, v_a_8726_);
                    v___x_8731_ = v_reuseFailAlloc_8732_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs___boxed(
    mut v_a_8734_: *mut LeanObject,
    mut v_a_8735_: *mut LeanObject,
    mut v_a_8736_: *mut LeanObject,
    mut v_a_8737_: *mut LeanObject,
    mut v_a_8738_: *mut LeanObject,
    mut v_a_8739_: *mut LeanObject,
    mut v_a_8740_: *mut LeanObject,
    mut v_a_8741_: *mut LeanObject,
    mut v_a_8742_: *mut LeanObject,
    mut v_a_8743_: *mut LeanObject,
    mut v_a_8744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8745_: *mut LeanObject = core::ptr::null_mut();
    v_res_8745_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(
        v_a_8734_, v_a_8735_, v_a_8736_, v_a_8737_, v_a_8738_, v_a_8739_, v_a_8740_, v_a_8741_,
        v_a_8742_, v_a_8743_,
    );
    lean_dec(v_a_8743_);
    lean_dec_ref(v_a_8742_);
    lean_dec(v_a_8741_);
    lean_dec_ref(v_a_8740_);
    lean_dec(v_a_8739_);
    lean_dec_ref(v_a_8738_);
    lean_dec(v_a_8737_);
    lean_dec_ref(v_a_8736_);
    lean_dec(v_a_8735_);
    lean_dec(v_a_8734_);
    return v_res_8745_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_8748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8753_: *mut LeanObject = core::ptr::null_mut();
    v___x_8748_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__1;
    v___x_8749_ = lean_unsigned_to_nat(4);
    v___x_8750_ = lean_unsigned_to_nat(99);
    v___x_8751_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__0;
    v___x_8752_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_8753_ = l_mkPanicMessageWithDecl(
        v___x_8752_,
        v___x_8751_,
        v___x_8750_,
        v___x_8749_,
        v___x_8748_,
    );
    return v___x_8753_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(
    mut v_as_x27_8754_: *mut LeanObject,
    mut v_b_8755_: *mut LeanObject,
    mut v___y_8756_: *mut LeanObject,
    mut v___y_8757_: *mut LeanObject,
    mut v___y_8758_: *mut LeanObject,
    mut v___y_8759_: *mut LeanObject,
    mut v___y_8760_: *mut LeanObject,
    mut v___y_8761_: *mut LeanObject,
    mut v___y_8762_: *mut LeanObject,
    mut v___y_8763_: *mut LeanObject,
    mut v___y_8764_: *mut LeanObject,
    mut v___y_8765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_8768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8772_: u8 = 0;
    let mut v___x_8773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8778_: u8 = 0;
    let mut v_a_8779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8785_: u8 = 0;
    let mut v_a_8786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8789_: u8 = 0;
    let mut v___x_8791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8793_: u8 = 0;
    let mut v___x_8794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8799_: u8 = 0;
    let mut v___x_8801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_8754_) == 0 {
                    v___x_8767_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8767_, 0, v_b_8755_);
                    return v___x_8767_;
                } else {
                    v_head_8768_ = lean_ctor_get(v_as_x27_8754_, 0);
                    v_tail_8769_ = lean_ctor_get(v_as_x27_8754_, 1);
                    v___x_8770_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(
                        v_head_8768_,
                        v___y_8756_,
                        v___y_8764_,
                    );
                    if lean_obj_tag(v___x_8770_) == 0 {
                        v_a_8771_ = lean_ctor_get(v___x_8770_, 0);
                        lean_inc(v_a_8771_);
                        lean_dec_ref_known(v___x_8770_, 1);
                        v___x_8772_ = (lean_unbox(v_a_8771_) as u8);
                        lean_dec(v_a_8771_);
                        if v___x_8772_ == 0 {
                            v___x_8773_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___closed__2);
                            v___x_8774_ =
                                l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_checkLeCnstrs_spec__0(
                                    v___x_8773_,
                                    v___y_8756_,
                                    v___y_8757_,
                                    v___y_8758_,
                                    v___y_8759_,
                                    v___y_8760_,
                                    v___y_8761_,
                                    v___y_8762_,
                                    v___y_8763_,
                                    v___y_8764_,
                                    v___y_8765_,
                                );
                            if lean_obj_tag(v___x_8774_) == 0 {
                                v_a_8775_ = lean_ctor_get(v___x_8774_, 0);
                                v_isSharedCheck_8785_ = (!lean_is_exclusive(v___x_8774_)) as u8;
                                if v_isSharedCheck_8785_ == 0 {
                                    v___x_8777_ = v___x_8774_;
                                    v_isShared_8778_ = v_isSharedCheck_8785_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_8775_);
                                    lean_dec(v___x_8774_);
                                    v___x_8777_ = lean_box(0);
                                    v_isShared_8778_ = v_isSharedCheck_8785_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_8786_ = lean_ctor_get(v___x_8774_, 0);
                                v_isSharedCheck_8793_ = (!lean_is_exclusive(v___x_8774_)) as u8;
                                if v_isSharedCheck_8793_ == 0 {
                                    v___x_8788_ = v___x_8774_;
                                    v_isShared_8789_ = v_isSharedCheck_8793_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_8786_);
                                    lean_dec(v___x_8774_);
                                    v___x_8788_ = lean_box(0);
                                    v_isShared_8789_ = v_isSharedCheck_8793_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_8794_ = lean_box(0);
                            v_as_x27_8754_ = v_tail_8769_;
                            v_b_8755_ = v___x_8794_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_a_8796_ = lean_ctor_get(v___x_8770_, 0);
                        v_isSharedCheck_8803_ = (!lean_is_exclusive(v___x_8770_)) as u8;
                        if v_isSharedCheck_8803_ == 0 {
                            v___x_8798_ = v___x_8770_;
                            v_isShared_8799_ = v_isSharedCheck_8803_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_8796_);
                            lean_dec(v___x_8770_);
                            v___x_8798_ = lean_box(0);
                            v_isShared_8799_ = v_isSharedCheck_8803_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_8775_) == 0 {
                    v_a_8779_ = lean_ctor_get(v_a_8775_, 0);
                    lean_inc(v_a_8779_);
                    lean_dec_ref_known(v_a_8775_, 1);
                    if v_isShared_8778_ == 0 {
                        lean_ctor_set(v___x_8777_, 0, v_a_8779_);
                        v___x_8781_ = v___x_8777_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8782_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8782_, 0, v_a_8779_);
                        v___x_8781_ = v_reuseFailAlloc_8782_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8777_);
                    v_a_8783_ = lean_ctor_get(v_a_8775_, 0);
                    lean_inc(v_a_8783_);
                    lean_dec_ref_known(v_a_8775_, 1);
                    v_as_x27_8754_ = v_tail_8769_;
                    v_b_8755_ = v_a_8783_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_8781_;
            }
            3 => {
                if v_isShared_8789_ == 0 {
                    v___x_8791_ = v___x_8788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8792_, 0, v_a_8786_);
                    v___x_8791_ = v_reuseFailAlloc_8792_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8791_;
            }
            5 => {
                if v_isShared_8799_ == 0 {
                    v___x_8801_ = v___x_8798_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8802_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8802_, 0, v_a_8796_);
                    v___x_8801_ = v_reuseFailAlloc_8802_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg___boxed(
    mut v_as_x27_8804_: *mut LeanObject,
    mut v_b_8805_: *mut LeanObject,
    mut v___y_8806_: *mut LeanObject,
    mut v___y_8807_: *mut LeanObject,
    mut v___y_8808_: *mut LeanObject,
    mut v___y_8809_: *mut LeanObject,
    mut v___y_8810_: *mut LeanObject,
    mut v___y_8811_: *mut LeanObject,
    mut v___y_8812_: *mut LeanObject,
    mut v___y_8813_: *mut LeanObject,
    mut v___y_8814_: *mut LeanObject,
    mut v___y_8815_: *mut LeanObject,
    mut v___y_8816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8817_: *mut LeanObject = core::ptr::null_mut();
    v_res_8817_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(
            v_as_x27_8804_,
            v_b_8805_,
            v___y_8806_,
            v___y_8807_,
            v___y_8808_,
            v___y_8809_,
            v___y_8810_,
            v___y_8811_,
            v___y_8812_,
            v___y_8813_,
            v___y_8814_,
            v___y_8815_,
        );
    lean_dec(v___y_8815_);
    lean_dec_ref(v___y_8814_);
    lean_dec(v___y_8813_);
    lean_dec_ref(v___y_8812_);
    lean_dec(v___y_8811_);
    lean_dec_ref(v___y_8810_);
    lean_dec(v___y_8809_);
    lean_dec_ref(v___y_8808_);
    lean_dec(v___y_8807_);
    lean_dec(v___y_8806_);
    lean_dec(v_as_x27_8804_);
    return v_res_8817_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(
    mut v_a_8818_: *mut LeanObject,
    mut v_a_8819_: *mut LeanObject,
    mut v_a_8820_: *mut LeanObject,
    mut v_a_8821_: *mut LeanObject,
    mut v_a_8822_: *mut LeanObject,
    mut v_a_8823_: *mut LeanObject,
    mut v_a_8824_: *mut LeanObject,
    mut v_a_8825_: *mut LeanObject,
    mut v_a_8826_: *mut LeanObject,
    mut v_a_8827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_8831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8836_: u8 = 0;
    let mut v___x_8838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8840_: u8 = 0;
    let mut v_unused_8841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8845_: u8 = 0;
    let mut v___x_8847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8829_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_8818_, v_a_8826_);
                if lean_obj_tag(v___x_8829_) == 0 {
                    v_a_8830_ = lean_ctor_get(v___x_8829_, 0);
                    lean_inc(v_a_8830_);
                    lean_dec_ref_known(v___x_8829_, 1);
                    v_elimStack_8831_ = lean_ctor_get(v_a_8830_, 11);
                    lean_inc(v_elimStack_8831_);
                    lean_dec(v_a_8830_);
                    v___x_8832_ = lean_box(0);
                    v___x_8833_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(v_elimStack_8831_, v___x_8832_, v_a_8818_, v_a_8819_, v_a_8820_, v_a_8821_, v_a_8822_, v_a_8823_, v_a_8824_, v_a_8825_, v_a_8826_, v_a_8827_);
                    lean_dec(v_elimStack_8831_);
                    if lean_obj_tag(v___x_8833_) == 0 {
                        v_isSharedCheck_8840_ = (!lean_is_exclusive(v___x_8833_)) as u8;
                        if v_isSharedCheck_8840_ == 0 {
                            v_unused_8841_ = lean_ctor_get(v___x_8833_, 0);
                            lean_dec(v_unused_8841_);
                            v___x_8835_ = v___x_8833_;
                            v_isShared_8836_ = v_isSharedCheck_8840_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_8833_);
                            v___x_8835_ = lean_box(0);
                            v_isShared_8836_ = v_isSharedCheck_8840_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_8833_;
                    }
                } else {
                    v_a_8842_ = lean_ctor_get(v___x_8829_, 0);
                    v_isSharedCheck_8849_ = (!lean_is_exclusive(v___x_8829_)) as u8;
                    if v_isSharedCheck_8849_ == 0 {
                        v___x_8844_ = v___x_8829_;
                        v_isShared_8845_ = v_isSharedCheck_8849_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8842_);
                        lean_dec(v___x_8829_);
                        v___x_8844_ = lean_box(0);
                        v_isShared_8845_ = v_isSharedCheck_8849_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8836_ == 0 {
                    lean_ctor_set(v___x_8835_, 0, v___x_8832_);
                    v___x_8838_ = v___x_8835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8839_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8839_, 0, v___x_8832_);
                    v___x_8838_ = v_reuseFailAlloc_8839_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8838_;
            }
            3 => {
                if v_isShared_8845_ == 0 {
                    v___x_8847_ = v___x_8844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8848_, 0, v_a_8842_);
                    v___x_8847_ = v_reuseFailAlloc_8848_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack___boxed(
    mut v_a_8850_: *mut LeanObject,
    mut v_a_8851_: *mut LeanObject,
    mut v_a_8852_: *mut LeanObject,
    mut v_a_8853_: *mut LeanObject,
    mut v_a_8854_: *mut LeanObject,
    mut v_a_8855_: *mut LeanObject,
    mut v_a_8856_: *mut LeanObject,
    mut v_a_8857_: *mut LeanObject,
    mut v_a_8858_: *mut LeanObject,
    mut v_a_8859_: *mut LeanObject,
    mut v_a_8860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8861_: *mut LeanObject = core::ptr::null_mut();
    v_res_8861_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(
        v_a_8850_, v_a_8851_, v_a_8852_, v_a_8853_, v_a_8854_, v_a_8855_, v_a_8856_, v_a_8857_,
        v_a_8858_, v_a_8859_,
    );
    lean_dec(v_a_8859_);
    lean_dec_ref(v_a_8858_);
    lean_dec(v_a_8857_);
    lean_dec_ref(v_a_8856_);
    lean_dec(v_a_8855_);
    lean_dec_ref(v_a_8854_);
    lean_dec(v_a_8853_);
    lean_dec_ref(v_a_8852_);
    lean_dec(v_a_8851_);
    lean_dec(v_a_8850_);
    return v_res_8861_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(
    mut v_as_8862_: *mut LeanObject,
    mut v_as_x27_8863_: *mut LeanObject,
    mut v_b_8864_: *mut LeanObject,
    mut v_a_8865_: *mut LeanObject,
    mut v___y_8866_: *mut LeanObject,
    mut v___y_8867_: *mut LeanObject,
    mut v___y_8868_: *mut LeanObject,
    mut v___y_8869_: *mut LeanObject,
    mut v___y_8870_: *mut LeanObject,
    mut v___y_8871_: *mut LeanObject,
    mut v___y_8872_: *mut LeanObject,
    mut v___y_8873_: *mut LeanObject,
    mut v___y_8874_: *mut LeanObject,
    mut v___y_8875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8877_: *mut LeanObject = core::ptr::null_mut();
    v___x_8877_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___redArg(
            v_as_x27_8863_,
            v_b_8864_,
            v___y_8866_,
            v___y_8867_,
            v___y_8868_,
            v___y_8869_,
            v___y_8870_,
            v___y_8871_,
            v___y_8872_,
            v___y_8873_,
            v___y_8874_,
            v___y_8875_,
        );
    return v___x_8877_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0___boxed(
    mut v_as_8878_: *mut LeanObject,
    mut v_as_x27_8879_: *mut LeanObject,
    mut v_b_8880_: *mut LeanObject,
    mut v_a_8881_: *mut LeanObject,
    mut v___y_8882_: *mut LeanObject,
    mut v___y_8883_: *mut LeanObject,
    mut v___y_8884_: *mut LeanObject,
    mut v___y_8885_: *mut LeanObject,
    mut v___y_8886_: *mut LeanObject,
    mut v___y_8887_: *mut LeanObject,
    mut v___y_8888_: *mut LeanObject,
    mut v___y_8889_: *mut LeanObject,
    mut v___y_8890_: *mut LeanObject,
    mut v___y_8891_: *mut LeanObject,
    mut v___y_8892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8893_: *mut LeanObject = core::ptr::null_mut();
    v_res_8893_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimStack_spec__0(
            v_as_8878_,
            v_as_x27_8879_,
            v_b_8880_,
            v_a_8881_,
            v___y_8882_,
            v___y_8883_,
            v___y_8884_,
            v___y_8885_,
            v___y_8886_,
            v___y_8887_,
            v___y_8888_,
            v___y_8889_,
            v___y_8890_,
            v___y_8891_,
        );
    lean_dec(v___y_8891_);
    lean_dec_ref(v___y_8890_);
    lean_dec(v___y_8889_);
    lean_dec_ref(v___y_8888_);
    lean_dec(v___y_8887_);
    lean_dec_ref(v___y_8886_);
    lean_dec(v___y_8885_);
    lean_dec_ref(v___y_8884_);
    lean_dec(v___y_8883_);
    lean_dec(v___y_8882_);
    lean_dec(v_as_x27_8879_);
    lean_dec(v_as_8878_);
    return v_res_8893_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(
    mut v_____s_8897_: *mut LeanObject,
    mut v_as_8898_: *mut LeanObject,
    mut v_sz_8899_: usize,
    mut v_i_8900_: usize,
    mut v_b_8901_: *mut LeanObject,
    mut v___y_8902_: *mut LeanObject,
    mut v___y_8903_: *mut LeanObject,
    mut v___y_8904_: *mut LeanObject,
    mut v___y_8905_: *mut LeanObject,
    mut v___y_8906_: *mut LeanObject,
    mut v___y_8907_: *mut LeanObject,
    mut v___y_8908_: *mut LeanObject,
    mut v___y_8909_: *mut LeanObject,
    mut v___y_8910_: *mut LeanObject,
    mut v___y_8911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8913_: u8 = 0;
    let mut v___x_8914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_8916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8919_: usize = 0;
    let mut v___x_8920_: usize = 0;
    let mut v_a_8922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8925_: u8 = 0;
    let mut v___x_8927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8929_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8913_ = lean_usize_dec_lt(v_i_8900_, v_sz_8899_);
                if v___x_8913_ == 0 {
                    v___x_8914_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8914_, 0, v_b_8901_);
                    return v___x_8914_;
                } else {
                    lean_dec_ref(v_b_8901_);
                    v_a_8915_ = lean_array_uget_borrowed(v_as_8898_, v_i_8900_);
                    v_p_8916_ = lean_ctor_get(v_a_8915_, 0);
                    v___x_8917_ = l_Int_Linear_Poly_checkCnstrOf(
                        v_p_8916_,
                        v_____s_8897_,
                        v___y_8902_,
                        v___y_8903_,
                        v___y_8904_,
                        v___y_8905_,
                        v___y_8906_,
                        v___y_8907_,
                        v___y_8908_,
                        v___y_8909_,
                        v___y_8910_,
                        v___y_8911_,
                    );
                    if lean_obj_tag(v___x_8917_) == 0 {
                        lean_dec_ref_known(v___x_8917_, 1);
                        v___x_8918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0;
                        v___x_8919_ = 1usize;
                        v___x_8920_ = lean_usize_add(v_i_8900_, v___x_8919_);
                        v_i_8900_ = v___x_8920_;
                        v_b_8901_ = v___x_8918_;
                        state = 0;
                        continue;
                    } else {
                        v_a_8922_ = lean_ctor_get(v___x_8917_, 0);
                        v_isSharedCheck_8929_ = (!lean_is_exclusive(v___x_8917_)) as u8;
                        if v_isSharedCheck_8929_ == 0 {
                            v___x_8924_ = v___x_8917_;
                            v_isShared_8925_ = v_isSharedCheck_8929_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8922_);
                            lean_dec(v___x_8917_);
                            v___x_8924_ = lean_box(0);
                            v_isShared_8925_ = v_isSharedCheck_8929_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8925_ == 0 {
                    v___x_8927_ = v___x_8924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8928_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8928_, 0, v_a_8922_);
                    v___x_8927_ = v_reuseFailAlloc_8928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(
    mut v_____s_8930_: *mut LeanObject,
    mut v_as_8931_: *mut LeanObject,
    mut v_sz_8932_: *mut LeanObject,
    mut v_i_8933_: *mut LeanObject,
    mut v_b_8934_: *mut LeanObject,
    mut v___y_8935_: *mut LeanObject,
    mut v___y_8936_: *mut LeanObject,
    mut v___y_8937_: *mut LeanObject,
    mut v___y_8938_: *mut LeanObject,
    mut v___y_8939_: *mut LeanObject,
    mut v___y_8940_: *mut LeanObject,
    mut v___y_8941_: *mut LeanObject,
    mut v___y_8942_: *mut LeanObject,
    mut v___y_8943_: *mut LeanObject,
    mut v___y_8944_: *mut LeanObject,
    mut v___y_8945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8946_: usize = 0;
    let mut v_i_boxed_8947_: usize = 0;
    let mut v_res_8948_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8946_ = lean_unbox_usize(v_sz_8932_);
    lean_dec(v_sz_8932_);
    v_i_boxed_8947_ = lean_unbox_usize(v_i_8933_);
    lean_dec(v_i_8933_);
    v_res_8948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_8930_, v_as_8931_, v_sz_boxed_8946_, v_i_boxed_8947_, v_b_8934_, v___y_8935_, v___y_8936_, v___y_8937_, v___y_8938_, v___y_8939_, v___y_8940_, v___y_8941_, v___y_8942_, v___y_8943_, v___y_8944_);
    lean_dec(v___y_8944_);
    lean_dec_ref(v___y_8943_);
    lean_dec(v___y_8942_);
    lean_dec_ref(v___y_8941_);
    lean_dec(v___y_8940_);
    lean_dec_ref(v___y_8939_);
    lean_dec(v___y_8938_);
    lean_dec_ref(v___y_8937_);
    lean_dec(v___y_8936_);
    lean_dec(v___y_8935_);
    lean_dec_ref(v_as_8931_);
    lean_dec(v_____s_8930_);
    return v_res_8948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(
    mut v_____s_8949_: *mut LeanObject,
    mut v_as_8950_: *mut LeanObject,
    mut v_sz_8951_: usize,
    mut v_i_8952_: usize,
    mut v_b_8953_: *mut LeanObject,
    mut v___y_8954_: *mut LeanObject,
    mut v___y_8955_: *mut LeanObject,
    mut v___y_8956_: *mut LeanObject,
    mut v___y_8957_: *mut LeanObject,
    mut v___y_8958_: *mut LeanObject,
    mut v___y_8959_: *mut LeanObject,
    mut v___y_8960_: *mut LeanObject,
    mut v___y_8961_: *mut LeanObject,
    mut v___y_8962_: *mut LeanObject,
    mut v___y_8963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8965_: u8 = 0;
    let mut v___x_8966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_8968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8971_: usize = 0;
    let mut v___x_8972_: usize = 0;
    let mut v___x_8973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8977_: u8 = 0;
    let mut v___x_8979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8981_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8965_ = lean_usize_dec_lt(v_i_8952_, v_sz_8951_);
                if v___x_8965_ == 0 {
                    v___x_8966_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8966_, 0, v_b_8953_);
                    return v___x_8966_;
                } else {
                    lean_dec_ref(v_b_8953_);
                    v_a_8967_ = lean_array_uget_borrowed(v_as_8950_, v_i_8952_);
                    v_p_8968_ = lean_ctor_get(v_a_8967_, 0);
                    v___x_8969_ = l_Int_Linear_Poly_checkCnstrOf(
                        v_p_8968_,
                        v_____s_8949_,
                        v___y_8954_,
                        v___y_8955_,
                        v___y_8956_,
                        v___y_8957_,
                        v___y_8958_,
                        v___y_8959_,
                        v___y_8960_,
                        v___y_8961_,
                        v___y_8962_,
                        v___y_8963_,
                    );
                    if lean_obj_tag(v___x_8969_) == 0 {
                        lean_dec_ref_known(v___x_8969_, 1);
                        v___x_8970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0;
                        v___x_8971_ = 1usize;
                        v___x_8972_ = lean_usize_add(v_i_8952_, v___x_8971_);
                        v___x_8973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_8949_, v_as_8950_, v_sz_8951_, v___x_8972_, v___x_8970_, v___y_8954_, v___y_8955_, v___y_8956_, v___y_8957_, v___y_8958_, v___y_8959_, v___y_8960_, v___y_8961_, v___y_8962_, v___y_8963_);
                        return v___x_8973_;
                    } else {
                        v_a_8974_ = lean_ctor_get(v___x_8969_, 0);
                        v_isSharedCheck_8981_ = (!lean_is_exclusive(v___x_8969_)) as u8;
                        if v_isSharedCheck_8981_ == 0 {
                            v___x_8976_ = v___x_8969_;
                            v_isShared_8977_ = v_isSharedCheck_8981_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8974_);
                            lean_dec(v___x_8969_);
                            v___x_8976_ = lean_box(0);
                            v_isShared_8977_ = v_isSharedCheck_8981_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8977_ == 0 {
                    v___x_8979_ = v___x_8976_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8980_, 0, v_a_8974_);
                    v___x_8979_ = v_reuseFailAlloc_8980_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1___boxed(
    mut v_____s_8982_: *mut LeanObject,
    mut v_as_8983_: *mut LeanObject,
    mut v_sz_8984_: *mut LeanObject,
    mut v_i_8985_: *mut LeanObject,
    mut v_b_8986_: *mut LeanObject,
    mut v___y_8987_: *mut LeanObject,
    mut v___y_8988_: *mut LeanObject,
    mut v___y_8989_: *mut LeanObject,
    mut v___y_8990_: *mut LeanObject,
    mut v___y_8991_: *mut LeanObject,
    mut v___y_8992_: *mut LeanObject,
    mut v___y_8993_: *mut LeanObject,
    mut v___y_8994_: *mut LeanObject,
    mut v___y_8995_: *mut LeanObject,
    mut v___y_8996_: *mut LeanObject,
    mut v___y_8997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8998_: usize = 0;
    let mut v_i_boxed_8999_: usize = 0;
    let mut v_res_9000_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8998_ = lean_unbox_usize(v_sz_8984_);
    lean_dec(v_sz_8984_);
    v_i_boxed_8999_ = lean_unbox_usize(v_i_8985_);
    lean_dec(v_i_8985_);
    v_res_9000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_8982_, v_as_8983_, v_sz_boxed_8998_, v_i_boxed_8999_, v_b_8986_, v___y_8987_, v___y_8988_, v___y_8989_, v___y_8990_, v___y_8991_, v___y_8992_, v___y_8993_, v___y_8994_, v___y_8995_, v___y_8996_);
    lean_dec(v___y_8996_);
    lean_dec_ref(v___y_8995_);
    lean_dec(v___y_8994_);
    lean_dec_ref(v___y_8993_);
    lean_dec(v___y_8992_);
    lean_dec_ref(v___y_8991_);
    lean_dec(v___y_8990_);
    lean_dec_ref(v___y_8989_);
    lean_dec(v___y_8988_);
    lean_dec(v___y_8987_);
    lean_dec_ref(v_as_8983_);
    lean_dec(v_____s_8982_);
    return v_res_9000_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(
    mut v_____s_9004_: *mut LeanObject,
    mut v_as_9005_: *mut LeanObject,
    mut v_sz_9006_: usize,
    mut v_i_9007_: usize,
    mut v_b_9008_: *mut LeanObject,
    mut v___y_9009_: *mut LeanObject,
    mut v___y_9010_: *mut LeanObject,
    mut v___y_9011_: *mut LeanObject,
    mut v___y_9012_: *mut LeanObject,
    mut v___y_9013_: *mut LeanObject,
    mut v___y_9014_: *mut LeanObject,
    mut v___y_9015_: *mut LeanObject,
    mut v___y_9016_: *mut LeanObject,
    mut v___y_9017_: *mut LeanObject,
    mut v___y_9018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9020_: u8 = 0;
    let mut v___x_9021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_9023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9026_: usize = 0;
    let mut v___x_9027_: usize = 0;
    let mut v_a_9029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9032_: u8 = 0;
    let mut v___x_9034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9020_ = lean_usize_dec_lt(v_i_9007_, v_sz_9006_);
                if v___x_9020_ == 0 {
                    v___x_9021_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9021_, 0, v_b_9008_);
                    return v___x_9021_;
                } else {
                    lean_dec_ref(v_b_9008_);
                    v_a_9022_ = lean_array_uget_borrowed(v_as_9005_, v_i_9007_);
                    v_p_9023_ = lean_ctor_get(v_a_9022_, 0);
                    v___x_9024_ = l_Int_Linear_Poly_checkCnstrOf(
                        v_p_9023_,
                        v_____s_9004_,
                        v___y_9009_,
                        v___y_9010_,
                        v___y_9011_,
                        v___y_9012_,
                        v___y_9013_,
                        v___y_9014_,
                        v___y_9015_,
                        v___y_9016_,
                        v___y_9017_,
                        v___y_9018_,
                    );
                    if lean_obj_tag(v___x_9024_) == 0 {
                        lean_dec_ref_known(v___x_9024_, 1);
                        v___x_9025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0;
                        v___x_9026_ = 1usize;
                        v___x_9027_ = lean_usize_add(v_i_9007_, v___x_9026_);
                        v_i_9007_ = v___x_9027_;
                        v_b_9008_ = v___x_9025_;
                        state = 0;
                        continue;
                    } else {
                        v_a_9029_ = lean_ctor_get(v___x_9024_, 0);
                        v_isSharedCheck_9036_ = (!lean_is_exclusive(v___x_9024_)) as u8;
                        if v_isSharedCheck_9036_ == 0 {
                            v___x_9031_ = v___x_9024_;
                            v_isShared_9032_ = v_isSharedCheck_9036_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9029_);
                            lean_dec(v___x_9024_);
                            v___x_9031_ = lean_box(0);
                            v_isShared_9032_ = v_isSharedCheck_9036_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_9032_ == 0 {
                    v___x_9034_ = v___x_9031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9035_, 0, v_a_9029_);
                    v___x_9034_ = v_reuseFailAlloc_9035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_____s_9037_: *mut LeanObject,
    mut v_as_9038_: *mut LeanObject,
    mut v_sz_9039_: *mut LeanObject,
    mut v_i_9040_: *mut LeanObject,
    mut v_b_9041_: *mut LeanObject,
    mut v___y_9042_: *mut LeanObject,
    mut v___y_9043_: *mut LeanObject,
    mut v___y_9044_: *mut LeanObject,
    mut v___y_9045_: *mut LeanObject,
    mut v___y_9046_: *mut LeanObject,
    mut v___y_9047_: *mut LeanObject,
    mut v___y_9048_: *mut LeanObject,
    mut v___y_9049_: *mut LeanObject,
    mut v___y_9050_: *mut LeanObject,
    mut v___y_9051_: *mut LeanObject,
    mut v___y_9052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9053_: usize = 0;
    let mut v_i_boxed_9054_: usize = 0;
    let mut v_res_9055_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9053_ = lean_unbox_usize(v_sz_9039_);
    lean_dec(v_sz_9039_);
    v_i_boxed_9054_ = lean_unbox_usize(v_i_9040_);
    lean_dec(v_i_9040_);
    v_res_9055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_9037_, v_as_9038_, v_sz_boxed_9053_, v_i_boxed_9054_, v_b_9041_, v___y_9042_, v___y_9043_, v___y_9044_, v___y_9045_, v___y_9046_, v___y_9047_, v___y_9048_, v___y_9049_, v___y_9050_, v___y_9051_);
    lean_dec(v___y_9051_);
    lean_dec_ref(v___y_9050_);
    lean_dec(v___y_9049_);
    lean_dec_ref(v___y_9048_);
    lean_dec(v___y_9047_);
    lean_dec_ref(v___y_9046_);
    lean_dec(v___y_9045_);
    lean_dec_ref(v___y_9044_);
    lean_dec(v___y_9043_);
    lean_dec(v___y_9042_);
    lean_dec_ref(v_as_9038_);
    lean_dec(v_____s_9037_);
    return v_res_9055_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(
    mut v_____s_9056_: *mut LeanObject,
    mut v_as_9057_: *mut LeanObject,
    mut v_sz_9058_: usize,
    mut v_i_9059_: usize,
    mut v_b_9060_: *mut LeanObject,
    mut v___y_9061_: *mut LeanObject,
    mut v___y_9062_: *mut LeanObject,
    mut v___y_9063_: *mut LeanObject,
    mut v___y_9064_: *mut LeanObject,
    mut v___y_9065_: *mut LeanObject,
    mut v___y_9066_: *mut LeanObject,
    mut v___y_9067_: *mut LeanObject,
    mut v___y_9068_: *mut LeanObject,
    mut v___y_9069_: *mut LeanObject,
    mut v___y_9070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9072_: u8 = 0;
    let mut v___x_9073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_9075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9078_: usize = 0;
    let mut v___x_9079_: usize = 0;
    let mut v___x_9080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9084_: u8 = 0;
    let mut v___x_9086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9072_ = lean_usize_dec_lt(v_i_9059_, v_sz_9058_);
                if v___x_9072_ == 0 {
                    v___x_9073_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9073_, 0, v_b_9060_);
                    return v___x_9073_;
                } else {
                    lean_dec_ref(v_b_9060_);
                    v_a_9074_ = lean_array_uget_borrowed(v_as_9057_, v_i_9059_);
                    v_p_9075_ = lean_ctor_get(v_a_9074_, 0);
                    v___x_9076_ = l_Int_Linear_Poly_checkCnstrOf(
                        v_p_9075_,
                        v_____s_9056_,
                        v___y_9061_,
                        v___y_9062_,
                        v___y_9063_,
                        v___y_9064_,
                        v___y_9065_,
                        v___y_9066_,
                        v___y_9067_,
                        v___y_9068_,
                        v___y_9069_,
                        v___y_9070_,
                    );
                    if lean_obj_tag(v___x_9076_) == 0 {
                        lean_dec_ref_known(v___x_9076_, 1);
                        v___x_9077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0;
                        v___x_9078_ = 1usize;
                        v___x_9079_ = lean_usize_add(v_i_9059_, v___x_9078_);
                        v___x_9080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_9056_, v_as_9057_, v_sz_9058_, v___x_9079_, v___x_9077_, v___y_9061_, v___y_9062_, v___y_9063_, v___y_9064_, v___y_9065_, v___y_9066_, v___y_9067_, v___y_9068_, v___y_9069_, v___y_9070_);
                        return v___x_9080_;
                    } else {
                        v_a_9081_ = lean_ctor_get(v___x_9076_, 0);
                        v_isSharedCheck_9088_ = (!lean_is_exclusive(v___x_9076_)) as u8;
                        if v_isSharedCheck_9088_ == 0 {
                            v___x_9083_ = v___x_9076_;
                            v_isShared_9084_ = v_isSharedCheck_9088_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9081_);
                            lean_dec(v___x_9076_);
                            v___x_9083_ = lean_box(0);
                            v_isShared_9084_ = v_isSharedCheck_9088_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_9084_ == 0 {
                    v___x_9086_ = v___x_9083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9087_, 0, v_a_9081_);
                    v___x_9086_ = v_reuseFailAlloc_9087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(
    mut v_____s_9089_: *mut LeanObject,
    mut v_as_9090_: *mut LeanObject,
    mut v_sz_9091_: *mut LeanObject,
    mut v_i_9092_: *mut LeanObject,
    mut v_b_9093_: *mut LeanObject,
    mut v___y_9094_: *mut LeanObject,
    mut v___y_9095_: *mut LeanObject,
    mut v___y_9096_: *mut LeanObject,
    mut v___y_9097_: *mut LeanObject,
    mut v___y_9098_: *mut LeanObject,
    mut v___y_9099_: *mut LeanObject,
    mut v___y_9100_: *mut LeanObject,
    mut v___y_9101_: *mut LeanObject,
    mut v___y_9102_: *mut LeanObject,
    mut v___y_9103_: *mut LeanObject,
    mut v___y_9104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9105_: usize = 0;
    let mut v_i_boxed_9106_: usize = 0;
    let mut v_res_9107_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9105_ = lean_unbox_usize(v_sz_9091_);
    lean_dec(v_sz_9091_);
    v_i_boxed_9106_ = lean_unbox_usize(v_i_9092_);
    lean_dec(v_i_9092_);
    v_res_9107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_9089_, v_as_9090_, v_sz_boxed_9105_, v_i_boxed_9106_, v_b_9093_, v___y_9094_, v___y_9095_, v___y_9096_, v___y_9097_, v___y_9098_, v___y_9099_, v___y_9100_, v___y_9101_, v___y_9102_, v___y_9103_);
    lean_dec(v___y_9103_);
    lean_dec_ref(v___y_9102_);
    lean_dec(v___y_9101_);
    lean_dec_ref(v___y_9100_);
    lean_dec(v___y_9099_);
    lean_dec_ref(v___y_9098_);
    lean_dec(v___y_9097_);
    lean_dec_ref(v___y_9096_);
    lean_dec(v___y_9095_);
    lean_dec(v___y_9094_);
    lean_dec_ref(v_as_9090_);
    lean_dec(v_____s_9089_);
    return v_res_9107_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(
    mut v_init_9108_: *mut LeanObject,
    mut v_____s_9109_: *mut LeanObject,
    mut v_n_9110_: *mut LeanObject,
    mut v_b_9111_: *mut LeanObject,
    mut v___y_9112_: *mut LeanObject,
    mut v___y_9113_: *mut LeanObject,
    mut v___y_9114_: *mut LeanObject,
    mut v___y_9115_: *mut LeanObject,
    mut v___y_9116_: *mut LeanObject,
    mut v___y_9117_: *mut LeanObject,
    mut v___y_9118_: *mut LeanObject,
    mut v___y_9119_: *mut LeanObject,
    mut v___y_9120_: *mut LeanObject,
    mut v___y_9121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_9123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9126_: usize = 0;
    let mut v___x_9127_: usize = 0;
    let mut v___x_9128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9132_: u8 = 0;
    let mut v_fst_9133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9143_: u8 = 0;
    let mut v_a_9144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9147_: u8 = 0;
    let mut v___x_9149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9151_: u8 = 0;
    let mut v_vs_9152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9155_: usize = 0;
    let mut v___x_9156_: usize = 0;
    let mut v___x_9157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9161_: u8 = 0;
    let mut v_fst_9162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9172_: u8 = 0;
    let mut v_a_9173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9176_: u8 = 0;
    let mut v___x_9178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_9110_) == 0 {
                    v_cs_9123_ = lean_ctor_get(v_n_9110_, 0);
                    v___x_9124_ = lean_box(0);
                    v___x_9125_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9125_, 0, v___x_9124_);
                    lean_ctor_set(v___x_9125_, 1, v_b_9111_);
                    v_sz_9126_ = lean_array_size(v_cs_9123_);
                    v___x_9127_ = 0usize;
                    v___x_9128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_9108_, v_____s_9109_, v_cs_9123_, v_sz_9126_, v___x_9127_, v___x_9125_, v___y_9112_, v___y_9113_, v___y_9114_, v___y_9115_, v___y_9116_, v___y_9117_, v___y_9118_, v___y_9119_, v___y_9120_, v___y_9121_);
                    if lean_obj_tag(v___x_9128_) == 0 {
                        v_a_9129_ = lean_ctor_get(v___x_9128_, 0);
                        v_isSharedCheck_9143_ = (!lean_is_exclusive(v___x_9128_)) as u8;
                        if v_isSharedCheck_9143_ == 0 {
                            v___x_9131_ = v___x_9128_;
                            v_isShared_9132_ = v_isSharedCheck_9143_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9129_);
                            lean_dec(v___x_9128_);
                            v___x_9131_ = lean_box(0);
                            v_isShared_9132_ = v_isSharedCheck_9143_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_9144_ = lean_ctor_get(v___x_9128_, 0);
                        v_isSharedCheck_9151_ = (!lean_is_exclusive(v___x_9128_)) as u8;
                        if v_isSharedCheck_9151_ == 0 {
                            v___x_9146_ = v___x_9128_;
                            v_isShared_9147_ = v_isSharedCheck_9151_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_9144_);
                            lean_dec(v___x_9128_);
                            v___x_9146_ = lean_box(0);
                            v_isShared_9147_ = v_isSharedCheck_9151_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_9152_ = lean_ctor_get(v_n_9110_, 0);
                    v___x_9153_ = lean_box(0);
                    v___x_9154_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9154_, 0, v___x_9153_);
                    lean_ctor_set(v___x_9154_, 1, v_b_9111_);
                    v_sz_9155_ = lean_array_size(v_vs_9152_);
                    v___x_9156_ = 0usize;
                    v___x_9157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_9109_, v_vs_9152_, v_sz_9155_, v___x_9156_, v___x_9154_, v___y_9112_, v___y_9113_, v___y_9114_, v___y_9115_, v___y_9116_, v___y_9117_, v___y_9118_, v___y_9119_, v___y_9120_, v___y_9121_);
                    if lean_obj_tag(v___x_9157_) == 0 {
                        v_a_9158_ = lean_ctor_get(v___x_9157_, 0);
                        v_isSharedCheck_9172_ = (!lean_is_exclusive(v___x_9157_)) as u8;
                        if v_isSharedCheck_9172_ == 0 {
                            v___x_9160_ = v___x_9157_;
                            v_isShared_9161_ = v_isSharedCheck_9172_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_9158_);
                            lean_dec(v___x_9157_);
                            v___x_9160_ = lean_box(0);
                            v_isShared_9161_ = v_isSharedCheck_9172_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_9173_ = lean_ctor_get(v___x_9157_, 0);
                        v_isSharedCheck_9180_ = (!lean_is_exclusive(v___x_9157_)) as u8;
                        if v_isSharedCheck_9180_ == 0 {
                            v___x_9175_ = v___x_9157_;
                            v_isShared_9176_ = v_isSharedCheck_9180_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_9173_);
                            lean_dec(v___x_9157_);
                            v___x_9175_ = lean_box(0);
                            v_isShared_9176_ = v_isSharedCheck_9180_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_9133_ = lean_ctor_get(v_a_9129_, 0);
                if lean_obj_tag(v_fst_9133_) == 0 {
                    v_snd_9134_ = lean_ctor_get(v_a_9129_, 1);
                    lean_inc(v_snd_9134_);
                    lean_dec(v_a_9129_);
                    v___x_9135_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9135_, 0, v_snd_9134_);
                    if v_isShared_9132_ == 0 {
                        lean_ctor_set(v___x_9131_, 0, v___x_9135_);
                        v___x_9137_ = v___x_9131_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9138_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9138_, 0, v___x_9135_);
                        v___x_9137_ = v_reuseFailAlloc_9138_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_9133_);
                    lean_dec(v_a_9129_);
                    v_val_9139_ = lean_ctor_get(v_fst_9133_, 0);
                    lean_inc(v_val_9139_);
                    lean_dec_ref_known(v_fst_9133_, 1);
                    if v_isShared_9132_ == 0 {
                        lean_ctor_set(v___x_9131_, 0, v_val_9139_);
                        v___x_9141_ = v___x_9131_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9142_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9142_, 0, v_val_9139_);
                        v___x_9141_ = v_reuseFailAlloc_9142_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_9137_;
            }
            3 => {
                return v___x_9141_;
            }
            4 => {
                if v_isShared_9147_ == 0 {
                    v___x_9149_ = v___x_9146_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9150_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9150_, 0, v_a_9144_);
                    v___x_9149_ = v_reuseFailAlloc_9150_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9149_;
            }
            6 => {
                v_fst_9162_ = lean_ctor_get(v_a_9158_, 0);
                if lean_obj_tag(v_fst_9162_) == 0 {
                    v_snd_9163_ = lean_ctor_get(v_a_9158_, 1);
                    lean_inc(v_snd_9163_);
                    lean_dec(v_a_9158_);
                    v___x_9164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9164_, 0, v_snd_9163_);
                    if v_isShared_9161_ == 0 {
                        lean_ctor_set(v___x_9160_, 0, v___x_9164_);
                        v___x_9166_ = v___x_9160_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_9167_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9167_, 0, v___x_9164_);
                        v___x_9166_ = v_reuseFailAlloc_9167_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_9162_);
                    lean_dec(v_a_9158_);
                    v_val_9168_ = lean_ctor_get(v_fst_9162_, 0);
                    lean_inc(v_val_9168_);
                    lean_dec_ref_known(v_fst_9162_, 1);
                    if v_isShared_9161_ == 0 {
                        lean_ctor_set(v___x_9160_, 0, v_val_9168_);
                        v___x_9170_ = v___x_9160_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_9171_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9171_, 0, v_val_9168_);
                        v___x_9170_ = v_reuseFailAlloc_9171_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_9166_;
            }
            8 => {
                return v___x_9170_;
            }
            9 => {
                if v_isShared_9176_ == 0 {
                    v___x_9178_ = v___x_9175_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_9179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9179_, 0, v_a_9173_);
                    v___x_9178_ = v_reuseFailAlloc_9179_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_9178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(
    mut v_init_9181_: *mut LeanObject,
    mut v_____s_9182_: *mut LeanObject,
    mut v_as_9183_: *mut LeanObject,
    mut v_sz_9184_: usize,
    mut v_i_9185_: usize,
    mut v_b_9186_: *mut LeanObject,
    mut v___y_9187_: *mut LeanObject,
    mut v___y_9188_: *mut LeanObject,
    mut v___y_9189_: *mut LeanObject,
    mut v___y_9190_: *mut LeanObject,
    mut v___y_9191_: *mut LeanObject,
    mut v___y_9192_: *mut LeanObject,
    mut v___y_9193_: *mut LeanObject,
    mut v___y_9194_: *mut LeanObject,
    mut v___y_9195_: *mut LeanObject,
    mut v___y_9196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9198_: u8 = 0;
    let mut v___x_9199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9203_: u8 = 0;
    let mut v_a_9204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9209_: u8 = 0;
    let mut v___x_9210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9221_: usize = 0;
    let mut v___x_9222_: usize = 0;
    let mut v_reuseFailAlloc_9224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9225_: u8 = 0;
    let mut v_a_9226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9229_: u8 = 0;
    let mut v___x_9231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9233_: u8 = 0;
    let mut v_isSharedCheck_9234_: u8 = 0;
    let mut v_unused_9235_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9198_ = lean_usize_dec_lt(v_i_9185_, v_sz_9184_);
                if v___x_9198_ == 0 {
                    v___x_9199_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9199_, 0, v_b_9186_);
                    return v___x_9199_;
                } else {
                    v_snd_9200_ = lean_ctor_get(v_b_9186_, 1);
                    v_isSharedCheck_9234_ = (!lean_is_exclusive(v_b_9186_)) as u8;
                    if v_isSharedCheck_9234_ == 0 {
                        v_unused_9235_ = lean_ctor_get(v_b_9186_, 0);
                        lean_dec(v_unused_9235_);
                        v___x_9202_ = v_b_9186_;
                        v_isShared_9203_ = v_isSharedCheck_9234_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_9200_);
                        lean_dec(v_b_9186_);
                        v___x_9202_ = lean_box(0);
                        v_isShared_9203_ = v_isSharedCheck_9234_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_9204_ = lean_array_uget_borrowed(v_as_9183_, v_i_9185_);
                lean_inc(v_snd_9200_);
                v___x_9205_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_9181_, v_____s_9182_, v_a_9204_, v_snd_9200_, v___y_9187_, v___y_9188_, v___y_9189_, v___y_9190_, v___y_9191_, v___y_9192_, v___y_9193_, v___y_9194_, v___y_9195_, v___y_9196_);
                if lean_obj_tag(v___x_9205_) == 0 {
                    v_a_9206_ = lean_ctor_get(v___x_9205_, 0);
                    v_isSharedCheck_9225_ = (!lean_is_exclusive(v___x_9205_)) as u8;
                    if v_isSharedCheck_9225_ == 0 {
                        v___x_9208_ = v___x_9205_;
                        v_isShared_9209_ = v_isSharedCheck_9225_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_9206_);
                        lean_dec(v___x_9205_);
                        v___x_9208_ = lean_box(0);
                        v_isShared_9209_ = v_isSharedCheck_9225_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9202_);
                    lean_dec(v_snd_9200_);
                    v_a_9226_ = lean_ctor_get(v___x_9205_, 0);
                    v_isSharedCheck_9233_ = (!lean_is_exclusive(v___x_9205_)) as u8;
                    if v_isSharedCheck_9233_ == 0 {
                        v___x_9228_ = v___x_9205_;
                        v_isShared_9229_ = v_isSharedCheck_9233_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_9226_);
                        lean_dec(v___x_9205_);
                        v___x_9228_ = lean_box(0);
                        v_isShared_9229_ = v_isSharedCheck_9233_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_9206_) == 0 {
                    v___x_9210_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9210_, 0, v_a_9206_);
                    if v_isShared_9203_ == 0 {
                        lean_ctor_set(v___x_9202_, 0, v___x_9210_);
                        v___x_9212_ = v___x_9202_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9216_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9216_, 0, v___x_9210_);
                        lean_ctor_set(v_reuseFailAlloc_9216_, 1, v_snd_9200_);
                        v___x_9212_ = v_reuseFailAlloc_9216_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9208_);
                    lean_dec(v_snd_9200_);
                    v_a_9217_ = lean_ctor_get(v_a_9206_, 0);
                    lean_inc(v_a_9217_);
                    lean_dec_ref_known(v_a_9206_, 1);
                    v___x_9218_ = lean_box(0);
                    if v_isShared_9203_ == 0 {
                        lean_ctor_set(v___x_9202_, 1, v_a_9217_);
                        lean_ctor_set(v___x_9202_, 0, v___x_9218_);
                        v___x_9220_ = v___x_9202_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_9224_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9224_, 0, v___x_9218_);
                        lean_ctor_set(v_reuseFailAlloc_9224_, 1, v_a_9217_);
                        v___x_9220_ = v_reuseFailAlloc_9224_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_9209_ == 0 {
                    lean_ctor_set(v___x_9208_, 0, v___x_9212_);
                    v___x_9214_ = v___x_9208_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9215_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9215_, 0, v___x_9212_);
                    v___x_9214_ = v_reuseFailAlloc_9215_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9214_;
            }
            5 => {
                v___x_9221_ = 1usize;
                v___x_9222_ = lean_usize_add(v_i_9185_, v___x_9221_);
                v_i_9185_ = v___x_9222_;
                v_b_9186_ = v___x_9220_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_9229_ == 0 {
                    v___x_9231_ = v___x_9228_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9232_, 0, v_a_9226_);
                    v___x_9231_ = v_reuseFailAlloc_9232_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_9236_: *mut LeanObject = *_args.add(0);
    let mut v_____s_9237_: *mut LeanObject = *_args.add(1);
    let mut v_as_9238_: *mut LeanObject = *_args.add(2);
    let mut v_sz_9239_: *mut LeanObject = *_args.add(3);
    let mut v_i_9240_: *mut LeanObject = *_args.add(4);
    let mut v_b_9241_: *mut LeanObject = *_args.add(5);
    let mut v___y_9242_: *mut LeanObject = *_args.add(6);
    let mut v___y_9243_: *mut LeanObject = *_args.add(7);
    let mut v___y_9244_: *mut LeanObject = *_args.add(8);
    let mut v___y_9245_: *mut LeanObject = *_args.add(9);
    let mut v___y_9246_: *mut LeanObject = *_args.add(10);
    let mut v___y_9247_: *mut LeanObject = *_args.add(11);
    let mut v___y_9248_: *mut LeanObject = *_args.add(12);
    let mut v___y_9249_: *mut LeanObject = *_args.add(13);
    let mut v___y_9250_: *mut LeanObject = *_args.add(14);
    let mut v___y_9251_: *mut LeanObject = *_args.add(15);
    let mut v___y_9252_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_9253_: usize = 0;
    let mut v_i_boxed_9254_: usize = 0;
    let mut v_res_9255_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9253_ = lean_unbox_usize(v_sz_9239_);
    lean_dec(v_sz_9239_);
    v_i_boxed_9254_ = lean_unbox_usize(v_i_9240_);
    lean_dec(v_i_9240_);
    v_res_9255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_9236_, v_____s_9237_, v_as_9238_, v_sz_boxed_9253_, v_i_boxed_9254_, v_b_9241_, v___y_9242_, v___y_9243_, v___y_9244_, v___y_9245_, v___y_9246_, v___y_9247_, v___y_9248_, v___y_9249_, v___y_9250_, v___y_9251_);
    lean_dec(v___y_9251_);
    lean_dec_ref(v___y_9250_);
    lean_dec(v___y_9249_);
    lean_dec_ref(v___y_9248_);
    lean_dec(v___y_9247_);
    lean_dec_ref(v___y_9246_);
    lean_dec(v___y_9245_);
    lean_dec_ref(v___y_9244_);
    lean_dec(v___y_9243_);
    lean_dec(v___y_9242_);
    lean_dec_ref(v_as_9238_);
    lean_dec(v_____s_9237_);
    return v_res_9255_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0___boxed(
    mut v_init_9256_: *mut LeanObject,
    mut v_____s_9257_: *mut LeanObject,
    mut v_n_9258_: *mut LeanObject,
    mut v_b_9259_: *mut LeanObject,
    mut v___y_9260_: *mut LeanObject,
    mut v___y_9261_: *mut LeanObject,
    mut v___y_9262_: *mut LeanObject,
    mut v___y_9263_: *mut LeanObject,
    mut v___y_9264_: *mut LeanObject,
    mut v___y_9265_: *mut LeanObject,
    mut v___y_9266_: *mut LeanObject,
    mut v___y_9267_: *mut LeanObject,
    mut v___y_9268_: *mut LeanObject,
    mut v___y_9269_: *mut LeanObject,
    mut v___y_9270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9271_: *mut LeanObject = core::ptr::null_mut();
    v_res_9271_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_9256_, v_____s_9257_, v_n_9258_, v_b_9259_, v___y_9260_, v___y_9261_, v___y_9262_, v___y_9263_, v___y_9264_, v___y_9265_, v___y_9266_, v___y_9267_, v___y_9268_, v___y_9269_);
    lean_dec(v___y_9269_);
    lean_dec_ref(v___y_9268_);
    lean_dec(v___y_9267_);
    lean_dec_ref(v___y_9266_);
    lean_dec(v___y_9265_);
    lean_dec_ref(v___y_9264_);
    lean_dec(v___y_9263_);
    lean_dec_ref(v___y_9262_);
    lean_dec(v___y_9261_);
    lean_dec(v___y_9260_);
    lean_dec_ref(v_n_9258_);
    lean_dec(v_____s_9257_);
    return v_res_9271_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(
    mut v_____s_9272_: *mut LeanObject,
    mut v_t_9273_: *mut LeanObject,
    mut v_init_9274_: *mut LeanObject,
    mut v___y_9275_: *mut LeanObject,
    mut v___y_9276_: *mut LeanObject,
    mut v___y_9277_: *mut LeanObject,
    mut v___y_9278_: *mut LeanObject,
    mut v___y_9279_: *mut LeanObject,
    mut v___y_9280_: *mut LeanObject,
    mut v___y_9281_: *mut LeanObject,
    mut v___y_9282_: *mut LeanObject,
    mut v___y_9283_: *mut LeanObject,
    mut v___y_9284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_9286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_9287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9292_: u8 = 0;
    let mut v_a_9293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9300_: usize = 0;
    let mut v___x_9301_: usize = 0;
    let mut v___x_9302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9306_: u8 = 0;
    let mut v_fst_9307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9316_: u8 = 0;
    let mut v_a_9317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9320_: u8 = 0;
    let mut v___x_9322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9324_: u8 = 0;
    let mut v_isSharedCheck_9325_: u8 = 0;
    let mut v_a_9326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9329_: u8 = 0;
    let mut v___x_9331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_9286_ = lean_ctor_get(v_t_9273_, 0);
                v_tail_9287_ = lean_ctor_get(v_t_9273_, 1);
                v___x_9288_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__0(v_init_9274_, v_____s_9272_, v_root_9286_, v_init_9274_, v___y_9275_, v___y_9276_, v___y_9277_, v___y_9278_, v___y_9279_, v___y_9280_, v___y_9281_, v___y_9282_, v___y_9283_, v___y_9284_);
                if lean_obj_tag(v___x_9288_) == 0 {
                    v_a_9289_ = lean_ctor_get(v___x_9288_, 0);
                    v_isSharedCheck_9325_ = (!lean_is_exclusive(v___x_9288_)) as u8;
                    if v_isSharedCheck_9325_ == 0 {
                        v___x_9291_ = v___x_9288_;
                        v_isShared_9292_ = v_isSharedCheck_9325_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9289_);
                        lean_dec(v___x_9288_);
                        v___x_9291_ = lean_box(0);
                        v_isShared_9292_ = v_isSharedCheck_9325_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9326_ = lean_ctor_get(v___x_9288_, 0);
                    v_isSharedCheck_9333_ = (!lean_is_exclusive(v___x_9288_)) as u8;
                    if v_isSharedCheck_9333_ == 0 {
                        v___x_9328_ = v___x_9288_;
                        v_isShared_9329_ = v_isSharedCheck_9333_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_9326_);
                        lean_dec(v___x_9288_);
                        v___x_9328_ = lean_box(0);
                        v_isShared_9329_ = v_isSharedCheck_9333_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_9289_) == 0 {
                    v_a_9293_ = lean_ctor_get(v_a_9289_, 0);
                    lean_inc(v_a_9293_);
                    lean_dec_ref_known(v_a_9289_, 1);
                    if v_isShared_9292_ == 0 {
                        lean_ctor_set(v___x_9291_, 0, v_a_9293_);
                        v___x_9295_ = v___x_9291_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9296_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9296_, 0, v_a_9293_);
                        v___x_9295_ = v_reuseFailAlloc_9296_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9291_);
                    v_a_9297_ = lean_ctor_get(v_a_9289_, 0);
                    lean_inc(v_a_9297_);
                    lean_dec_ref_known(v_a_9289_, 1);
                    v___x_9298_ = lean_box(0);
                    v___x_9299_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9299_, 0, v___x_9298_);
                    lean_ctor_set(v___x_9299_, 1, v_a_9297_);
                    v_sz_9300_ = lean_array_size(v_tail_9287_);
                    v___x_9301_ = 0usize;
                    v___x_9302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0_spec__1(v_____s_9272_, v_tail_9287_, v_sz_9300_, v___x_9301_, v___x_9299_, v___y_9275_, v___y_9276_, v___y_9277_, v___y_9278_, v___y_9279_, v___y_9280_, v___y_9281_, v___y_9282_, v___y_9283_, v___y_9284_);
                    if lean_obj_tag(v___x_9302_) == 0 {
                        v_a_9303_ = lean_ctor_get(v___x_9302_, 0);
                        v_isSharedCheck_9316_ = (!lean_is_exclusive(v___x_9302_)) as u8;
                        if v_isSharedCheck_9316_ == 0 {
                            v___x_9305_ = v___x_9302_;
                            v_isShared_9306_ = v_isSharedCheck_9316_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_9303_);
                            lean_dec(v___x_9302_);
                            v___x_9305_ = lean_box(0);
                            v_isShared_9306_ = v_isSharedCheck_9316_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_9317_ = lean_ctor_get(v___x_9302_, 0);
                        v_isSharedCheck_9324_ = (!lean_is_exclusive(v___x_9302_)) as u8;
                        if v_isSharedCheck_9324_ == 0 {
                            v___x_9319_ = v___x_9302_;
                            v_isShared_9320_ = v_isSharedCheck_9324_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_9317_);
                            lean_dec(v___x_9302_);
                            v___x_9319_ = lean_box(0);
                            v_isShared_9320_ = v_isSharedCheck_9324_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_9295_;
            }
            3 => {
                v_fst_9307_ = lean_ctor_get(v_a_9303_, 0);
                if lean_obj_tag(v_fst_9307_) == 0 {
                    v_snd_9308_ = lean_ctor_get(v_a_9303_, 1);
                    lean_inc(v_snd_9308_);
                    lean_dec(v_a_9303_);
                    if v_isShared_9306_ == 0 {
                        lean_ctor_set(v___x_9305_, 0, v_snd_9308_);
                        v___x_9310_ = v___x_9305_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_9311_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9311_, 0, v_snd_9308_);
                        v___x_9310_ = v_reuseFailAlloc_9311_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_9307_);
                    lean_dec(v_a_9303_);
                    v_val_9312_ = lean_ctor_get(v_fst_9307_, 0);
                    lean_inc(v_val_9312_);
                    lean_dec_ref_known(v_fst_9307_, 1);
                    if v_isShared_9306_ == 0 {
                        lean_ctor_set(v___x_9305_, 0, v_val_9312_);
                        v___x_9314_ = v___x_9305_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_9315_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9315_, 0, v_val_9312_);
                        v___x_9314_ = v_reuseFailAlloc_9315_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_9310_;
            }
            5 => {
                return v___x_9314_;
            }
            6 => {
                if v_isShared_9320_ == 0 {
                    v___x_9322_ = v___x_9319_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9323_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9323_, 0, v_a_9317_);
                    v___x_9322_ = v_reuseFailAlloc_9323_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9322_;
            }
            8 => {
                if v_isShared_9329_ == 0 {
                    v___x_9331_ = v___x_9328_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_9332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9332_, 0, v_a_9326_);
                    v___x_9331_ = v_reuseFailAlloc_9332_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_9331_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0___boxed(
    mut v_____s_9334_: *mut LeanObject,
    mut v_t_9335_: *mut LeanObject,
    mut v_init_9336_: *mut LeanObject,
    mut v___y_9337_: *mut LeanObject,
    mut v___y_9338_: *mut LeanObject,
    mut v___y_9339_: *mut LeanObject,
    mut v___y_9340_: *mut LeanObject,
    mut v___y_9341_: *mut LeanObject,
    mut v___y_9342_: *mut LeanObject,
    mut v___y_9343_: *mut LeanObject,
    mut v___y_9344_: *mut LeanObject,
    mut v___y_9345_: *mut LeanObject,
    mut v___y_9346_: *mut LeanObject,
    mut v___y_9347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9348_: *mut LeanObject = core::ptr::null_mut();
    v_res_9348_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(
            v_____s_9334_,
            v_t_9335_,
            v_init_9336_,
            v___y_9337_,
            v___y_9338_,
            v___y_9339_,
            v___y_9340_,
            v___y_9341_,
            v___y_9342_,
            v___y_9343_,
            v___y_9344_,
            v___y_9345_,
            v___y_9346_,
        );
    lean_dec(v___y_9346_);
    lean_dec_ref(v___y_9345_);
    lean_dec(v___y_9344_);
    lean_dec_ref(v___y_9343_);
    lean_dec(v___y_9342_);
    lean_dec_ref(v___y_9341_);
    lean_dec(v___y_9340_);
    lean_dec_ref(v___y_9339_);
    lean_dec(v___y_9338_);
    lean_dec(v___y_9337_);
    lean_dec_ref(v_t_9335_);
    lean_dec(v_____s_9334_);
    return v_res_9348_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(
    mut v_as_9349_: *mut LeanObject,
    mut v_sz_9350_: usize,
    mut v_i_9351_: usize,
    mut v_b_9352_: *mut LeanObject,
    mut v___y_9353_: *mut LeanObject,
    mut v___y_9354_: *mut LeanObject,
    mut v___y_9355_: *mut LeanObject,
    mut v___y_9356_: *mut LeanObject,
    mut v___y_9357_: *mut LeanObject,
    mut v___y_9358_: *mut LeanObject,
    mut v___y_9359_: *mut LeanObject,
    mut v___y_9360_: *mut LeanObject,
    mut v___y_9361_: *mut LeanObject,
    mut v___y_9362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9364_: u8 = 0;
    let mut v___x_9365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9369_: u8 = 0;
    let mut v_a_9370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9378_: usize = 0;
    let mut v___x_9379_: usize = 0;
    let mut v_reuseFailAlloc_9381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9385_: u8 = 0;
    let mut v___x_9387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9389_: u8 = 0;
    let mut v_isSharedCheck_9390_: u8 = 0;
    let mut v_unused_9391_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9364_ = lean_usize_dec_lt(v_i_9351_, v_sz_9350_);
                if v___x_9364_ == 0 {
                    v___x_9365_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9365_, 0, v_b_9352_);
                    return v___x_9365_;
                } else {
                    v_snd_9366_ = lean_ctor_get(v_b_9352_, 1);
                    v_isSharedCheck_9390_ = (!lean_is_exclusive(v_b_9352_)) as u8;
                    if v_isSharedCheck_9390_ == 0 {
                        v_unused_9391_ = lean_ctor_get(v_b_9352_, 0);
                        lean_dec(v_unused_9391_);
                        v___x_9368_ = v_b_9352_;
                        v_isShared_9369_ = v_isSharedCheck_9390_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_9366_);
                        lean_dec(v_b_9352_);
                        v___x_9368_ = lean_box(0);
                        v_isShared_9369_ = v_isSharedCheck_9390_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_9370_ = lean_array_uget_borrowed(v_as_9349_, v_i_9351_);
                v___x_9371_ = lean_box(0);
                v___x_9372_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_9366_, v_a_9370_, v___x_9371_, v___y_9353_, v___y_9354_, v___y_9355_, v___y_9356_, v___y_9357_, v___y_9358_, v___y_9359_, v___y_9360_, v___y_9361_, v___y_9362_);
                if lean_obj_tag(v___x_9372_) == 0 {
                    lean_dec_ref_known(v___x_9372_, 1);
                    v___x_9373_ = lean_box(0);
                    v___x_9374_ = lean_unsigned_to_nat(1);
                    v___x_9375_ = lean_nat_add(v_snd_9366_, v___x_9374_);
                    lean_dec(v_snd_9366_);
                    if v_isShared_9369_ == 0 {
                        lean_ctor_set(v___x_9368_, 1, v___x_9375_);
                        lean_ctor_set(v___x_9368_, 0, v___x_9373_);
                        v___x_9377_ = v___x_9368_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9381_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9381_, 0, v___x_9373_);
                        lean_ctor_set(v_reuseFailAlloc_9381_, 1, v___x_9375_);
                        v___x_9377_ = v_reuseFailAlloc_9381_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9368_);
                    lean_dec(v_snd_9366_);
                    v_a_9382_ = lean_ctor_get(v___x_9372_, 0);
                    v_isSharedCheck_9389_ = (!lean_is_exclusive(v___x_9372_)) as u8;
                    if v_isSharedCheck_9389_ == 0 {
                        v___x_9384_ = v___x_9372_;
                        v_isShared_9385_ = v_isSharedCheck_9389_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9382_);
                        lean_dec(v___x_9372_);
                        v___x_9384_ = lean_box(0);
                        v_isShared_9385_ = v_isSharedCheck_9389_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9378_ = 1usize;
                v___x_9379_ = lean_usize_add(v_i_9351_, v___x_9378_);
                v_i_9351_ = v___x_9379_;
                v_b_9352_ = v___x_9377_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_9385_ == 0 {
                    v___x_9387_ = v___x_9384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9388_, 0, v_a_9382_);
                    v___x_9387_ = v_reuseFailAlloc_9388_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(
    mut v_as_9392_: *mut LeanObject,
    mut v_sz_9393_: *mut LeanObject,
    mut v_i_9394_: *mut LeanObject,
    mut v_b_9395_: *mut LeanObject,
    mut v___y_9396_: *mut LeanObject,
    mut v___y_9397_: *mut LeanObject,
    mut v___y_9398_: *mut LeanObject,
    mut v___y_9399_: *mut LeanObject,
    mut v___y_9400_: *mut LeanObject,
    mut v___y_9401_: *mut LeanObject,
    mut v___y_9402_: *mut LeanObject,
    mut v___y_9403_: *mut LeanObject,
    mut v___y_9404_: *mut LeanObject,
    mut v___y_9405_: *mut LeanObject,
    mut v___y_9406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9407_: usize = 0;
    let mut v_i_boxed_9408_: usize = 0;
    let mut v_res_9409_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9407_ = lean_unbox_usize(v_sz_9393_);
    lean_dec(v_sz_9393_);
    v_i_boxed_9408_ = lean_unbox_usize(v_i_9394_);
    lean_dec(v_i_9394_);
    v_res_9409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_9392_, v_sz_boxed_9407_, v_i_boxed_9408_, v_b_9395_, v___y_9396_, v___y_9397_, v___y_9398_, v___y_9399_, v___y_9400_, v___y_9401_, v___y_9402_, v___y_9403_, v___y_9404_, v___y_9405_);
    lean_dec(v___y_9405_);
    lean_dec_ref(v___y_9404_);
    lean_dec(v___y_9403_);
    lean_dec_ref(v___y_9402_);
    lean_dec(v___y_9401_);
    lean_dec_ref(v___y_9400_);
    lean_dec(v___y_9399_);
    lean_dec_ref(v___y_9398_);
    lean_dec(v___y_9397_);
    lean_dec(v___y_9396_);
    lean_dec_ref(v_as_9392_);
    return v_res_9409_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(
    mut v_as_9410_: *mut LeanObject,
    mut v_sz_9411_: usize,
    mut v_i_9412_: usize,
    mut v_b_9413_: *mut LeanObject,
    mut v___y_9414_: *mut LeanObject,
    mut v___y_9415_: *mut LeanObject,
    mut v___y_9416_: *mut LeanObject,
    mut v___y_9417_: *mut LeanObject,
    mut v___y_9418_: *mut LeanObject,
    mut v___y_9419_: *mut LeanObject,
    mut v___y_9420_: *mut LeanObject,
    mut v___y_9421_: *mut LeanObject,
    mut v___y_9422_: *mut LeanObject,
    mut v___y_9423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9425_: u8 = 0;
    let mut v___x_9426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9430_: u8 = 0;
    let mut v_a_9431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9439_: usize = 0;
    let mut v___x_9440_: usize = 0;
    let mut v___x_9441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9446_: u8 = 0;
    let mut v___x_9448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9450_: u8 = 0;
    let mut v_isSharedCheck_9451_: u8 = 0;
    let mut v_unused_9452_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9425_ = lean_usize_dec_lt(v_i_9412_, v_sz_9411_);
                if v___x_9425_ == 0 {
                    v___x_9426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9426_, 0, v_b_9413_);
                    return v___x_9426_;
                } else {
                    v_snd_9427_ = lean_ctor_get(v_b_9413_, 1);
                    v_isSharedCheck_9451_ = (!lean_is_exclusive(v_b_9413_)) as u8;
                    if v_isSharedCheck_9451_ == 0 {
                        v_unused_9452_ = lean_ctor_get(v_b_9413_, 0);
                        lean_dec(v_unused_9452_);
                        v___x_9429_ = v_b_9413_;
                        v_isShared_9430_ = v_isSharedCheck_9451_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_9427_);
                        lean_dec(v_b_9413_);
                        v___x_9429_ = lean_box(0);
                        v_isShared_9430_ = v_isSharedCheck_9451_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_9431_ = lean_array_uget_borrowed(v_as_9410_, v_i_9412_);
                v___x_9432_ = lean_box(0);
                v___x_9433_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_9427_, v_a_9431_, v___x_9432_, v___y_9414_, v___y_9415_, v___y_9416_, v___y_9417_, v___y_9418_, v___y_9419_, v___y_9420_, v___y_9421_, v___y_9422_, v___y_9423_);
                if lean_obj_tag(v___x_9433_) == 0 {
                    lean_dec_ref_known(v___x_9433_, 1);
                    v___x_9434_ = lean_box(0);
                    v___x_9435_ = lean_unsigned_to_nat(1);
                    v___x_9436_ = lean_nat_add(v_snd_9427_, v___x_9435_);
                    lean_dec(v_snd_9427_);
                    if v_isShared_9430_ == 0 {
                        lean_ctor_set(v___x_9429_, 1, v___x_9436_);
                        lean_ctor_set(v___x_9429_, 0, v___x_9434_);
                        v___x_9438_ = v___x_9429_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9442_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9442_, 0, v___x_9434_);
                        lean_ctor_set(v_reuseFailAlloc_9442_, 1, v___x_9436_);
                        v___x_9438_ = v_reuseFailAlloc_9442_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9429_);
                    lean_dec(v_snd_9427_);
                    v_a_9443_ = lean_ctor_get(v___x_9433_, 0);
                    v_isSharedCheck_9450_ = (!lean_is_exclusive(v___x_9433_)) as u8;
                    if v_isSharedCheck_9450_ == 0 {
                        v___x_9445_ = v___x_9433_;
                        v_isShared_9446_ = v_isSharedCheck_9450_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9443_);
                        lean_dec(v___x_9433_);
                        v___x_9445_ = lean_box(0);
                        v_isShared_9446_ = v_isSharedCheck_9450_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9439_ = 1usize;
                v___x_9440_ = lean_usize_add(v_i_9412_, v___x_9439_);
                v___x_9441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_9410_, v_sz_9411_, v___x_9440_, v___x_9438_, v___y_9414_, v___y_9415_, v___y_9416_, v___y_9417_, v___y_9418_, v___y_9419_, v___y_9420_, v___y_9421_, v___y_9422_, v___y_9423_);
                return v___x_9441_;
            }
            3 => {
                if v_isShared_9446_ == 0 {
                    v___x_9448_ = v___x_9445_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9449_, 0, v_a_9443_);
                    v___x_9448_ = v_reuseFailAlloc_9449_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(
    mut v_as_9453_: *mut LeanObject,
    mut v_sz_9454_: *mut LeanObject,
    mut v_i_9455_: *mut LeanObject,
    mut v_b_9456_: *mut LeanObject,
    mut v___y_9457_: *mut LeanObject,
    mut v___y_9458_: *mut LeanObject,
    mut v___y_9459_: *mut LeanObject,
    mut v___y_9460_: *mut LeanObject,
    mut v___y_9461_: *mut LeanObject,
    mut v___y_9462_: *mut LeanObject,
    mut v___y_9463_: *mut LeanObject,
    mut v___y_9464_: *mut LeanObject,
    mut v___y_9465_: *mut LeanObject,
    mut v___y_9466_: *mut LeanObject,
    mut v___y_9467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9468_: usize = 0;
    let mut v_i_boxed_9469_: usize = 0;
    let mut v_res_9470_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9468_ = lean_unbox_usize(v_sz_9454_);
    lean_dec(v_sz_9454_);
    v_i_boxed_9469_ = lean_unbox_usize(v_i_9455_);
    lean_dec(v_i_9455_);
    v_res_9470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_9453_, v_sz_boxed_9468_, v_i_boxed_9469_, v_b_9456_, v___y_9457_, v___y_9458_, v___y_9459_, v___y_9460_, v___y_9461_, v___y_9462_, v___y_9463_, v___y_9464_, v___y_9465_, v___y_9466_);
    lean_dec(v___y_9466_);
    lean_dec_ref(v___y_9465_);
    lean_dec(v___y_9464_);
    lean_dec_ref(v___y_9463_);
    lean_dec(v___y_9462_);
    lean_dec_ref(v___y_9461_);
    lean_dec(v___y_9460_);
    lean_dec_ref(v___y_9459_);
    lean_dec(v___y_9458_);
    lean_dec(v___y_9457_);
    lean_dec_ref(v_as_9453_);
    return v_res_9470_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(
    mut v_init_9471_: *mut LeanObject,
    mut v_n_9472_: *mut LeanObject,
    mut v_b_9473_: *mut LeanObject,
    mut v___y_9474_: *mut LeanObject,
    mut v___y_9475_: *mut LeanObject,
    mut v___y_9476_: *mut LeanObject,
    mut v___y_9477_: *mut LeanObject,
    mut v___y_9478_: *mut LeanObject,
    mut v___y_9479_: *mut LeanObject,
    mut v___y_9480_: *mut LeanObject,
    mut v___y_9481_: *mut LeanObject,
    mut v___y_9482_: *mut LeanObject,
    mut v___y_9483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_9485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9488_: usize = 0;
    let mut v___x_9489_: usize = 0;
    let mut v___x_9490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9494_: u8 = 0;
    let mut v_fst_9495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9505_: u8 = 0;
    let mut v_a_9506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9509_: u8 = 0;
    let mut v___x_9511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9513_: u8 = 0;
    let mut v_vs_9514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9517_: usize = 0;
    let mut v___x_9518_: usize = 0;
    let mut v___x_9519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9523_: u8 = 0;
    let mut v_fst_9524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9534_: u8 = 0;
    let mut v_a_9535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9538_: u8 = 0;
    let mut v___x_9540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_9472_) == 0 {
                    v_cs_9485_ = lean_ctor_get(v_n_9472_, 0);
                    v___x_9486_ = lean_box(0);
                    v___x_9487_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9487_, 0, v___x_9486_);
                    lean_ctor_set(v___x_9487_, 1, v_b_9473_);
                    v_sz_9488_ = lean_array_size(v_cs_9485_);
                    v___x_9489_ = 0usize;
                    v___x_9490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_9471_, v_cs_9485_, v_sz_9488_, v___x_9489_, v___x_9487_, v___y_9474_, v___y_9475_, v___y_9476_, v___y_9477_, v___y_9478_, v___y_9479_, v___y_9480_, v___y_9481_, v___y_9482_, v___y_9483_);
                    if lean_obj_tag(v___x_9490_) == 0 {
                        v_a_9491_ = lean_ctor_get(v___x_9490_, 0);
                        v_isSharedCheck_9505_ = (!lean_is_exclusive(v___x_9490_)) as u8;
                        if v_isSharedCheck_9505_ == 0 {
                            v___x_9493_ = v___x_9490_;
                            v_isShared_9494_ = v_isSharedCheck_9505_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9491_);
                            lean_dec(v___x_9490_);
                            v___x_9493_ = lean_box(0);
                            v_isShared_9494_ = v_isSharedCheck_9505_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_9506_ = lean_ctor_get(v___x_9490_, 0);
                        v_isSharedCheck_9513_ = (!lean_is_exclusive(v___x_9490_)) as u8;
                        if v_isSharedCheck_9513_ == 0 {
                            v___x_9508_ = v___x_9490_;
                            v_isShared_9509_ = v_isSharedCheck_9513_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_9506_);
                            lean_dec(v___x_9490_);
                            v___x_9508_ = lean_box(0);
                            v_isShared_9509_ = v_isSharedCheck_9513_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_9514_ = lean_ctor_get(v_n_9472_, 0);
                    v___x_9515_ = lean_box(0);
                    v___x_9516_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9516_, 0, v___x_9515_);
                    lean_ctor_set(v___x_9516_, 1, v_b_9473_);
                    v_sz_9517_ = lean_array_size(v_vs_9514_);
                    v___x_9518_ = 0usize;
                    v___x_9519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_9514_, v_sz_9517_, v___x_9518_, v___x_9516_, v___y_9474_, v___y_9475_, v___y_9476_, v___y_9477_, v___y_9478_, v___y_9479_, v___y_9480_, v___y_9481_, v___y_9482_, v___y_9483_);
                    if lean_obj_tag(v___x_9519_) == 0 {
                        v_a_9520_ = lean_ctor_get(v___x_9519_, 0);
                        v_isSharedCheck_9534_ = (!lean_is_exclusive(v___x_9519_)) as u8;
                        if v_isSharedCheck_9534_ == 0 {
                            v___x_9522_ = v___x_9519_;
                            v_isShared_9523_ = v_isSharedCheck_9534_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_9520_);
                            lean_dec(v___x_9519_);
                            v___x_9522_ = lean_box(0);
                            v_isShared_9523_ = v_isSharedCheck_9534_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_9535_ = lean_ctor_get(v___x_9519_, 0);
                        v_isSharedCheck_9542_ = (!lean_is_exclusive(v___x_9519_)) as u8;
                        if v_isSharedCheck_9542_ == 0 {
                            v___x_9537_ = v___x_9519_;
                            v_isShared_9538_ = v_isSharedCheck_9542_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_9535_);
                            lean_dec(v___x_9519_);
                            v___x_9537_ = lean_box(0);
                            v_isShared_9538_ = v_isSharedCheck_9542_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_9495_ = lean_ctor_get(v_a_9491_, 0);
                if lean_obj_tag(v_fst_9495_) == 0 {
                    v_snd_9496_ = lean_ctor_get(v_a_9491_, 1);
                    lean_inc(v_snd_9496_);
                    lean_dec(v_a_9491_);
                    v___x_9497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9497_, 0, v_snd_9496_);
                    if v_isShared_9494_ == 0 {
                        lean_ctor_set(v___x_9493_, 0, v___x_9497_);
                        v___x_9499_ = v___x_9493_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9500_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9500_, 0, v___x_9497_);
                        v___x_9499_ = v_reuseFailAlloc_9500_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_9495_);
                    lean_dec(v_a_9491_);
                    v_val_9501_ = lean_ctor_get(v_fst_9495_, 0);
                    lean_inc(v_val_9501_);
                    lean_dec_ref_known(v_fst_9495_, 1);
                    if v_isShared_9494_ == 0 {
                        lean_ctor_set(v___x_9493_, 0, v_val_9501_);
                        v___x_9503_ = v___x_9493_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9504_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9504_, 0, v_val_9501_);
                        v___x_9503_ = v_reuseFailAlloc_9504_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_9499_;
            }
            3 => {
                return v___x_9503_;
            }
            4 => {
                if v_isShared_9509_ == 0 {
                    v___x_9511_ = v___x_9508_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9512_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9512_, 0, v_a_9506_);
                    v___x_9511_ = v_reuseFailAlloc_9512_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9511_;
            }
            6 => {
                v_fst_9524_ = lean_ctor_get(v_a_9520_, 0);
                if lean_obj_tag(v_fst_9524_) == 0 {
                    v_snd_9525_ = lean_ctor_get(v_a_9520_, 1);
                    lean_inc(v_snd_9525_);
                    lean_dec(v_a_9520_);
                    v___x_9526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9526_, 0, v_snd_9525_);
                    if v_isShared_9523_ == 0 {
                        lean_ctor_set(v___x_9522_, 0, v___x_9526_);
                        v___x_9528_ = v___x_9522_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_9529_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9529_, 0, v___x_9526_);
                        v___x_9528_ = v_reuseFailAlloc_9529_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_9524_);
                    lean_dec(v_a_9520_);
                    v_val_9530_ = lean_ctor_get(v_fst_9524_, 0);
                    lean_inc(v_val_9530_);
                    lean_dec_ref_known(v_fst_9524_, 1);
                    if v_isShared_9523_ == 0 {
                        lean_ctor_set(v___x_9522_, 0, v_val_9530_);
                        v___x_9532_ = v___x_9522_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_9533_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9533_, 0, v_val_9530_);
                        v___x_9532_ = v_reuseFailAlloc_9533_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_9528_;
            }
            8 => {
                return v___x_9532_;
            }
            9 => {
                if v_isShared_9538_ == 0 {
                    v___x_9540_ = v___x_9537_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_9541_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9541_, 0, v_a_9535_);
                    v___x_9540_ = v_reuseFailAlloc_9541_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_9540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(
    mut v_init_9543_: *mut LeanObject,
    mut v_as_9544_: *mut LeanObject,
    mut v_sz_9545_: usize,
    mut v_i_9546_: usize,
    mut v_b_9547_: *mut LeanObject,
    mut v___y_9548_: *mut LeanObject,
    mut v___y_9549_: *mut LeanObject,
    mut v___y_9550_: *mut LeanObject,
    mut v___y_9551_: *mut LeanObject,
    mut v___y_9552_: *mut LeanObject,
    mut v___y_9553_: *mut LeanObject,
    mut v___y_9554_: *mut LeanObject,
    mut v___y_9555_: *mut LeanObject,
    mut v___y_9556_: *mut LeanObject,
    mut v___y_9557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9559_: u8 = 0;
    let mut v___x_9560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9564_: u8 = 0;
    let mut v_a_9565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9570_: u8 = 0;
    let mut v___x_9571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9582_: usize = 0;
    let mut v___x_9583_: usize = 0;
    let mut v_reuseFailAlloc_9585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9586_: u8 = 0;
    let mut v_a_9587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9590_: u8 = 0;
    let mut v___x_9592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9594_: u8 = 0;
    let mut v_isSharedCheck_9595_: u8 = 0;
    let mut v_unused_9596_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9559_ = lean_usize_dec_lt(v_i_9546_, v_sz_9545_);
                if v___x_9559_ == 0 {
                    v___x_9560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9560_, 0, v_b_9547_);
                    return v___x_9560_;
                } else {
                    v_snd_9561_ = lean_ctor_get(v_b_9547_, 1);
                    v_isSharedCheck_9595_ = (!lean_is_exclusive(v_b_9547_)) as u8;
                    if v_isSharedCheck_9595_ == 0 {
                        v_unused_9596_ = lean_ctor_get(v_b_9547_, 0);
                        lean_dec(v_unused_9596_);
                        v___x_9563_ = v_b_9547_;
                        v_isShared_9564_ = v_isSharedCheck_9595_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_9561_);
                        lean_dec(v_b_9547_);
                        v___x_9563_ = lean_box(0);
                        v_isShared_9564_ = v_isSharedCheck_9595_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_9565_ = lean_array_uget_borrowed(v_as_9544_, v_i_9546_);
                lean_inc(v_snd_9561_);
                v___x_9566_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_9543_, v_a_9565_, v_snd_9561_, v___y_9548_, v___y_9549_, v___y_9550_, v___y_9551_, v___y_9552_, v___y_9553_, v___y_9554_, v___y_9555_, v___y_9556_, v___y_9557_);
                if lean_obj_tag(v___x_9566_) == 0 {
                    v_a_9567_ = lean_ctor_get(v___x_9566_, 0);
                    v_isSharedCheck_9586_ = (!lean_is_exclusive(v___x_9566_)) as u8;
                    if v_isSharedCheck_9586_ == 0 {
                        v___x_9569_ = v___x_9566_;
                        v_isShared_9570_ = v_isSharedCheck_9586_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_9567_);
                        lean_dec(v___x_9566_);
                        v___x_9569_ = lean_box(0);
                        v_isShared_9570_ = v_isSharedCheck_9586_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9563_);
                    lean_dec(v_snd_9561_);
                    v_a_9587_ = lean_ctor_get(v___x_9566_, 0);
                    v_isSharedCheck_9594_ = (!lean_is_exclusive(v___x_9566_)) as u8;
                    if v_isSharedCheck_9594_ == 0 {
                        v___x_9589_ = v___x_9566_;
                        v_isShared_9590_ = v_isSharedCheck_9594_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_9587_);
                        lean_dec(v___x_9566_);
                        v___x_9589_ = lean_box(0);
                        v_isShared_9590_ = v_isSharedCheck_9594_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_9567_) == 0 {
                    v___x_9571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9571_, 0, v_a_9567_);
                    if v_isShared_9564_ == 0 {
                        lean_ctor_set(v___x_9563_, 0, v___x_9571_);
                        v___x_9573_ = v___x_9563_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9577_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9577_, 0, v___x_9571_);
                        lean_ctor_set(v_reuseFailAlloc_9577_, 1, v_snd_9561_);
                        v___x_9573_ = v_reuseFailAlloc_9577_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9569_);
                    lean_dec(v_snd_9561_);
                    v_a_9578_ = lean_ctor_get(v_a_9567_, 0);
                    lean_inc(v_a_9578_);
                    lean_dec_ref_known(v_a_9567_, 1);
                    v___x_9579_ = lean_box(0);
                    if v_isShared_9564_ == 0 {
                        lean_ctor_set(v___x_9563_, 1, v_a_9578_);
                        lean_ctor_set(v___x_9563_, 0, v___x_9579_);
                        v___x_9581_ = v___x_9563_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_9585_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9585_, 0, v___x_9579_);
                        lean_ctor_set(v_reuseFailAlloc_9585_, 1, v_a_9578_);
                        v___x_9581_ = v_reuseFailAlloc_9585_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_9570_ == 0 {
                    lean_ctor_set(v___x_9569_, 0, v___x_9573_);
                    v___x_9575_ = v___x_9569_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9576_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9576_, 0, v___x_9573_);
                    v___x_9575_ = v_reuseFailAlloc_9576_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9575_;
            }
            5 => {
                v___x_9582_ = 1usize;
                v___x_9583_ = lean_usize_add(v_i_9546_, v___x_9582_);
                v_i_9546_ = v___x_9583_;
                v_b_9547_ = v___x_9581_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_9590_ == 0 {
                    v___x_9592_ = v___x_9589_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9593_, 0, v_a_9587_);
                    v___x_9592_ = v_reuseFailAlloc_9593_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(
    mut v_init_9597_: *mut LeanObject,
    mut v_as_9598_: *mut LeanObject,
    mut v_sz_9599_: *mut LeanObject,
    mut v_i_9600_: *mut LeanObject,
    mut v_b_9601_: *mut LeanObject,
    mut v___y_9602_: *mut LeanObject,
    mut v___y_9603_: *mut LeanObject,
    mut v___y_9604_: *mut LeanObject,
    mut v___y_9605_: *mut LeanObject,
    mut v___y_9606_: *mut LeanObject,
    mut v___y_9607_: *mut LeanObject,
    mut v___y_9608_: *mut LeanObject,
    mut v___y_9609_: *mut LeanObject,
    mut v___y_9610_: *mut LeanObject,
    mut v___y_9611_: *mut LeanObject,
    mut v___y_9612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9613_: usize = 0;
    let mut v_i_boxed_9614_: usize = 0;
    let mut v_res_9615_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9613_ = lean_unbox_usize(v_sz_9599_);
    lean_dec(v_sz_9599_);
    v_i_boxed_9614_ = lean_unbox_usize(v_i_9600_);
    lean_dec(v_i_9600_);
    v_res_9615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_9597_, v_as_9598_, v_sz_boxed_9613_, v_i_boxed_9614_, v_b_9601_, v___y_9602_, v___y_9603_, v___y_9604_, v___y_9605_, v___y_9606_, v___y_9607_, v___y_9608_, v___y_9609_, v___y_9610_, v___y_9611_);
    lean_dec(v___y_9611_);
    lean_dec_ref(v___y_9610_);
    lean_dec(v___y_9609_);
    lean_dec_ref(v___y_9608_);
    lean_dec(v___y_9607_);
    lean_dec_ref(v___y_9606_);
    lean_dec(v___y_9605_);
    lean_dec_ref(v___y_9604_);
    lean_dec(v___y_9603_);
    lean_dec(v___y_9602_);
    lean_dec_ref(v_as_9598_);
    lean_dec(v_init_9597_);
    return v_res_9615_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3___boxed(
    mut v_init_9616_: *mut LeanObject,
    mut v_n_9617_: *mut LeanObject,
    mut v_b_9618_: *mut LeanObject,
    mut v___y_9619_: *mut LeanObject,
    mut v___y_9620_: *mut LeanObject,
    mut v___y_9621_: *mut LeanObject,
    mut v___y_9622_: *mut LeanObject,
    mut v___y_9623_: *mut LeanObject,
    mut v___y_9624_: *mut LeanObject,
    mut v___y_9625_: *mut LeanObject,
    mut v___y_9626_: *mut LeanObject,
    mut v___y_9627_: *mut LeanObject,
    mut v___y_9628_: *mut LeanObject,
    mut v___y_9629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9630_: *mut LeanObject = core::ptr::null_mut();
    v_res_9630_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_9616_, v_n_9617_, v_b_9618_, v___y_9619_, v___y_9620_, v___y_9621_, v___y_9622_, v___y_9623_, v___y_9624_, v___y_9625_, v___y_9626_, v___y_9627_, v___y_9628_);
    lean_dec(v___y_9628_);
    lean_dec_ref(v___y_9627_);
    lean_dec(v___y_9626_);
    lean_dec_ref(v___y_9625_);
    lean_dec(v___y_9624_);
    lean_dec_ref(v___y_9623_);
    lean_dec(v___y_9622_);
    lean_dec_ref(v___y_9621_);
    lean_dec(v___y_9620_);
    lean_dec(v___y_9619_);
    lean_dec_ref(v_n_9617_);
    lean_dec(v_init_9616_);
    return v_res_9630_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(
    mut v_as_9631_: *mut LeanObject,
    mut v_sz_9632_: usize,
    mut v_i_9633_: usize,
    mut v_b_9634_: *mut LeanObject,
    mut v___y_9635_: *mut LeanObject,
    mut v___y_9636_: *mut LeanObject,
    mut v___y_9637_: *mut LeanObject,
    mut v___y_9638_: *mut LeanObject,
    mut v___y_9639_: *mut LeanObject,
    mut v___y_9640_: *mut LeanObject,
    mut v___y_9641_: *mut LeanObject,
    mut v___y_9642_: *mut LeanObject,
    mut v___y_9643_: *mut LeanObject,
    mut v___y_9644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9646_: u8 = 0;
    let mut v___x_9647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9651_: u8 = 0;
    let mut v_a_9652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9660_: usize = 0;
    let mut v___x_9661_: usize = 0;
    let mut v_reuseFailAlloc_9663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9667_: u8 = 0;
    let mut v___x_9669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9671_: u8 = 0;
    let mut v_isSharedCheck_9672_: u8 = 0;
    let mut v_unused_9673_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9646_ = lean_usize_dec_lt(v_i_9633_, v_sz_9632_);
                if v___x_9646_ == 0 {
                    v___x_9647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9647_, 0, v_b_9634_);
                    return v___x_9647_;
                } else {
                    v_snd_9648_ = lean_ctor_get(v_b_9634_, 1);
                    v_isSharedCheck_9672_ = (!lean_is_exclusive(v_b_9634_)) as u8;
                    if v_isSharedCheck_9672_ == 0 {
                        v_unused_9673_ = lean_ctor_get(v_b_9634_, 0);
                        lean_dec(v_unused_9673_);
                        v___x_9650_ = v_b_9634_;
                        v_isShared_9651_ = v_isSharedCheck_9672_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_9648_);
                        lean_dec(v_b_9634_);
                        v___x_9650_ = lean_box(0);
                        v_isShared_9651_ = v_isSharedCheck_9672_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_9652_ = lean_array_uget_borrowed(v_as_9631_, v_i_9633_);
                v___x_9653_ = lean_box(0);
                v___x_9654_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_9648_, v_a_9652_, v___x_9653_, v___y_9635_, v___y_9636_, v___y_9637_, v___y_9638_, v___y_9639_, v___y_9640_, v___y_9641_, v___y_9642_, v___y_9643_, v___y_9644_);
                if lean_obj_tag(v___x_9654_) == 0 {
                    lean_dec_ref_known(v___x_9654_, 1);
                    v___x_9655_ = lean_box(0);
                    v___x_9656_ = lean_unsigned_to_nat(1);
                    v___x_9657_ = lean_nat_add(v_snd_9648_, v___x_9656_);
                    lean_dec(v_snd_9648_);
                    if v_isShared_9651_ == 0 {
                        lean_ctor_set(v___x_9650_, 1, v___x_9657_);
                        lean_ctor_set(v___x_9650_, 0, v___x_9655_);
                        v___x_9659_ = v___x_9650_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9663_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9663_, 0, v___x_9655_);
                        lean_ctor_set(v_reuseFailAlloc_9663_, 1, v___x_9657_);
                        v___x_9659_ = v_reuseFailAlloc_9663_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9650_);
                    lean_dec(v_snd_9648_);
                    v_a_9664_ = lean_ctor_get(v___x_9654_, 0);
                    v_isSharedCheck_9671_ = (!lean_is_exclusive(v___x_9654_)) as u8;
                    if v_isSharedCheck_9671_ == 0 {
                        v___x_9666_ = v___x_9654_;
                        v_isShared_9667_ = v_isSharedCheck_9671_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9664_);
                        lean_dec(v___x_9654_);
                        v___x_9666_ = lean_box(0);
                        v_isShared_9667_ = v_isSharedCheck_9671_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9660_ = 1usize;
                v___x_9661_ = lean_usize_add(v_i_9633_, v___x_9660_);
                v_i_9633_ = v___x_9661_;
                v_b_9634_ = v___x_9659_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_9667_ == 0 {
                    v___x_9669_ = v___x_9666_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9670_, 0, v_a_9664_);
                    v___x_9669_ = v_reuseFailAlloc_9670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(
    mut v_as_9674_: *mut LeanObject,
    mut v_sz_9675_: *mut LeanObject,
    mut v_i_9676_: *mut LeanObject,
    mut v_b_9677_: *mut LeanObject,
    mut v___y_9678_: *mut LeanObject,
    mut v___y_9679_: *mut LeanObject,
    mut v___y_9680_: *mut LeanObject,
    mut v___y_9681_: *mut LeanObject,
    mut v___y_9682_: *mut LeanObject,
    mut v___y_9683_: *mut LeanObject,
    mut v___y_9684_: *mut LeanObject,
    mut v___y_9685_: *mut LeanObject,
    mut v___y_9686_: *mut LeanObject,
    mut v___y_9687_: *mut LeanObject,
    mut v___y_9688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9689_: usize = 0;
    let mut v_i_boxed_9690_: usize = 0;
    let mut v_res_9691_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9689_ = lean_unbox_usize(v_sz_9675_);
    lean_dec(v_sz_9675_);
    v_i_boxed_9690_ = lean_unbox_usize(v_i_9676_);
    lean_dec(v_i_9676_);
    v_res_9691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_9674_, v_sz_boxed_9689_, v_i_boxed_9690_, v_b_9677_, v___y_9678_, v___y_9679_, v___y_9680_, v___y_9681_, v___y_9682_, v___y_9683_, v___y_9684_, v___y_9685_, v___y_9686_, v___y_9687_);
    lean_dec(v___y_9687_);
    lean_dec_ref(v___y_9686_);
    lean_dec(v___y_9685_);
    lean_dec_ref(v___y_9684_);
    lean_dec(v___y_9683_);
    lean_dec_ref(v___y_9682_);
    lean_dec(v___y_9681_);
    lean_dec_ref(v___y_9680_);
    lean_dec(v___y_9679_);
    lean_dec(v___y_9678_);
    lean_dec_ref(v_as_9674_);
    return v_res_9691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(
    mut v_as_9692_: *mut LeanObject,
    mut v_sz_9693_: usize,
    mut v_i_9694_: usize,
    mut v_b_9695_: *mut LeanObject,
    mut v___y_9696_: *mut LeanObject,
    mut v___y_9697_: *mut LeanObject,
    mut v___y_9698_: *mut LeanObject,
    mut v___y_9699_: *mut LeanObject,
    mut v___y_9700_: *mut LeanObject,
    mut v___y_9701_: *mut LeanObject,
    mut v___y_9702_: *mut LeanObject,
    mut v___y_9703_: *mut LeanObject,
    mut v___y_9704_: *mut LeanObject,
    mut v___y_9705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9707_: u8 = 0;
    let mut v___x_9708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9712_: u8 = 0;
    let mut v_a_9713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9721_: usize = 0;
    let mut v___x_9722_: usize = 0;
    let mut v___x_9723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9728_: u8 = 0;
    let mut v___x_9730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9732_: u8 = 0;
    let mut v_isSharedCheck_9733_: u8 = 0;
    let mut v_unused_9734_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9707_ = lean_usize_dec_lt(v_i_9694_, v_sz_9693_);
                if v___x_9707_ == 0 {
                    v___x_9708_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9708_, 0, v_b_9695_);
                    return v___x_9708_;
                } else {
                    v_snd_9709_ = lean_ctor_get(v_b_9695_, 1);
                    v_isSharedCheck_9733_ = (!lean_is_exclusive(v_b_9695_)) as u8;
                    if v_isSharedCheck_9733_ == 0 {
                        v_unused_9734_ = lean_ctor_get(v_b_9695_, 0);
                        lean_dec(v_unused_9734_);
                        v___x_9711_ = v_b_9695_;
                        v_isShared_9712_ = v_isSharedCheck_9733_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_9709_);
                        lean_dec(v_b_9695_);
                        v___x_9711_ = lean_box(0);
                        v_isShared_9712_ = v_isSharedCheck_9733_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_9713_ = lean_array_uget_borrowed(v_as_9692_, v_i_9694_);
                v___x_9714_ = lean_box(0);
                v___x_9715_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__0(v_snd_9709_, v_a_9713_, v___x_9714_, v___y_9696_, v___y_9697_, v___y_9698_, v___y_9699_, v___y_9700_, v___y_9701_, v___y_9702_, v___y_9703_, v___y_9704_, v___y_9705_);
                if lean_obj_tag(v___x_9715_) == 0 {
                    lean_dec_ref_known(v___x_9715_, 1);
                    v___x_9716_ = lean_box(0);
                    v___x_9717_ = lean_unsigned_to_nat(1);
                    v___x_9718_ = lean_nat_add(v_snd_9709_, v___x_9717_);
                    lean_dec(v_snd_9709_);
                    if v_isShared_9712_ == 0 {
                        lean_ctor_set(v___x_9711_, 1, v___x_9718_);
                        lean_ctor_set(v___x_9711_, 0, v___x_9716_);
                        v___x_9720_ = v___x_9711_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9724_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9724_, 0, v___x_9716_);
                        lean_ctor_set(v_reuseFailAlloc_9724_, 1, v___x_9718_);
                        v___x_9720_ = v_reuseFailAlloc_9724_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9711_);
                    lean_dec(v_snd_9709_);
                    v_a_9725_ = lean_ctor_get(v___x_9715_, 0);
                    v_isSharedCheck_9732_ = (!lean_is_exclusive(v___x_9715_)) as u8;
                    if v_isSharedCheck_9732_ == 0 {
                        v___x_9727_ = v___x_9715_;
                        v_isShared_9728_ = v_isSharedCheck_9732_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9725_);
                        lean_dec(v___x_9715_);
                        v___x_9727_ = lean_box(0);
                        v_isShared_9728_ = v_isSharedCheck_9732_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9721_ = 1usize;
                v___x_9722_ = lean_usize_add(v_i_9694_, v___x_9721_);
                v___x_9723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_9692_, v_sz_9693_, v___x_9722_, v___x_9720_, v___y_9696_, v___y_9697_, v___y_9698_, v___y_9699_, v___y_9700_, v___y_9701_, v___y_9702_, v___y_9703_, v___y_9704_, v___y_9705_);
                return v___x_9723_;
            }
            3 => {
                if v_isShared_9728_ == 0 {
                    v___x_9730_ = v___x_9727_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9731_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9731_, 0, v_a_9725_);
                    v___x_9730_ = v_reuseFailAlloc_9731_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4___boxed(
    mut v_as_9735_: *mut LeanObject,
    mut v_sz_9736_: *mut LeanObject,
    mut v_i_9737_: *mut LeanObject,
    mut v_b_9738_: *mut LeanObject,
    mut v___y_9739_: *mut LeanObject,
    mut v___y_9740_: *mut LeanObject,
    mut v___y_9741_: *mut LeanObject,
    mut v___y_9742_: *mut LeanObject,
    mut v___y_9743_: *mut LeanObject,
    mut v___y_9744_: *mut LeanObject,
    mut v___y_9745_: *mut LeanObject,
    mut v___y_9746_: *mut LeanObject,
    mut v___y_9747_: *mut LeanObject,
    mut v___y_9748_: *mut LeanObject,
    mut v___y_9749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9750_: usize = 0;
    let mut v_i_boxed_9751_: usize = 0;
    let mut v_res_9752_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9750_ = lean_unbox_usize(v_sz_9736_);
    lean_dec(v_sz_9736_);
    v_i_boxed_9751_ = lean_unbox_usize(v_i_9737_);
    lean_dec(v_i_9737_);
    v_res_9752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_as_9735_, v_sz_boxed_9750_, v_i_boxed_9751_, v_b_9738_, v___y_9739_, v___y_9740_, v___y_9741_, v___y_9742_, v___y_9743_, v___y_9744_, v___y_9745_, v___y_9746_, v___y_9747_, v___y_9748_);
    lean_dec(v___y_9748_);
    lean_dec_ref(v___y_9747_);
    lean_dec(v___y_9746_);
    lean_dec_ref(v___y_9745_);
    lean_dec(v___y_9744_);
    lean_dec_ref(v___y_9743_);
    lean_dec(v___y_9742_);
    lean_dec_ref(v___y_9741_);
    lean_dec(v___y_9740_);
    lean_dec(v___y_9739_);
    lean_dec_ref(v_as_9735_);
    return v_res_9752_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(
    mut v_t_9753_: *mut LeanObject,
    mut v_init_9754_: *mut LeanObject,
    mut v___y_9755_: *mut LeanObject,
    mut v___y_9756_: *mut LeanObject,
    mut v___y_9757_: *mut LeanObject,
    mut v___y_9758_: *mut LeanObject,
    mut v___y_9759_: *mut LeanObject,
    mut v___y_9760_: *mut LeanObject,
    mut v___y_9761_: *mut LeanObject,
    mut v___y_9762_: *mut LeanObject,
    mut v___y_9763_: *mut LeanObject,
    mut v___y_9764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_9766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_9767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9772_: u8 = 0;
    let mut v_a_9773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9780_: usize = 0;
    let mut v___x_9781_: usize = 0;
    let mut v___x_9782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9786_: u8 = 0;
    let mut v_fst_9787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9796_: u8 = 0;
    let mut v_a_9797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9800_: u8 = 0;
    let mut v___x_9802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9804_: u8 = 0;
    let mut v_isSharedCheck_9805_: u8 = 0;
    let mut v_a_9806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9809_: u8 = 0;
    let mut v___x_9811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_9766_ = lean_ctor_get(v_t_9753_, 0);
                v_tail_9767_ = lean_ctor_get(v_t_9753_, 1);
                lean_inc(v_init_9754_);
                v___x_9768_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__3(v_init_9754_, v_root_9766_, v_init_9754_, v___y_9755_, v___y_9756_, v___y_9757_, v___y_9758_, v___y_9759_, v___y_9760_, v___y_9761_, v___y_9762_, v___y_9763_, v___y_9764_);
                lean_dec(v_init_9754_);
                if lean_obj_tag(v___x_9768_) == 0 {
                    v_a_9769_ = lean_ctor_get(v___x_9768_, 0);
                    v_isSharedCheck_9805_ = (!lean_is_exclusive(v___x_9768_)) as u8;
                    if v_isSharedCheck_9805_ == 0 {
                        v___x_9771_ = v___x_9768_;
                        v_isShared_9772_ = v_isSharedCheck_9805_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9769_);
                        lean_dec(v___x_9768_);
                        v___x_9771_ = lean_box(0);
                        v_isShared_9772_ = v_isSharedCheck_9805_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9806_ = lean_ctor_get(v___x_9768_, 0);
                    v_isSharedCheck_9813_ = (!lean_is_exclusive(v___x_9768_)) as u8;
                    if v_isSharedCheck_9813_ == 0 {
                        v___x_9808_ = v___x_9768_;
                        v_isShared_9809_ = v_isSharedCheck_9813_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_9806_);
                        lean_dec(v___x_9768_);
                        v___x_9808_ = lean_box(0);
                        v_isShared_9809_ = v_isSharedCheck_9813_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_9769_) == 0 {
                    v_a_9773_ = lean_ctor_get(v_a_9769_, 0);
                    lean_inc(v_a_9773_);
                    lean_dec_ref_known(v_a_9769_, 1);
                    if v_isShared_9772_ == 0 {
                        lean_ctor_set(v___x_9771_, 0, v_a_9773_);
                        v___x_9775_ = v___x_9771_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9776_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9776_, 0, v_a_9773_);
                        v___x_9775_ = v_reuseFailAlloc_9776_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9771_);
                    v_a_9777_ = lean_ctor_get(v_a_9769_, 0);
                    lean_inc(v_a_9777_);
                    lean_dec_ref_known(v_a_9769_, 1);
                    v___x_9778_ = lean_box(0);
                    v___x_9779_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9779_, 0, v___x_9778_);
                    lean_ctor_set(v___x_9779_, 1, v_a_9777_);
                    v_sz_9780_ = lean_array_size(v_tail_9767_);
                    v___x_9781_ = 0usize;
                    v___x_9782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1_spec__4(v_tail_9767_, v_sz_9780_, v___x_9781_, v___x_9779_, v___y_9755_, v___y_9756_, v___y_9757_, v___y_9758_, v___y_9759_, v___y_9760_, v___y_9761_, v___y_9762_, v___y_9763_, v___y_9764_);
                    if lean_obj_tag(v___x_9782_) == 0 {
                        v_a_9783_ = lean_ctor_get(v___x_9782_, 0);
                        v_isSharedCheck_9796_ = (!lean_is_exclusive(v___x_9782_)) as u8;
                        if v_isSharedCheck_9796_ == 0 {
                            v___x_9785_ = v___x_9782_;
                            v_isShared_9786_ = v_isSharedCheck_9796_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_9783_);
                            lean_dec(v___x_9782_);
                            v___x_9785_ = lean_box(0);
                            v_isShared_9786_ = v_isSharedCheck_9796_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_9797_ = lean_ctor_get(v___x_9782_, 0);
                        v_isSharedCheck_9804_ = (!lean_is_exclusive(v___x_9782_)) as u8;
                        if v_isSharedCheck_9804_ == 0 {
                            v___x_9799_ = v___x_9782_;
                            v_isShared_9800_ = v_isSharedCheck_9804_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_9797_);
                            lean_dec(v___x_9782_);
                            v___x_9799_ = lean_box(0);
                            v_isShared_9800_ = v_isSharedCheck_9804_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_9775_;
            }
            3 => {
                v_fst_9787_ = lean_ctor_get(v_a_9783_, 0);
                if lean_obj_tag(v_fst_9787_) == 0 {
                    v_snd_9788_ = lean_ctor_get(v_a_9783_, 1);
                    lean_inc(v_snd_9788_);
                    lean_dec(v_a_9783_);
                    if v_isShared_9786_ == 0 {
                        lean_ctor_set(v___x_9785_, 0, v_snd_9788_);
                        v___x_9790_ = v___x_9785_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_9791_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9791_, 0, v_snd_9788_);
                        v___x_9790_ = v_reuseFailAlloc_9791_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_9787_);
                    lean_dec(v_a_9783_);
                    v_val_9792_ = lean_ctor_get(v_fst_9787_, 0);
                    lean_inc(v_val_9792_);
                    lean_dec_ref_known(v_fst_9787_, 1);
                    if v_isShared_9786_ == 0 {
                        lean_ctor_set(v___x_9785_, 0, v_val_9792_);
                        v___x_9794_ = v___x_9785_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_9795_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9795_, 0, v_val_9792_);
                        v___x_9794_ = v_reuseFailAlloc_9795_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_9790_;
            }
            5 => {
                return v___x_9794_;
            }
            6 => {
                if v_isShared_9800_ == 0 {
                    v___x_9802_ = v___x_9799_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9803_, 0, v_a_9797_);
                    v___x_9802_ = v_reuseFailAlloc_9803_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9802_;
            }
            8 => {
                if v_isShared_9809_ == 0 {
                    v___x_9811_ = v___x_9808_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_9812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9812_, 0, v_a_9806_);
                    v___x_9811_ = v_reuseFailAlloc_9812_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_9811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1___boxed(
    mut v_t_9814_: *mut LeanObject,
    mut v_init_9815_: *mut LeanObject,
    mut v___y_9816_: *mut LeanObject,
    mut v___y_9817_: *mut LeanObject,
    mut v___y_9818_: *mut LeanObject,
    mut v___y_9819_: *mut LeanObject,
    mut v___y_9820_: *mut LeanObject,
    mut v___y_9821_: *mut LeanObject,
    mut v___y_9822_: *mut LeanObject,
    mut v___y_9823_: *mut LeanObject,
    mut v___y_9824_: *mut LeanObject,
    mut v___y_9825_: *mut LeanObject,
    mut v___y_9826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9827_: *mut LeanObject = core::ptr::null_mut();
    v_res_9827_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(
            v_t_9814_,
            v_init_9815_,
            v___y_9816_,
            v___y_9817_,
            v___y_9818_,
            v___y_9819_,
            v___y_9820_,
            v___y_9821_,
            v___y_9822_,
            v___y_9823_,
            v___y_9824_,
            v___y_9825_,
        );
    lean_dec(v___y_9825_);
    lean_dec_ref(v___y_9824_);
    lean_dec(v___y_9823_);
    lean_dec_ref(v___y_9822_);
    lean_dec(v___y_9821_);
    lean_dec_ref(v___y_9820_);
    lean_dec(v___y_9819_);
    lean_dec_ref(v___y_9818_);
    lean_dec(v___y_9817_);
    lean_dec(v___y_9816_);
    lean_dec_ref(v_t_9814_);
    return v_res_9827_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2() -> *mut LeanObject
{
    let mut v___x_9830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9835_: *mut LeanObject = core::ptr::null_mut();
    v___x_9830_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__1;
    v___x_9831_ = lean_unsigned_to_nat(2);
    v___x_9832_ = lean_unsigned_to_nat(103);
    v___x_9833_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__0;
    v___x_9834_ = l_Int_Linear_Poly_checkNoElimVars___closed__0;
    v___x_9835_ = l_mkPanicMessageWithDecl(
        v___x_9834_,
        v___x_9833_,
        v___x_9832_,
        v___x_9831_,
        v___x_9830_,
    );
    return v___x_9835_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(
    mut v_a_9836_: *mut LeanObject,
    mut v_a_9837_: *mut LeanObject,
    mut v_a_9838_: *mut LeanObject,
    mut v_a_9839_: *mut LeanObject,
    mut v_a_9840_: *mut LeanObject,
    mut v_a_9841_: *mut LeanObject,
    mut v_a_9842_: *mut LeanObject,
    mut v_a_9843_: *mut LeanObject,
    mut v_a_9844_: *mut LeanObject,
    mut v_a_9845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_9849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_9850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_9851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_9852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9853_: u8 = 0;
    let mut v___x_9854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9860_: u8 = 0;
    let mut v___x_9861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9865_: u8 = 0;
    let mut v_unused_9866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9870_: u8 = 0;
    let mut v___x_9872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9874_: u8 = 0;
    let mut v_a_9875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9878_: u8 = 0;
    let mut v___x_9880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9847_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_9836_, v_a_9844_);
                if lean_obj_tag(v___x_9847_) == 0 {
                    v_a_9848_ = lean_ctor_get(v___x_9847_, 0);
                    lean_inc(v_a_9848_);
                    lean_dec_ref_known(v___x_9847_, 1);
                    v_vars_9849_ = lean_ctor_get(v_a_9848_, 0);
                    lean_inc_ref(v_vars_9849_);
                    v_diseqs_9850_ = lean_ctor_get(v_a_9848_, 9);
                    lean_inc_ref(v_diseqs_9850_);
                    lean_dec(v_a_9848_);
                    v_size_9851_ = lean_ctor_get(v_vars_9849_, 2);
                    lean_inc(v_size_9851_);
                    lean_dec_ref(v_vars_9849_);
                    v_size_9852_ = lean_ctor_get(v_diseqs_9850_, 2);
                    v___x_9853_ = lean_nat_dec_eq(v_size_9851_, v_size_9852_);
                    lean_dec(v_size_9851_);
                    if v___x_9853_ == 0 {
                        lean_dec_ref(v_diseqs_9850_);
                        v___x_9854_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___closed__2,
                        );
                        v___x_9855_ = l_panic___at___00Int_Linear_Poly_checkNoElimVars_spec__0(
                            v___x_9854_,
                            v_a_9836_,
                            v_a_9837_,
                            v_a_9838_,
                            v_a_9839_,
                            v_a_9840_,
                            v_a_9841_,
                            v_a_9842_,
                            v_a_9843_,
                            v_a_9844_,
                            v_a_9845_,
                        );
                        return v___x_9855_;
                    } else {
                        v___x_9856_ = lean_unsigned_to_nat(0);
                        v___x_9857_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs_spec__1(v_diseqs_9850_, v___x_9856_, v_a_9836_, v_a_9837_, v_a_9838_, v_a_9839_, v_a_9840_, v_a_9841_, v_a_9842_, v_a_9843_, v_a_9844_, v_a_9845_);
                        lean_dec_ref(v_diseqs_9850_);
                        if lean_obj_tag(v___x_9857_) == 0 {
                            v_isSharedCheck_9865_ = (!lean_is_exclusive(v___x_9857_)) as u8;
                            if v_isSharedCheck_9865_ == 0 {
                                v_unused_9866_ = lean_ctor_get(v___x_9857_, 0);
                                lean_dec(v_unused_9866_);
                                v___x_9859_ = v___x_9857_;
                                v_isShared_9860_ = v_isSharedCheck_9865_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_9857_);
                                v___x_9859_ = lean_box(0);
                                v_isShared_9860_ = v_isSharedCheck_9865_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_9867_ = lean_ctor_get(v___x_9857_, 0);
                            v_isSharedCheck_9874_ = (!lean_is_exclusive(v___x_9857_)) as u8;
                            if v_isSharedCheck_9874_ == 0 {
                                v___x_9869_ = v___x_9857_;
                                v_isShared_9870_ = v_isSharedCheck_9874_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_9867_);
                                lean_dec(v___x_9857_);
                                v___x_9869_ = lean_box(0);
                                v_isShared_9870_ = v_isSharedCheck_9874_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_9875_ = lean_ctor_get(v___x_9847_, 0);
                    v_isSharedCheck_9882_ = (!lean_is_exclusive(v___x_9847_)) as u8;
                    if v_isSharedCheck_9882_ == 0 {
                        v___x_9877_ = v___x_9847_;
                        v_isShared_9878_ = v_isSharedCheck_9882_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_9875_);
                        lean_dec(v___x_9847_);
                        v___x_9877_ = lean_box(0);
                        v_isShared_9878_ = v_isSharedCheck_9882_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9861_ = lean_box(0);
                if v_isShared_9860_ == 0 {
                    lean_ctor_set(v___x_9859_, 0, v___x_9861_);
                    v___x_9863_ = v___x_9859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9864_, 0, v___x_9861_);
                    v___x_9863_ = v_reuseFailAlloc_9864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9863_;
            }
            3 => {
                if v_isShared_9870_ == 0 {
                    v___x_9872_ = v___x_9869_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9873_, 0, v_a_9867_);
                    v___x_9872_ = v_reuseFailAlloc_9873_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9872_;
            }
            5 => {
                if v_isShared_9878_ == 0 {
                    v___x_9880_ = v___x_9877_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9881_, 0, v_a_9875_);
                    v___x_9880_ = v_reuseFailAlloc_9881_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs___boxed(
    mut v_a_9883_: *mut LeanObject,
    mut v_a_9884_: *mut LeanObject,
    mut v_a_9885_: *mut LeanObject,
    mut v_a_9886_: *mut LeanObject,
    mut v_a_9887_: *mut LeanObject,
    mut v_a_9888_: *mut LeanObject,
    mut v_a_9889_: *mut LeanObject,
    mut v_a_9890_: *mut LeanObject,
    mut v_a_9891_: *mut LeanObject,
    mut v_a_9892_: *mut LeanObject,
    mut v_a_9893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9894_: *mut LeanObject = core::ptr::null_mut();
    v_res_9894_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(
        v_a_9883_, v_a_9884_, v_a_9885_, v_a_9886_, v_a_9887_, v_a_9888_, v_a_9889_, v_a_9890_,
        v_a_9891_, v_a_9892_,
    );
    lean_dec(v_a_9892_);
    lean_dec_ref(v_a_9891_);
    lean_dec(v_a_9890_);
    lean_dec_ref(v_a_9889_);
    lean_dec(v_a_9888_);
    lean_dec_ref(v_a_9887_);
    lean_dec(v_a_9886_);
    lean_dec_ref(v_a_9885_);
    lean_dec(v_a_9884_);
    lean_dec(v_a_9883_);
    return v_res_9894_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(
    mut v_a_9895_: *mut LeanObject,
    mut v_a_9896_: *mut LeanObject,
    mut v_a_9897_: *mut LeanObject,
    mut v_a_9898_: *mut LeanObject,
    mut v_a_9899_: *mut LeanObject,
    mut v_a_9900_: *mut LeanObject,
    mut v_a_9901_: *mut LeanObject,
    mut v_a_9902_: *mut LeanObject,
    mut v_a_9903_: *mut LeanObject,
    mut v_a_9904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9906_: *mut LeanObject = core::ptr::null_mut();
    v___x_9906_ = l_Lean_Meta_Grind_Arith_Cutsat_checkVars(
        v_a_9895_, v_a_9896_, v_a_9897_, v_a_9898_, v_a_9899_, v_a_9900_, v_a_9901_, v_a_9902_,
        v_a_9903_, v_a_9904_,
    );
    if lean_obj_tag(v___x_9906_) == 0 {
        let mut v___x_9907_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_9906_, 1);
        v___x_9907_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDvds(
            v_a_9895_, v_a_9896_, v_a_9897_, v_a_9898_, v_a_9899_, v_a_9900_, v_a_9901_, v_a_9902_,
            v_a_9903_, v_a_9904_,
        );
        if lean_obj_tag(v___x_9907_) == 0 {
            let mut v___x_9908_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_9907_, 1);
            v___x_9908_ = l_Lean_Meta_Grind_Arith_Cutsat_checkLowers(
                v_a_9895_, v_a_9896_, v_a_9897_, v_a_9898_, v_a_9899_, v_a_9900_, v_a_9901_,
                v_a_9902_, v_a_9903_, v_a_9904_,
            );
            if lean_obj_tag(v___x_9908_) == 0 {
                let mut v___x_9909_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_9908_, 1);
                v___x_9909_ = l_Lean_Meta_Grind_Arith_Cutsat_checkUppers(
                    v_a_9895_, v_a_9896_, v_a_9897_, v_a_9898_, v_a_9899_, v_a_9900_, v_a_9901_,
                    v_a_9902_, v_a_9903_, v_a_9904_,
                );
                if lean_obj_tag(v___x_9909_) == 0 {
                    let mut v___x_9910_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_9909_, 1);
                    v___x_9910_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimEqs(
                        v_a_9895_, v_a_9896_, v_a_9897_, v_a_9898_, v_a_9899_, v_a_9900_,
                        v_a_9901_, v_a_9902_, v_a_9903_, v_a_9904_,
                    );
                    if lean_obj_tag(v___x_9910_) == 0 {
                        let mut v___x_9911_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_9910_, 1);
                        v___x_9911_ = l_Lean_Meta_Grind_Arith_Cutsat_checkElimStack(
                            v_a_9895_, v_a_9896_, v_a_9897_, v_a_9898_, v_a_9899_, v_a_9900_,
                            v_a_9901_, v_a_9902_, v_a_9903_, v_a_9904_,
                        );
                        if lean_obj_tag(v___x_9911_) == 0 {
                            let mut v___x_9912_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v___x_9911_, 1);
                            v___x_9912_ = l_Lean_Meta_Grind_Arith_Cutsat_checkDiseqCnstrs(
                                v_a_9895_, v_a_9896_, v_a_9897_, v_a_9898_, v_a_9899_, v_a_9900_,
                                v_a_9901_, v_a_9902_, v_a_9903_, v_a_9904_,
                            );
                            return v___x_9912_;
                        } else {
                            return v___x_9911_;
                        }
                    } else {
                        return v___x_9910_;
                    }
                } else {
                    return v___x_9909_;
                }
            } else {
                return v___x_9908_;
            }
        } else {
            return v___x_9907_;
        }
    } else {
        return v___x_9906_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(
    mut v_a_9913_: *mut LeanObject,
    mut v_a_9914_: *mut LeanObject,
    mut v_a_9915_: *mut LeanObject,
    mut v_a_9916_: *mut LeanObject,
    mut v_a_9917_: *mut LeanObject,
    mut v_a_9918_: *mut LeanObject,
    mut v_a_9919_: *mut LeanObject,
    mut v_a_9920_: *mut LeanObject,
    mut v_a_9921_: *mut LeanObject,
    mut v_a_9922_: *mut LeanObject,
    mut v_a_9923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9924_: *mut LeanObject = core::ptr::null_mut();
    v_res_9924_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(
        v_a_9913_, v_a_9914_, v_a_9915_, v_a_9916_, v_a_9917_, v_a_9918_, v_a_9919_, v_a_9920_,
        v_a_9921_, v_a_9922_,
    );
    lean_dec(v_a_9922_);
    lean_dec_ref(v_a_9921_);
    lean_dec(v_a_9920_);
    lean_dec_ref(v_a_9919_);
    lean_dec(v_a_9918_);
    lean_dec_ref(v_a_9917_);
    lean_dec(v_a_9916_);
    lean_dec_ref(v_a_9915_);
    lean_dec(v_a_9914_);
    lean_dec(v_a_9913_);
    return v_res_9924_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
}
